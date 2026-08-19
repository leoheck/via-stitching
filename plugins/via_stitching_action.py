# Via Stitching - KiCad 10 IPC action plugin
#
# Fills the overlap of a net's copper zones (e.g. the top + bottom GND pours)
# with a grid of through vias, so the two ground planes are stitched together.
#
# Uses the modern IPC API (kicad-python / kipy), so it keeps working on KiCad 11+
# where the legacy SWIG pcbnew bindings are removed.
#
# Original via-stitching idea: JS Reynaud. This is an independent IPC re-implementation.
# License: GPL-3.0-or-later

import json
import math
import os
import re
import sys
import traceback
from collections import defaultdict
from pathlib import Path

import wx
import wx.adv

from kipy import KiCad
from kipy.errors import ApiError, ConnectionError as KiCadConnectionError
from kipy.proto.common import ApiStatusCode
from kipy.proto.common.types import KiCadObjectType
from kipy.proto.board.board_types_pb2 import BoardLayer as BL, ViaType
from kipy.board_types import Group, Via, ArcTrack, PadType, PSS_CIRCLE
from kipy.geometry import Vector2
from kipy.util.units import from_mm, to_mm
from kipy.util.board_layer import iter_copper_layers

# Make the sibling helper modules importable regardless of how KiCad launches us.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from _mac_dialog import attach_to_stage_manager, prepare_app  # noqa: E402
from _win_dialog import make_tool_window  # noqa: E402

VERSION = "2.0.0"

# shapely (plus the numpy and GEOS it drags in) costs the better part of a second
# to import, more than the rest of start-up together, so the geometry functions
# import it lazily and the dialog is on screen before any of it is paid.

# kipy defaults to 2 s, which get_zones() or a few hundred vias blow through on a
# real board. Every miss surfaces as a lost connection mid-edit.
API_TIMEOUT_MS = 30000


# --- Dialog defaults --------------------------------------------------------
DEFAULT_VIA_DIAMETER_MM = 0.6
DEFAULT_DRILL_MM = 0.3
DEFAULT_SPACING_MM = 2.0
DEFAULT_NET = "GND"
PATTERNS = ["Hexagonal", "Square", "Staggered"]
DEFAULT_PATTERN = "Square"
# Off by default: a via through another net's zone is not a DRC error. KiCad pulls
# the fill back around it on the refill this plugin already triggers. And on the
# common 4-layer stackup an inner power plane covers most of the board, so on by
# default would place no vias at all where it otherwise places a full grid.
# Tracks are the opposite case, so that keepout is unconditional.
DEFAULT_AVOID_OTHER_ZONES = False
# Off by default: thermal-via arrays under a QFN/BGA ground pad are a common,
# intentional use of via stitching, so this must not block them by default.
DEFAULT_AVOID_FOOTPRINTS = False


# Safety margins applied silently (the dialog has no clearance field, by design).
# The inset keeps a via at least (via_radius + EDGE_EPS) inside the fill on every
# layer the net is poured on, where KiCad has already pulled the fill back by the
# board clearance. It says nothing about layers the net is *not* poured on: a
# through via's drill crosses those too, which is what the track and zone keepouts
# below are for. EDGE_EPS just absorbs polygon rounding.
EDGE_EPS_MM = 0.05
# Hole-to-hole margin kept between a new via drill and existing via/pad drills.
HOLE_MARGIN_MM = 0.25
# Copper-to-copper clearance used when KiCad's netclass carries no value of its
# own, which is what a netclass inheriting the board minimum reports over IPC.
FALLBACK_CLEARANCE_MM = 0.2

# Warn before placing more than this many vias (keeps KiCad responsive).
VIA_COUNT_WARN = 5000

# Environment lines for error reports. Filled in once we know the KiCad version.
_ENV = []

def _kipy_version():
    try:
        from importlib.metadata import version

        return version("kicad-python")
    except Exception:
        return "unknown"


def _kicad_config_dirs():
    """KiCad's per-version config directories, newest version first.

    KiCad keeps per-version settings (kicad_common.json, pcbnew.json,
    colors/) under one directory per platform. Shared by
    _api_enabled_in_config and _layer_colors so there's exactly one place
    that knows where KiCad's config lives on each OS, instead of each caller
    hardcoding its own (previously Linux-only) guess.
    """
    root = os.environ.get("KICAD_CONFIG_HOME")
    if not root:
        if sys.platform == "win32":
            root = os.path.join(os.environ.get("APPDATA", ""), "kicad")
        elif sys.platform == "darwin":
            root = os.path.expanduser("~/Library/Preferences/kicad")
        else:
            root = os.path.join(
                os.environ.get("XDG_CONFIG_HOME") or os.path.expanduser("~/.config"),
                "kicad",
            )
    try:
        # Version subdirectories, newest first, so KiCad 11 wins over 10.
        versions = sorted(
            (d for d in os.listdir(root) if os.path.isdir(os.path.join(root, d))),
            key=lambda d: [int(p) for p in d.split(".") if p.isdigit()] or [0],
            reverse=True,
        )
    except Exception:
        return []
    return [os.path.join(root, name) for name in versions]


# KiCad default theme copper colors (fallback)
_DEFAULT_COPPER = {
    "f": (200, 52, 52), "in1": (127, 200, 127), "in2": (206, 125, 66),
    "in3": (79, 203, 203), "in4": (219, 98, 139), "in5": (167, 165, 198),
    "in6": (40, 204, 217), "b": (77, 127, 196),
}

def _copper_key_to_layer(key):
    if key == "f":
        return BL.BL_F_Cu
    if key == "b":
        return BL.BL_B_Cu
    m = re.match(r"in(\d+)$", key)
    return getattr(BL, f"BL_In{m.group(1)}_Cu", None) if m else None

def _layer_colors():
    """{BoardLayer: (r, g, b)} from the active KiCad color theme, with fallbacks."""
    copper = dict(_DEFAULT_COPPER)
    try:
        for config_dir in _kicad_config_dirs():
            pcbnew_json = Path(config_dir) / "pcbnew.json"
            if not pcbnew_json.exists():
                continue
            theme = json.loads(pcbnew_json.read_text())["appearance"]["color_theme"]
            data = json.loads((Path(config_dir) / "colors" / f"{theme}.json").read_text())
            for key, val in data.get("board", {}).get("copper", {}).items():
                m = re.match(r"rgba?\(\s*(\d+)\s*,\s*(\d+)\s*,\s*(\d+)", val)
                if m:
                    copper[key.lower()] = tuple(map(int, m.groups()))
            break  # newest version dir with a pcbnew.json wins
    except Exception:
        pass  # built-in theme or unreadable config: defaults stand
    out = {}
    for key, rgb in copper.items():
        layer = _copper_key_to_layer(key)
        if layer is not None:
            out[layer] = rgb
    return out

def _color_swatch(rgb, size=14):
    bmp = wx.Bitmap(size, size)
    dc = wx.MemoryDC(bmp)
    dc.SetBackground(wx.Brush(wx.Colour(*rgb)))
    dc.Clear()
    dc.SetPen(wx.Pen(wx.Colour(90, 90, 90)))
    dc.SetBrush(wx.TRANSPARENT_BRUSH)
    dc.DrawRectangle(0, 0, size, size)
    dc.SelectObject(wx.NullBitmap)
    return bmp

def _polyline_coords(polyline):
    """Convert a kipy PolyLine into a list of (x, y) nm tuples for shapely.

    Zone fill outlines are polygonal; arc nodes (rare in fills) are approximated
    by their start/mid/end points.
    """
    coords = []
    for node in polyline.nodes:
        if node.has_point:
            p = node.point
            coords.append((p.x, p.y))
        elif node.has_arc:
            arc = node.arc
            for pt in (arc.start, arc.mid, arc.end):
                coords.append((pt.x, pt.y))
    return coords


def _polygon_with_holes_to_shapely(pwh):
    """Build a shapely Polygon (with holes) from a kipy PolygonWithHoles."""
    from shapely.geometry import Polygon

    shell = _polyline_coords(pwh.outline)
    if len(shell) < 3:
        return None
    holes = []
    for hole in pwh.holes:
        ring = _polyline_coords(hole)
        if len(ring) >= 3:
            holes.append(ring)
    poly = Polygon(shell, holes)
    if not poly.is_valid:
        poly = poly.buffer(0)
    return poly if (not poly.is_empty) else None


def _span_layers(board, start_layer, end_layer):
    """All enabled copper layers between start and end, inclusive, in stackup order."""
    enabled = set(board.get_enabled_layers())
    order = [l for l in iter_copper_layers() if l in enabled]
    i, j = order.index(start_layer), order.index(end_layer)
    if i > j:
        i, j = j, i          # user may have picked them "upside down"
    return order[i:j + 1]


def _layer_region(zones, net_name):
    """Return {layer: shapely geometry} of the filled copper of `net_name`."""
    from shapely.ops import unary_union

    per_layer = {}
    for zone in zones:
        if zone.is_rule_area():
            continue
        net = zone.net
        if net is None or net.name != net_name:
            continue
        for layer, shapes in zone.filled_polygons.items():
            for pwh in shapes:
                poly = _polygon_with_holes_to_shapely(pwh)
                if poly is not None and not poly.is_empty:
                    if not poly.is_valid:
                        poly = poly.buffer(0)   # repair rare self-intersections
                    per_layer.setdefault(layer, []).append(poly)
    return {layer: unary_union(polys) for layer, polys in per_layer.items()}


def _fallback_clearances():
    """Clearance lookup that answers FALLBACK_CLEARANCE_MM for every net."""
    return defaultdict(lambda: from_mm(FALLBACK_CLEARANCE_MM))


def _net_clearances(board, nets, net_name):
    """Clearance in nm to hold between a via on `net_name` and each other net.

    KiCad resolves the clearance between two items to the larger of their two
    netclass values, so that maximum is what gets pre-computed per net here. A
    netclass that simply inherits the board minimum reports no value of its own
    over IPC, and those fall back to FALLBACK_CLEARANCE_MM, as does every net if
    KiCad refuses the call outright.
    """
    clearances = _fallback_clearances()
    try:
        classes = board.get_netclass_for_nets(nets)
    except Exception:
        return clearances

    fallback = from_mm(FALLBACK_CLEARANCE_MM)
    # `is not None`, not `or`: a netclass may legitimately carry an explicit 0,
    # and only a genuinely unset value means "inherits the board minimum".
    values = {
        name: (fallback if nc.clearance is None else nc.clearance)
        for name, nc in classes.items()
    }
    own = values.get(net_name, fallback)
    clearances.update({name: max(own, value) for name, value in values.items()})
    return clearances


def _blocked_predicate(shapes):
    """Build a `blocked(x, y)` test over `shapes`, through one spatial index.

    Unioning the keepouts first is what made this slow. On a board with 8000
    track segments, the unary_union of the buffered tracks alone cost about 6 s
    of a 7.7 s total, against 0.6 s for the STRtree used here, for exactly the
    same set of blocked candidates.
    """
    if not shapes:
        return lambda x, y: False

    from shapely import STRtree
    from shapely.geometry import Point

    tree = STRtree(shapes)
    return lambda x, y: len(tree.query(Point(x, y), predicate="intersects")) > 0


def _keepout_shapes(board, via_radius_nm, span):
    """Drill keepouts around existing vias and through-hole pads.
    Prevents new stitching vias from violating hole-to-hole clearance.
    """
    from shapely.geometry import Point

    margin = from_mm(HOLE_MARGIN_MM)
    span_set = set(span)
    circles = []

    for via in board.get_vias():

        try:
            via_span = set(_span_layers(board, via.padstack.drill.start_layer, via.padstack.drill.end_layer))
        except ValueError:
            via_span = span_set  # unknown span: be conservative, treat as blocking
        if not (via_span & span_set):
            continue

        r = via_radius_nm + via.drill_diameter // 2 + margin
        circles.append(Point(via.position.x, via.position.y).buffer(r, quad_segs=8))

    for pad in board.get_pads():
        if pad.pad_type not in (PadType.PT_PTH, PadType.PT_NPTH):
            continue
        try:
            # A drill is a Vector2 because it may be a milled slot, so the long
            # axis is what a round keepout has to cover.
            drill = pad.padstack.drill.diameter
            hole_r = max(drill.x, drill.y) // 2
        except Exception:
            hole_r = 0
        if hole_r <= 0:
            continue
        r = via_radius_nm + hole_r + margin
        circles.append(Point(pad.position.x, pad.position.y).buffer(r, quad_segs=8))

    return circles


def _track_keepout_shapes(board, net_name, via_radius_nm, clearances, span):
    """Clearance areas around other nets' tracks on the layers the via spans.

    The via's drill only crosses the copper layers between its start and end,
    so only tracks on those layers can collide with it. For a through via the
    span is the whole stack and this matches the old behavior.
    """
    from shapely.geometry import LineString
    span_set = set(span)
    shapes = []
    for track in board.get_tracks():
        if track.net.name == net_name:
            continue
        if track.layer not in span_set:
            continue
        if isinstance(track, ArcTrack):
            coords = [
                (track.start.x, track.start.y),
                (track.mid.x, track.mid.y),
                (track.end.x, track.end.y),
            ]
        else:
            coords = [(track.start.x, track.start.y), (track.end.x, track.end.y)]
        r = via_radius_nm + track.width // 2 + clearances[track.net.name]
        shapes.append(LineString(coords).buffer(r, quad_segs=8))

    return shapes


def _zone_keepout_shapes(zones, net_name, via_radius_nm, clearances, span):
    """Clearance areas around other nets' filled zones, on any layer.
    A through via's drill spans every copper layer, so a filled zone for a
    different net on a layer `net_name` never pours on (an inner power plane
    under a GND-poured outer layer, say) can still be worth avoiding, even
    though KiCad's refill would clear the fill back around the via by itself.
    """
    span_set = set(span)
    shapes = []
    for zone in zones:
        net = zone.net
        if net is not None and net.name == net_name:
            continue
        margin = via_radius_nm + clearances[net.name if net is not None else ""]
        for layer, filled in zone.filled_polygons.items():
            if layer not in span_set:
                continue
            for pwh in filled:
                poly = _polygon_with_holes_to_shapely(pwh)
                if poly is not None:
                    shapes.append(poly.buffer(margin, quad_segs=8))

    return shapes


def _rule_area_keepout_shapes(zones, via_radius_nm, span):
    """Outlines of rule areas that forbid vias.

    A rule area is an explicit "keep out" from whoever laid the board out, so
    this is unconditional and takes no clearance on top: the rule is that the
    via simply is not inside the area.

    Layers are ignored on purpose. A through via crosses every copper layer, so
    a via keepout on any single layer still catches it.

    kipy 0.7.1 wraps a zone's copper settings but not its RuleAreaSettings, so
    the restriction flags are read off the proto.
    """
    span_set = set(span)
    shapes = []
    for zone in zones:
        if not zone.is_rule_area():
            continue
        if not zone.proto.rule_area_settings.keepout_vias:
            continue
        if not (set(zone.layers) & span_set):
            continue
        # Zone.outline indexes polygons[0], which an empty PolySet would not have.
        if not zone.proto.outline.polygons:
            continue
        poly = _polygon_with_holes_to_shapely(zone.outline)
        if poly is not None:
            shapes.append(poly.buffer(via_radius_nm, quad_segs=8))

    return shapes


def _footprint_keepout_shapes(board, net_name, via_radius_nm, clearances, span):
    """Clearance areas around every footprint's bounding box.

    Keeps vias out from under component bodies (BGAs, connectors, anything
    with fine-pitch leads underneath). This is a mechanical fit concern, not
    a copper one, so it applies regardless of the footprint's net.
    """
    from shapely.geometry import box as shapely_box

    span_set = set(span)

    footprints = [fp for fp in board.get_footprints() if fp.layer in span_set]
    if not footprints:
        return []

    # KiCad drops any item it has no box for, so this list can come back short.
    # Silently not avoiding those is the one outcome worth saying out loud.
    boxes = board.get_item_bounding_box(footprints)
    if len(boxes) < len(footprints):
        _to_stderr(
            f"Via Stitching: KiCad returned no bounding box for "
            f"{len(footprints) - len(boxes)} of {len(footprints)} footprints. "
            "Those are not being avoided."
        )

    margin = via_radius_nm + clearances[net_name]
    return [
        shapely_box(
            bbox.pos.x - margin,
            bbox.pos.y - margin,
            bbox.pos.x + bbox.size.x + margin,
            bbox.pos.y + bbox.size.y + margin,
        )
        for bbox in boxes
    ]

def _grid_points(bounds, spacing_nm, pattern):
    """Yield candidate (x, y) nm points across `bounds` for the given pattern.

    The grid is anchored to `bounds`, so the user controls placement via the
    region itself (and the X/Y offset parameters). Positions are therefore
    not reproducible across runs if the region's bounding box changes.
    """
    minx, miny, maxx, maxy = bounds
    minx, miny = int(math.floor(minx)), int(math.floor(miny))
    maxx, maxy = int(math.ceil(maxx)), int(math.ceil(maxy))
    if pattern == "Hexagonal":
        row_pitch = round(spacing_nm * math.sqrt(3) / 2)
    else:
        row_pitch = spacing_nm
    if row_pitch <= 0 or spacing_nm <= 0:
        return
    row = 0
    y = miny
    while y <= maxy:
        if pattern in ("Hexagonal", "Staggered") and (row % 2) == 1:
            x = minx + spacing_nm // 2
        else:
            x = minx
        while x <= maxx:
            yield (x, y)
            x += spacing_nm
        y += row_pitch
        row += 1


def _make_via(x, y, via_type, start_layer, end_layer, diameter_nm, drill_nm, net):
    """Create a through Via with a valid single-layer PST_NORMAL padstack."""
    via = Via()  # defaults to VT_THROUGH with a PST_NORMAL, F_Cu-only padstack
    via.type = via_type
    via.padstack.drill.start_layer = start_layer
    via.padstack.drill.end_layer = end_layer
    via.diameter = diameter_nm
    via.drill_diameter = drill_nm
    via.padstack.copper_layers[0].shape = PSS_CIRCLE
    via.position = Vector2.from_xy(int(x), int(y))
    via.net = net
    return via


def _group_vias(board, vias, net_name, start_layer, end_layer):
    """Bundle the vias into one named group. Best effort, never raises.

    Built on create_items, not the editor's Group Items action. Driving that action
    over a large selection is what left the new vias out of the canvas view on
    KiCad 10, and nothing but reopening the board brought them back. It also split
    one run across four groups, because add_to_selection returns before the
    selection has crossed KiCad's UI thread, and its only success signal was
    get_groups(), which raises ApiError if any unrelated group on the board has a
    dangling member. create_items needs no selection and returns what it made.
    """

    if not vias:
        return False
    try:
        group = Group()
        # Group.name is read-only in kicad-python 0.7.x, the inherited proto is not.
        group.proto.name = f"ViaStitching {net_name} {start_layer}:{end_layer}"
        group.items = vias  # stores the member KIIDs, so the vias must exist already
        return bool(board.create_items(group))
    except Exception:
        return False


def stitch(
    board, via_type, start_layer, end_layer, net_name, via_dia_mm, drill_mm, spacing_mm, pattern, 
    x_offset_mm, y_offset_mm, 
    avoid_other_zones=DEFAULT_AVOID_OTHER_ZONES, avoid_footprints=DEFAULT_AVOID_FOOTPRINTS, parent=None):

    """Run the stitching. Returns (vias placed, whether they were grouped)."""
    from shapely.geometry import Point
    from shapely.prepared import prep

    diameter_nm = from_mm(via_dia_mm)
    drill_nm = from_mm(drill_mm)
    spacing_nm = from_mm(spacing_mm)
    via_radius_nm = diameter_nm // 2

    x_offset_nm = from_mm(x_offset_mm)
    y_offset_nm = from_mm(y_offset_mm)

    # Resolve the real Net object (carries the proper proto for assignment).
    nets = board.get_nets()
    net = next((n for n in nets if n.name == net_name), None)
    if net is None:
        raise RuntimeError(f"Net '{net_name}' not found on the board.")

    zones = board.get_zones()
    regions = _layer_region(zones, net_name)
    if not regions:
        raise RuntimeError(
            f"No filled copper found for net '{net_name}'.\n"
            "Fill the zones first (press B in the PCB editor), then run again."
        )

    span = _span_layers(board, start_layer, end_layer)

    # The via must land on the net's copper on the two layers it connects.
    missing = [l for l in (start_layer, end_layer) if l not in regions]
    if missing:
        names = ", ".join(board.get_layer_name(l) for l in missing)
        raise RuntimeError(
            f"Net '{net_name}' has no filled copper on: {names}.\n"
            "Pick start/end layers where the net is poured, or fill the zones "
            "first (press B in the PCB editor)."
        )

    region = regions[start_layer].intersection(regions[end_layer])

    # Intermediate layers inside the span: where this net is poured there too,
    # keep the via on that copper (the barrel connects those layers as well).
    # Layers in the span where the net is NOT poured are left to DRC: the barrel
    # passing through another net's copper there is not checked here.
    for layer in span:
        if layer in regions and layer not in (start_layer, end_layer):
            region = region.intersection(regions[layer])

    if region.is_empty:
        raise RuntimeError(
            "The selected net's planes do not overlap anywhere on the "
            "selected layer span."
        )

    # Inset so the via body + clearance ring stay inside the fill on all layers.
    inset = via_radius_nm + from_mm(EDGE_EPS_MM)
    region = region.buffer(-inset)
    if region.is_empty:
        raise RuntimeError(
            "No room for vias after clearance inset. Try a smaller via diameter."
        )

    # Grid before subtracting the keepout, so "grid too coarse" and "every position
    # is taken by an existing hole" get different messages. The grid is anchored to
    # region.bounds, so it is not reproducible run to run.
    prepared = prep(region)
    candidates = [
        (x, y)
        for (x, y) in _grid_points(region.bounds, spacing_nm, pattern)
        if prepared.contains(Point(x, y))
    ]
    if not candidates:
        raise RuntimeError(
            "No via positions fit inside the overlap of the planes.\n"
            "Try a smaller spacing or via diameter."
        )

    # Every keepout as one flat list of shapes, tested through a single spatial
    # index. Avoid existing via/pad drill holes and other nets' tracks on any
    # layer, plus whatever else the dialog asked for.
    clearances = _net_clearances(board, nets, net_name)
    keepout = _keepout_shapes(board, via_radius_nm, span)
    keepout += _rule_area_keepout_shapes(zones, via_radius_nm, span)
    keepout += _track_keepout_shapes(board, net_name, via_radius_nm, clearances, span)
    if avoid_other_zones:
        keepout += _zone_keepout_shapes(zones, net_name, via_radius_nm, clearances, span)
    if avoid_footprints:
        keepout += _footprint_keepout_shapes(board, net_name, via_radius_nm, clearances, span)

    blocked = _blocked_predicate(keepout)
    points = [
        (ox, oy)
        for (ox, oy) in ((x + x_offset_nm, y + y_offset_nm) for (x, y) in candidates)
        if prepared.contains(Point(ox, oy)) and not blocked(ox, oy)
    ]

    if not points:
        # Only name the optional keepouts that are actually switched on, so this
        # never sends someone off to untick a box that is already off.
        optional = [
            name
            for name, on in (
                ("other nets' zones", avoid_other_zones),
                ("footprints", avoid_footprints),
            )
            if on
        ]
        blockers = " or ".join(
            ["existing vias, pads, tracks or rule areas"] + optional
        )
        untick = (
            " Or untick " + " or ".join(f"'Avoid {n}'" for n in optional) + "."
            if optional
            else ""
        )
        raise RuntimeError(
            f"All {len(candidates)} candidate positions are blocked by {blockers}.\n"
            "If these zones are already stitched, delete the previous vias first, "
            "or try a smaller spacing." + untick
        )

    if len(points) > VIA_COUNT_WARN:
        msg = (
            f"This will place {len(points)} vias, which may make KiCad slow.\n"
            "Increase the spacing for fewer vias.\n\nPlace them anyway?"
        )
        style = wx.YES_NO | wx.ICON_WARNING | wx.STAY_ON_TOP
        if wx.MessageBox(msg, "Many vias", style, parent) != wx.YES:
            return 0, False

    vias = [_make_via(x, y, via_type, start_layer, end_layer, diameter_nm, drill_nm, net) for (x, y) in points]

    # No explicit commit: one create_items call is already one undo step, and an
    # open commit can be seized or rolled back by anything else touching the editor.
    created = board.create_items(vias)
    if len(created) != len(vias):
        raise RuntimeError(
            f"KiCad accepted only {len(created)} of the {len(vias)} vias.\n"
            "Check that the drill is smaller than the via diameter."
        )

    # create_items reports what it echoed back, not what the board kept.
    placed = board.get_items_by_id([v.id for v in created])
    if len(placed) != len(created):
        raise RuntimeError(
            f"{len(created)} vias were created but only {len(placed)} are on the "
            "board. Nothing was rolled back, so check the board before saving."
        )

    grouped = _group_vias(board, created, net_name, start_layer, end_layer)

    # Refilling is safe: vias placed this way survive a manual B and an API refill.
    # block=False because kipy's blocking poll loop never increments its counter, so
    # a busy KiCad would spin it forever.
    try:
        board.refill_zones(block=False)
    except Exception:
        pass

    return len(placed), grouped


class ViaStitchingDialog(wx.Dialog):
    """The 'Via Stitching Parameters' input dialog."""

    def __init__(self, parent, net_names, board):
        super().__init__(
            parent,
            title="Via Stitching Parameters",
            style=wx.DEFAULT_DIALOG_STYLE | wx.STAY_ON_TOP,
        )

        icon_path = os.path.join(
            os.path.dirname(os.path.abspath(__file__)), "icon.png"
        )
        if os.path.exists(icon_path):
            self.SetIcon(wx.Icon(icon_path, wx.BITMAP_TYPE_PNG))

        # Default tooltip auto-pop is ~5s, too short for the multi-paragraph
        # tooltips below. This is a process-global wx setting, so one call here
        # covers every tooltip in the dialog. Windows' native tooltip control
        # takes this as a signed 16-bit delay (TTM_SETDELAYTIME): anything at
        # or above 32768 wraps around and comes back *shorter* than the
        # default, which is why 60000 didn't actually help. 32000 is the
        # longest value that doesn't wrap.
        wx.ToolTip.SetAutoPop(32000)

        enabled = set(board.get_enabled_layers())
        copper_layer_ids = [l for l in iter_copper_layers() if l in enabled]
        self.layer_map   = {board.get_layer_name(l): l for l in copper_layer_ids}
        self.layer_names = {v: k for k, v in self.layer_map.items()}
        copper_layer_names = list(self.layer_map.keys())
        self._all_layer_names = copper_layer_names  # physical order, front to back
        self._layer_colors = _layer_colors()
        layer_colors = self._layer_colors

        self.VIA_TYPE_CHOICES = {
            "Through":      ViaType.VT_THROUGH,
            "Micro":        ViaType.VT_MICRO,
            "Blind/Buried": ViaType.VT_BLIND_BURIED,
            "Blind":        ViaType.VT_BLIND,
            "Buried":       ViaType.VT_BURIED,
        }

        self.VIA_TYPE_NAMES = {v: k for k, v in self.VIA_TYPE_CHOICES.items()}   # int -> name

        selected_vias = board.get_selection(KiCadObjectType.KOT_PCB_VIA)
        sample_via = None
        if selected_vias:
            sample_via = selected_vias[0]
            sample_via_start_layer = sample_via.padstack.drill.start_layer
            sample_via_end_layer = sample_via.padstack.drill.end_layer
            sample_via_net_name = sample_via.net.name

        grid = wx.FlexGridSizer(cols=2, vgap=5, hgap=5)
        grid.AddGrowableCol(1)

        def add_row(label, ctrl):
            grid.Add(wx.StaticText(self, label=label), 0, wx.ALIGN_CENTER_VERTICAL)
            grid.Add(ctrl, 1, wx.EXPAND)

        via_types = list(self.VIA_TYPE_CHOICES.keys())
        self.via_type = wx.Choice(self, choices=via_types)
        if sample_via:
            self.via_type.SetStringSelection(self.VIA_TYPE_NAMES.get(sample_via.type))
        else:
            self.via_type.SetSelection(0)
        self.via_type.Bind(wx.EVT_CHOICE, lambda evt: self._refresh_layer_controls())

        def _layer_combo():
            combo = wx.adv.BitmapComboBox(self, style=wx.CB_READONLY)
            for name in copper_layer_names:
                rgb = layer_colors.get(self.layer_map[name], (128, 128, 128))
                combo.Append(name, _color_swatch(rgb))
            return combo

        self.start_layer = _layer_combo()
        if sample_via:
            self.start_layer.SetStringSelection(self.layer_names[sample_via_start_layer])
        else:
            self.start_layer.SetSelection(0)
        self.end_layer = _layer_combo()
        if sample_via:
            self.end_layer.SetStringSelection(self.layer_names[sample_via_end_layer])
        else:
            self.end_layer.SetSelection(len(copper_layer_names) - 1)
        # Micro's end layer is derived from which outer layer the start is, so
        # changing the start has to re-derive it.
        self.start_layer.Bind(wx.EVT_COMBOBOX, lambda evt: self._refresh_layer_controls())

        if sample_via:
            via_dia_mm_str = str(to_mm(sample_via.diameter))
            viar_drill_mm_str = str(to_mm(sample_via.drill_diameter))
            spacing_mm_str = str(to_mm(sample_via.diameter * 4))
        else:
            via_dia_mm_str = str(DEFAULT_VIA_DIAMETER_MM)
            viar_drill_mm_str = str(DEFAULT_DRILL_MM)
            spacing_mm_str = str(DEFAULT_SPACING_MM)

        self.via_dia = wx.TextCtrl(self, value=via_dia_mm_str)
        self.drill = wx.TextCtrl(self, value=viar_drill_mm_str)
        self.spacing = wx.TextCtrl(self, value=spacing_mm_str)

        self.pattern = wx.Choice(self, choices=PATTERNS)
        self.pattern.SetSelection(PATTERNS.index(DEFAULT_PATTERN))

        # if sample via layer starts in an odd layer then it starts with an offset
        if sample_via and sample_via_start_layer % 2 == 0:
            x_offset_mm_str = str(to_mm(sample_via.diameter * 2))
            y_offset_mm_str = str(to_mm(sample_via.diameter * 2))
        else:
            x_offset_mm_str = str(to_mm(0.0))
            y_offset_mm_str = str(to_mm(0.0))

        self.x_offset = wx.TextCtrl(self, value=x_offset_mm_str)
        self.y_offset = wx.TextCtrl(self, value=y_offset_mm_str)
        offset_tip = (
            "Shifts this run's grid, so a second pass (e.g. a back-side "
            "microvia stitch) doesn't land on top of the first."
        )
        self.x_offset.SetToolTip(offset_tip)
        self.y_offset.SetToolTip(offset_tip)

        names = list(net_names)
        self.net = wx.ComboBox(self, choices=names, style=wx.CB_DROPDOWN)
        if sample_via:
            self.net.SetValue(sample_via_net_name)
        else:
            if DEFAULT_NET in names:
                self.net.SetValue(DEFAULT_NET)
            elif names:
                self.net.SetSelection(0)

        self.avoid_zones = wx.CheckBox(self, label="Avoid zones of other nets")
        self.avoid_zones.SetValue(DEFAULT_AVOID_OTHER_ZONES)
        self.avoid_zones.SetToolTip(
            "Keep vias out of other nets' filled copper on every layer.\n\n"
            "Off by default: a via through another net's pour is not a DRC "
            "error, because KiCad clears the fill back around it when the "
            "zones are refilled.\n\n"
            "Tick this to leave an inner power plane unperforated. Expect far "
            "fewer vias, since such a plane often covers most of the board."
        )

        self.avoid_footprints = wx.CheckBox(self, label="Avoid footprints")
        self.avoid_footprints.SetValue(DEFAULT_AVOID_FOOTPRINTS)
        self.avoid_footprints.SetToolTip(
            "Keep vias out from under every component's bounding box.\n\n"
            "This is about mechanical fit, not clearance, so it applies "
            "whatever net the footprint is on.\n\n"
            "Off by default: a thermal via array under a QFN or BGA ground pad "
            "is a normal use of via stitching, and this would block it."
        )

        self.main_sizer = wx.BoxSizer(wx.VERTICAL)

        self._make_group(self.main_sizer, [
            ("Via Type:", self.via_type),
            ("Start Layer:", self.start_layer),
            ("End Layer:", self.end_layer),
            ("Via Diameter (mm):", self.via_dia),
            ("Drill (mm):", self.drill)
        ])

        self._make_group(self.main_sizer, [
            ("Via Pattern:", self.pattern),
            ("Spacing (mm):", self.spacing),
            ("X-Offset (mm):", self.x_offset),
            ("Y-Offset (mm):", self.y_offset),
            ("Zones:", self.avoid_zones),
            ("Footprints:", self.avoid_footprints)
        ])

        self._make_group(self.main_sizer, [
            ("Net Name:", self.net)
        ])

        # CreateButtonSizer, not a hand-built one: it orders OK/Cancel to match
        # the platform's own convention (OK-then-Cancel on Windows) instead of
        # a fixed left-to-right order that only matches some platforms.
        buttons = self.CreateButtonSizer(wx.OK | wx.CANCEL)

        self.main_sizer.AddSpacer(15)
        self.main_sizer.Add(buttons, 0, wx.EXPAND)

        outer = wx.BoxSizer(wx.VERTICAL)
        outer.Add(self.main_sizer, 1, wx.EXPAND | wx.ALL, 8)
        self.SetSizerAndFit(outer)

        # Constrain Start/End Layer and the offsets to what the initial via
        # type (Through by default, or the preselected via's type) actually
        # supports.
        self._refresh_layer_controls()

    def _layer_domains(self, via_type_name):
        """(start_choices, end_choices_for(start_name)) layer names for a via type.

        Through is always the full board; a microvia's end is whichever inner
        layer sits next to the outer layer picked as start; Blind starts on an
        outer layer and ends anywhere inside; Buried stays inside; Blind/Buried
        keeps the original free-for-all since it has no fixed span shape.
        """
        names = self._all_layer_names
        outer = [names[0], names[-1]]
        inner = names[1:-1]

        if via_type_name == "Through":
            return [names[0]], lambda start: [names[-1]]

        if via_type_name == "Micro":
            def micro_end(start):
                if len(names) < 3:
                    return []
                if start == names[0]:
                    return [names[1]]
                if start == names[-1]:
                    return [names[-2]]
                return []
            return outer, micro_end

        if via_type_name == "Blind":
            return outer, lambda start: inner

        if via_type_name == "Buried":
            return inner, lambda start: inner

        return names, lambda start: names  # Blind/Buried: arbitrary layers

    def _set_layer_combo_choices(self, combo, names, keep):
        """Repopulate a layer BitmapComboBox, keeping `keep` selected if still valid."""
        combo.Clear()
        for name in names:
            rgb = self._layer_colors.get(self.layer_map[name], (128, 128, 128))
            combo.Append(name, _color_swatch(rgb))
        if names:
            combo.SetStringSelection(keep if keep in names else names[0])
        combo.Enable(len(names) > 1)

    def _refresh_layer_controls(self):
        """Make the selected via type drive what's actually selectable.

        Locks Start/End Layer to what the via type can physically be (a
        Through via is always F.Cu/B.Cu, a microvia's end follows its start),
        instead of leaving every layer pair pickable regardless of via type.
        Also disables the offsets for Through, since a single-pass via has no
        second pass to stagger against.
        """
        via_type_name = self.via_type.GetStringSelection()
        start_choices, end_domain = self._layer_domains(via_type_name)

        current_start = self.start_layer.GetStringSelection()
        self._set_layer_combo_choices(self.start_layer, start_choices, current_start)
        new_start = self.start_layer.GetStringSelection()

        end_choices = end_domain(new_start)
        current_end = self.end_layer.GetStringSelection()
        if current_end not in end_choices:
            current_end = end_choices[0] if end_choices else None
        if current_end == new_start and len(end_choices) > 1:
            # Same-layer default (e.g. Buried offers identical start/end lists)
            # would just bounce back as a "must not be the same" error, so
            # steer the default end away from whatever start landed on.
            current_end = next(n for n in end_choices if n != new_start)
        self._set_layer_combo_choices(self.end_layer, end_choices, current_end)

        offsets_apply = via_type_name != "Through"
        self.x_offset.Enable(offsets_apply)
        self.y_offset.Enable(offsets_apply)
        if not offsets_apply:
            self.x_offset.SetValue("0.0")
            self.y_offset.SetValue("0.0")

    def _make_group(self, parent_sizer, rows):
        """rows: list of (label, control) pairs."""
        box = wx.StaticBoxSizer(wx.VERTICAL, self, "")
        grid = wx.FlexGridSizer(0, 2, 5, 5)     # rows grow, 2 cols
        grid.AddGrowableCol(1)
        for label, ctrl in rows:
            grid.Add(wx.StaticText(self, label=label), 0, wx.ALIGN_CENTER_VERTICAL)
            grid.Add(ctrl, 1, wx.EXPAND)
        box.Add(grid, 1, wx.EXPAND | wx.ALL, 5)
        parent_sizer.Add(box, 0, wx.EXPAND | wx.ALL, 5)

    def values(self):
        """Validated dialog values. ValueError carries a user-facing message."""

        via_type_name = self.via_type.GetStringSelection()
        via_type = self.VIA_TYPE_CHOICES[via_type_name]

        if not self.end_layer.GetStringSelection():
            # Only reachable for Micro on a board with no inner copper layer:
            # _layer_domains has no end-layer candidate to offer at all.
            raise ValueError(
                f"{via_type_name} vias need an inner copper layer, and this "
                "board doesn't have one."
            )

        start_layer = self.layer_map[self.start_layer.GetStringSelection()]
        end_layer = self.layer_map[self.end_layer.GetStringSelection()]

        if start_layer == end_layer:
            raise ValueError(f"Start and end layers must not be the same ({start_layer})")

        try:
            via_dia_mm = float(self.via_dia.GetValue())
            drill_mm = float(self.drill.GetValue())
            spacing_mm = float(self.spacing.GetValue())
            x_offset_mm = float(self.x_offset.GetValue())
            y_offset_mm = float(self.y_offset.GetValue())
        except ValueError:
            raise ValueError("Via diameter, drill and spacing and offsets must be numbers (mm).")

        # isfinite first: nan parses fine as a float and then compares False
        # against everything, so it would slip past both checks below and only
        # blow up later, inside from_mm().
        if not all(math.isfinite(v) for v in (via_dia_mm, drill_mm, spacing_mm)):
            raise ValueError(
                "Via diameter, drill and spacing must be real numbers (mm)."
            )
        if min(via_dia_mm, drill_mm, spacing_mm) <= 0:
            raise ValueError(
                "Via diameter, drill and spacing must all be greater than zero."
            )
        if drill_mm >= via_dia_mm:
            raise ValueError(
                f"The drill ({drill_mm} mm) must be smaller than the via diameter "
                f"({via_dia_mm} mm)."
            )

        net_name = self.net.GetValue().strip()
        if not net_name:
            raise ValueError("Pick the net to stitch.")

        return {
            "via_type": via_type,
            "start_layer": start_layer,
            "end_layer": end_layer,
            "via_dia_mm": via_dia_mm,
            "drill_mm": drill_mm,
            "spacing_mm": spacing_mm,
            "pattern": PATTERNS[self.pattern.GetSelection()],
            "net_name": net_name,
            "x_offset_mm": x_offset_mm,
            "y_offset_mm": y_offset_mm,
            "avoid_other_zones": self.avoid_zones.GetValue(),
            "avoid_footprints": self.avoid_footprints.GetValue(),
        }


class ErrorDialog(wx.Dialog):
    """Unexpected-failure report. Selectable, so Ctrl+A and Ctrl+C paste into a bug."""

    def __init__(self, parent, summary, details):
        super().__init__(
            parent,
            title="Via Stitching Error",
            size=(660, 420),
            style=wx.DEFAULT_DIALOG_STYLE | wx.RESIZE_BORDER | wx.STAY_ON_TOP,
        )

        label = wx.StaticText(self, label=summary)
        label.Wrap(620)

        text = wx.TextCtrl(
            self,
            value=details,
            style=wx.TE_MULTILINE | wx.TE_READONLY | wx.TE_DONTWRAP,
        )
        text.SetFont(wx.Font(wx.FontInfo(9).Family(wx.FONTFAMILY_TELETYPE)))

        outer = wx.BoxSizer(wx.VERTICAL)
        outer.Add(label, 0, wx.LEFT | wx.RIGHT | wx.TOP, 12)
        outer.Add(text, 1, wx.EXPAND | wx.ALL, 12)
        outer.Add(
            self.CreateButtonSizer(wx.OK), 0, wx.EXPAND | wx.LEFT | wx.RIGHT | wx.BOTTOM, 12
        )
        self.SetSizer(outer)


def _api_enabled_in_config():
    """Read KiCad's own API setting. True, False, or None if we cannot tell.

    KiCad only binds the API socket while starting up, so "switched off" and
    "switched on after KiCad launched" both look like a refused connection from
    here. The setting on disk is what tells them apart.
    """
    try:
        for config_dir in _kicad_config_dirs():
            path = os.path.join(config_dir, "kicad_common.json")
            if os.path.exists(path):
                with open(path, encoding="utf-8") as fh:
                    return bool(json.load(fh).get("api", {}).get("enable_server"))
    except Exception:
        pass
    return None


def _is_dial_failure(exc):
    """True if this ConnectionError means nothing answered, not that a reply was late.

    kipy raises the same type for both. It phrases a refused socket as "Failed to
    connect to KiCad", and a late reply as "Error receiving reply from KiCad".
    """
    return "Failed to connect" in str(exc)


def _is_busy(exc):
    """True if KiCad refused the call because it is mid-operation.

    This plugin's own parting refill_zones(block=False) is the usual cause: KiCad
    answers AS_BUSY to everything until that fill finishes, so a second run
    started too soon fails on its very first call, board open or not.
    """
    return isinstance(exc, ApiError) and exc.code == ApiStatusCode.AS_BUSY


BUSY_HELP = (
    "KiCad is busy and refused the request.\n\n"
    "It is most likely still refilling the zones from a previous run. Wait for "
    "the PCB editor to go idle, then run this again."
)

NO_BOARD_HELP = (
    "KiCad's API server answered but did not hand over a board.\n\n"
    "Open a board in the PCB editor and run this again."
)


def _connection_help(enabled, dial_failed=True):
    """Wording for a failed connection, given the API setting on disk.

    kipy raises the same ConnectionError for a refused socket and for a reply
    timeout. Only the first says anything about the server not running, so the
    confident advice is gated on dial_failed.
    """
    if not dial_failed:
        return (
            "KiCad did not reply in time.\n\n"
            "It is probably busy, for example filling zones. Wait for it to "
            "finish and run this again."
        )
    if enabled is False:
        # Never mention restarting on its own here: the setting is the real problem.
        return (
            "KiCad's API server is switched off.\n\n"
            "Turn on 'Enable KiCad API' in Preferences > Plugins, then restart "
            "KiCad. The server is only started while KiCad launches, so the "
            "setting does not take effect until then."
        )
    if enabled is True:
        return (
            "KiCad's API server is enabled but not listening.\n\n"
            "Restart KiCad. The server is only started while KiCad launches, so "
            "switching it on in Preferences does nothing for an instance that is "
            "already running.\n\n"
            "Then open a board in the PCB editor and run this again."
        )
    return (
        "Could not talk to KiCad.\n\n"
        "Check that 'Enable KiCad API' is on in Preferences > Plugins, restart "
        "KiCad, and make sure a board is open in the PCB editor."
    )


def _to_stderr(text):
    """KiCad 10.0.1+ shows plugin stderr in the editor's notification area."""
    try:
        print(text, file=sys.stderr or sys.__stderr__)
    except Exception:
        pass


def _msg(parent, text, style):
    """Message box that stays above the PCB editor."""
    wx.MessageBox(text, "Via Stitching", style | wx.STAY_ON_TOP, parent)


def _report(parent, summary, exc):
    """Show an unexpected failure with everything a bug report needs."""
    details = "\n".join(
        [f"{type(exc).__name__}: {exc}", ""] + _ENV + ["", traceback.format_exc()]
    )
    _to_stderr(summary + "\n" + details)
    try:
        dlg = ErrorDialog(parent, summary, details)
        try:
            dlg.ShowModal()
        finally:
            dlg.Destroy()
    except Exception:
        # No usable wx, so stderr above is all the reporting we get.
        pass


def main():
    app = wx.App()  # noqa: F841  (must outlive every window below)
    prepare_app()

    _ENV.extend(
        [
            f"Via Stitching {VERSION}",
            f"kicad-python {_kipy_version()}",
            f"Python {sys.version.split()[0]} on {sys.platform}",
        ]
    )

    try:
        kicad = KiCad(timeout_ms=API_TIMEOUT_MS)
        board = kicad.get_board()
        try:
            _ENV.append(f"KiCad {kicad.get_version()}")
        except Exception:
            pass
        net_names = sorted({n.name for n in board.get_nets() if n.name})
    except KiCadConnectionError as exc:
        # If kipy's wording ever changes we fall back to the vaguer message rather
        # than telling someone to restart KiCad for no reason.
        _report(
            None,
            _connection_help(_api_enabled_in_config(), _is_dial_failure(exc)),
            exc,
        )
        return
    except Exception as exc:
        # The server answered, so it is running. Something else went wrong: KiCad
        # still busy with our own parting zone refill, or no board open.
        _report(None, BUSY_HELP if _is_busy(exc) else NO_BOARD_HELP, exc)
        return

    # The plugin runs as its own process. Give the dialog editor-attached window
    # behavior: no taskbar button on Windows, and a floating window that joins the
    # PCB editor's Stage Manager set on macOS.
    dlg = ViaStitchingDialog(None, net_names, board)
    make_tool_window(dlg)
    attach_to_stage_manager(dlg)
    dlg.CentreOnScreen()

    # The dialog stays visible to the end so every message box has a real parent.
    try:
        if dlg.ShowModal() != wx.ID_OK:
            return
        try:
            params = dlg.values()
        except ValueError as exc:
            _msg(dlg, str(exc), wx.OK | wx.ICON_ERROR)
            return
        _ENV.append(
            "Parameters: " + ", ".join(f"{k}={v}" for k, v in sorted(params.items()))
        )

        busy = wx.BusyCursor()
        try:
            count, grouped = stitch(board, parent=dlg, **params)
        except (RuntimeError, ValueError) as exc:
            # Conditions we raise ourselves, already worded for the user.
            del busy
            _msg(dlg, str(exc), wx.OK | wx.ICON_ERROR)
            return
        except Exception as exc:
            del busy
            _report(
                dlg,
                BUSY_HELP if _is_busy(exc) else "Via Stitching failed while placing vias.",
                exc,
            )
            return
        del busy

        if count:
            text = f"Placed {count} stitching vias on net '{params['net_name']}'."
            if not grouped:
                text += (
                    "\n\nKiCad would not group them, so they delete individually "
                    "rather than as a set. The vias themselves are fine."
                )
            _msg(dlg, text, wx.OK | wx.ICON_INFORMATION)
    finally:
        dlg.Destroy()


if __name__ == "__main__":
    try:
        main()
    except BaseException as exc:  # nothing may exit silently
        _report(None, "Via Stitching hit an unexpected error.", exc)
