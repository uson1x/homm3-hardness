#!/usr/bin/env python3
"""Lemma D.4, executed: the embedding algorithm of the paper, end to end.

Until round 8 the executable artifact behind Theorem 3's boards was a
heuristic router (verify_x3c.build_board): hill-climbed placement, BFS
corridors, honest failures. The proof of Lemma D.4 never depended on it, but
the lemma claimed an *algorithm* and the repository did not contain one —
the round-8 codex leg named this the largest remaining gap between the proof
and the artifact. This module closes it: it is a literal implementation of
the six steps of Lemma D.4 (paper Appendix D.4), on top of the orthogonal
drawing machinery in planar_embed.py.

    build_board_lemma(n_elements, sets) -> ("board", inst)
                                         | ("G_no", {"reason", "instance"})

`inst` has exactly the schema of verify_x3c.build_board's output (plus a
`vertex_images` key — the scaled vertex centres — and a `features` key with
the gadget-box centres and the corridor point chains, so verify_embedding.py
can check the real (SEP') separation over all three non-incident feature
classes), so verify_x3c.check_geometry (invariants I1-I4) and the game
search run on it unchanged. The G_no branch is the lemma's total-reduction
branch: emitted only for encodings that are malformed or certifiably
no-instances (a member of C that is not a 3-set of distinct elements of X,
|X| not a non-negative multiple of 3, |C| < q, an element in no set) or for
a non-planar incidence graph (the verdict of the DMP planarity test in
planar_embed.py, not a heuristic giving up). Its payload carries the
lemma's CONCRETE fixed no-instance (1 × 1 board, one slot, stock 1, no
enemies, W = 1) alongside the reason string — round 10 caught the earlier
version returning a bare tag, which is not the total Karp reduction the
lemma states. Validation runs BEFORE deduplication (a malformed member is
rejected whether or not it repeats; sorting a mixed-type member first would
raise instead of certifying — also a round-10 catch); then duplicate members
of C are deleted, as step 0 instructs. |X| = 0 with C = ∅ is a YES-instance
of X3C (the empty cover), and maps to G_yes: the image of the fixed family
X = {0,1,2}, C = {{0,1,2}} under this very map.

Scale note. The lemma's constants are used literally — λ = 20, ρ = 4, μ = 6,
9 × 9 gadget boxes, the four Lemma D.3 adapters verbatim from
verify_x3c.ADAPTERS — so the boards are large (side ≈ 20·g for a drawing of
side g). That is what the proof constructs; the compact router remains the
board source for the big exhaustive-search suites, and verify_embedding.py
says exactly which checks run on which boards.

Everything here is deterministic: no randomness, no retries, no wall clock.
"""

from __future__ import annotations

import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import planar_embed  # noqa: E402
from verify_x3c import ADAPTERS, creature_types  # noqa: E402

LAMBDA = 20   # scale factor (even), paper D.4 step 4
RHO = 4       # gadget-box radius: boxes are (2ρ+1) × (2ρ+1) = 9 × 9
MU = 6        # offset of the drawing into the board; must exceed ρ, even

# axis directions in board coordinates (y grows downward, as row index)
DIRS = {"T": (0, -1), "R": (1, 0), "B": (0, 1), "L": (-1, 0)}
SIDE_OF_DIR = {v: k for k, v in DIRS.items()}
SIDE_NAME = {"T": "top", "R": "right", "B": "bottom", "L": "left"}
# local-frame port cells of the 9 × 9 adapter box (verify_x3c._PORTS)
PORT_LOCAL = {"T": (4, 0), "R": (8, 4), "B": (4, 8), "L": (0, 4)}


def _g_no_instance():
    """The lemma's fixed no-instance, built concretely: a 1 × 1 board, one
    slot, stock 1, no enemies, W = 1. Destroyed value is 0 under every
    allocation and every play, so the answer is no — for any creature
    constants (verify_embedding.py plays it to confirm)."""
    player, enemy = creature_types(1)
    return {"width": 1, "height": 1, "obstacles": frozenset(),
            "owner": {}, "enemy_hex": {}, "deploy": {}, "dockings": {},
            "sets": [], "n_elements": 0, "vertex_images": (),
            "features": {"lam": LAMBDA, "rho": RHO,
                         "boxes": {}, "corridors": {}},
            "player_type": player, "enemy_type": enemy,
            "stock": 1, "target": 1, "rounds": 1, "q": 0}


def _g_no(reason: str):
    return ("G_no", {"reason": reason, "instance": _g_no_instance()})


def _segment_hexes(a, b):
    """All integer points on the axis-parallel segment from a to b, inclusive."""
    (ax, ay), (bx, by) = a, b
    if ax == bx:
        step = 1 if by >= ay else -1
        return [(ax, y) for y in range(ay, by + step, step)]
    if ay == by:
        step = 1 if bx >= ax else -1
        return [(x, ay) for x in range(ax, bx + step, step)]
    raise ValueError(f"segment {a}-{b} is not axis-parallel")


def _route_hexes(route):
    pts = []
    for i in range(len(route) - 1):
        seg = _segment_hexes(route[i], route[i + 1])
        pts.extend(seg if i == 0 else seg[1:])
    return pts


def _first_dir(route):
    (ax, ay), (bx, by) = route[0], route[1]
    dx, dy = bx - ax, by - ay
    n = max(abs(dx), abs(dy))
    return (dx // n, dy // n)


def build_board_lemma(n_elements, sets):
    """The six steps of Lemma D.4, in order. See the module docstring."""
    # ---- step 0: degenerate inputs and the planarity certificate --------
    # Validation PRECEDES deduplication: a malformed member is rejected
    # whether or not it repeats (so the order swap is sound), and sorting a
    # mixed-type member for the dedupe key would raise TypeError instead of
    # certifying — round 10 caught exactly that.
    if not isinstance(n_elements, int) or isinstance(n_elements, bool) \
            or n_elements < 0:
        return _g_no("malformed encoding: |X| is not a non-negative integer")
    if not isinstance(sets, (list, tuple)):
        return _g_no("malformed encoding: C is not a sequence of 3-sets")
    cleaned = []
    for s in sets:
        if not isinstance(s, (list, tuple)) or len(s) != 3 \
                or not all(isinstance(e, int) and not isinstance(e, bool)
                           for e in s) \
                or len(set(s)) != 3 \
                or not all(0 <= e < n_elements for e in s):
            return _g_no("malformed encoding: a member of C is not a 3-set "
                         "of distinct elements of X")
        cleaned.append(tuple(s))
    seen: set = set()
    sets = []
    for s in cleaned:
        key = tuple(sorted(s))
        if key not in seen:            # "Delete repeated members of C"
            seen.add(key)
            sets.append(s)
    if n_elements % 3 != 0:
        return _g_no("|X| not divisible by 3")
    q = n_elements // 3
    if len(sets) < q:
        return _g_no("|C| < q")
    covered = {e for s in sets for e in s}
    if covered != set(range(n_elements)):
        return _g_no("an element lies in no set")
    if n_elements == 0:
        # |X| = 0 and C = ∅ (a non-empty member was malformed above): the
        # empty cover IS an exact cover, so this is a yes-instance of X3C
        # and must map to a yes-board. G_yes is the image of the fixed
        # yes-family X = {0,1,2}, C = {{0,1,2}} under this very map — a
        # valid ARMY-ALLOCATION instance (W ∈ Z>0), played end to end by
        # verify_embedding.py under both constant sets. (The earlier
        # version emitted a target-0 board, which the paper's problem
        # definition does not admit — a round-10 catch.)
        return build_board_lemma(3, [(0, 1, 2)])

    n_g = n_elements + len(sets)
    g_edges = [(e, n_elements + si) for si, s in enumerate(sets) for e in s]
    rotation = planar_embed.planarity(n_g, g_edges)
    if rotation is None:
        return _g_no("incidence graph is not planar (DMP verdict)")

    # ---- step 1: degree reduction preserving the rotation ---------------
    # element e of degree d becomes a path of d vertices; the i-th incident
    # edge (in the rotation's cyclic order, cut at an arbitrary point — we
    # cut where the returned list starts) attaches to the i-th path vertex
    node_of = {}          # ("s", si) | ("e", e, i)  ->  node id
    meta_of = []          # node id -> the same key
    def add(key):
        node_of[key] = len(meta_of)
        meta_of.append(key)

    for si in range(len(sets)):
        add(("s", si))
    inc_order = {e: [nb - n_elements for nb in rotation[e]]
                 for e in range(n_elements)}
    for e in range(n_elements):
        for i in range(len(inc_order[e])):
            add(("e", e, i))

    gp_edges = []         # (u, v) node ids
    edge_kind = {}        # (u, v) -> ("path", e) | ("inc", si, e)
    for e in range(n_elements):
        for i, si in enumerate(inc_order[e]):
            u, v = node_of[("e", e, i)], node_of[("s", si)]
            gp_edges.append((u, v))
            edge_kind[(u, v)] = ("inc", si, e)
        for i in range(len(inc_order[e]) - 1):
            u, v = node_of[("e", e, i)], node_of[("e", e, i + 1)]
            gp_edges.append((u, v))
            edge_kind[(u, v)] = ("path", e)

    # ---- steps 2-3: orthogonal grid drawing (components packed inside) --
    drawing = planar_embed.orthogonal_drawing(len(meta_of), gp_edges)
    if drawing is None:
        raise RuntimeError("G' must be planar when G is (D.4 step 1); "
                           "planar_embed disagrees — this is a bug")
    bad = planar_embed.validate_drawing(len(meta_of), gp_edges, drawing)
    if bad:
        raise RuntimeError("invalid orthogonal drawing: " + "; ".join(bad))

    # ---- step 4: scaling into hex coordinates ---------------------------
    pts = list(drawing["pos"].values())
    for r in drawing["routes"].values():
        pts.extend(r)
    i_min = min(p[0] for p in pts)
    j_min = min(p[1] for p in pts)

    def phi(p):
        return (LAMBDA * (p[0] - i_min) + MU, LAMBDA * (p[1] - j_min) + MU)

    centre = {v: phi(p) for v, p in drawing["pos"].items()}

    def near_box(h, v):
        cx, cy = centre[v]
        return max(abs(h[0] - cx), abs(h[1] - cy)) <= RHO

    owner = {}            # (x, y) -> ("e", e) | ("s", si)
    def claim(h, who):
        prev = owner.get(h)
        if prev is not None and prev != who:
            raise RuntimeError(f"hex {h} claimed by {prev} and {who}: "
                               f"the separation argument is violated")
        owner[h] = who

    # ports used at every node, and the element that arrives at each port
    # of every set node: needed for step 5's adapter choice and dockings
    used_dirs = {v: {} for v in range(len(meta_of))}   # dir -> edge key
    corridors = {}        # (u, v) -> the scaled corridor point chain, for
                          # the real (SEP') check in verify_embedding.py
    for (u, v), route in drawing["routes"].items():
        scaled = [phi(p) for p in route]
        corridors[(u, v)] = tuple(scaled)
        used_dirs[u][_first_dir(scaled)] = (u, v)
        rev = list(reversed(scaled))
        used_dirs[v][_first_dir(rev)] = (u, v)
        kind = edge_kind[(u, v)]
        e = kind[1] if kind[0] == "path" else kind[2]
        for h in _route_hexes(scaled):
            if near_box(h, u) or near_box(h, v):
                continue                      # truncated at the boxes, step 5
            claim(h, ("e", e))

    # ---- step 5: the gadget boxes ---------------------------------------
    enemy_hex = {}
    deploy = {}
    dockings = {}
    for v, key in enumerate(meta_of):
        cx, cy = centre[v]
        if cy % 2 != 0:               # λ, μ even ⟹ images sit on even rows
            raise RuntimeError(f"vertex image {centre[v]} off the even "
                               f"rows — λ or μ is no longer even")

        def board(local):
            return (cx - RHO + local[0], cy - RHO + local[1])

        if key[0] == "s":
            si = key[1]
            sides = {SIDE_OF_DIR[d]: ek for d, ek in used_dirs[v].items()}
            if len(sides) != 3:
                raise RuntimeError(f"set node {si}: {len(sides)} ports used")
            adapter = ADAPTERS["".join(s for s in "TRBL" if s in sides)]
            for letter, ek in sides.items():
                arm = adapter[SIDE_NAME[letter]]
                _, asi, ae = edge_kind[ek]
                if asi != si:
                    raise RuntimeError(f"set node {si}: port edge {ek} "
                                       f"belongs to set {asi}")
                for local in arm:
                    claim(board(local), ("e", ae))
                dockings[(si, ae)] = board(arm[-1])
            enemy_hex[si] = (cx, cy)
            claim((cx, cy), ("s", si))
        else:
            _, e, i = key
            for d in used_dirs[v]:
                for t in range(0, RHO + 1):
                    claim((cx + d[0] * t, cy + d[1] * t), ("e", e))
            if i == 0:
                # the deployment stub, along a deterministic unused direction
                for letter in "RBLT":
                    if letter not in (SIDE_OF_DIR[d] for d in used_dirs[v]):
                        u = DIRS[letter]
                        break
                claim((cx + u[0], cy + u[1]), ("e", e))
                stub = (cx + 2 * u[0], cy + 2 * u[1])
                claim(stub, ("e", e))
                deploy[e] = stub

    # ---- step 6: closing the board --------------------------------------
    width = LAMBDA * (max(p[0] for p in pts) - i_min) + 2 * MU + 1
    height = LAMBDA * (max(p[1] for p in pts) - j_min) + 2 * MU + 1
    to_index = {}
    for (x, y), who in owner.items():
        if not (0 <= x < width and 0 <= y < height):
            raise RuntimeError(f"hex {(x, y)} outside the {width}x{height} "
                               f"board — the μ margin is broken")
        to_index[x + y * width] = who
    obstacles = frozenset(h for h in range(width * height)
                          if h not in to_index)
    inst = {
        "width": width, "height": height, "obstacles": obstacles,
        "owner": to_index,
        "enemy_hex": {si: h[0] + h[1] * width for si, h in enemy_hex.items()},
        "deploy": {e: h[0] + h[1] * width for e, h in deploy.items()},
        "dockings": {k: h[0] + h[1] * width for k, h in dockings.items()},
        "sets": sets, "n_elements": n_elements,
        # scaled vertex centres, for the direct (SEP') check downstream
        "vertex_images": tuple(sorted(centre.values())),
        # the geometric features themselves — box centres per G' node and
        # corridor point chains per G' edge — so verify_embedding.py can
        # check (SEP') over ALL three non-incident feature classes, not
        # merely the vertex images (round 10: the image-only check was an
        # identity, images being λ times distinct grid points)
        "features": {"lam": LAMBDA, "rho": RHO,
                     "boxes": dict(centre), "corridors": corridors},
    }
    # the same army/defence dressing as verify_x3c.build_instance: σ is the
    # hex count (legal — creature statistics are input, paper sec. 2.1)
    player, enemy = creature_types(width * height)
    inst.update({
        "player_type": player, "enemy_type": enemy,
        "stock": 3 * q, "target": q, "rounds": 1, "q": q,
    })
    return ("board", inst)
