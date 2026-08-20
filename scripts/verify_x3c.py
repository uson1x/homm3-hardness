"""Machine check for candidate D: strong NP-hardness of ARMY-ALLOCATION with a
SINGLE creature type, by reduction from Planar Exact Cover by 3-Sets.

See ../proofs/candidate-D-singletype.md for the construction and the proof.

What this script checks, in order:

  1. The resource lemma (sec. 3 of the writeup).  With the player's attack far
     below the enemy's defence the defence factor is capped, so a stack of `c`
     creatures deals  D(c) = max(1, floor(mu * c))  with mu <= 1/3.  The lemma
     says: to accumulate 3 damage on one enemy you must spend at least 3
     creatures, and exactly 3 only as three separate one-creature stacks.
     Checked exhaustively over stack multisets, and for BOTH values of the
     defence cap that exist in the wild -- Python's 0.7 and the value VCMI's
     hand-written JSON parser actually loads, 0.7000000000000001
     (../engine-check/REPORT.md).

  2. The four enemy adapters (Lemma 4.3).  An orthogonal drawing delivers a
     set-vertex's three edges along three of the four axis directions; the three
     dockings are forced to be an alternating triple of the hex neighbour ring.
     One constant-size routing pattern per case, all four checked.

  3. A negative control.  With the resource lemma deliberately disabled, a
     no-instance of X3C must turn into a yes-instance of the game.  If it does
     not, the rest of the suite is passing for the wrong reason.

  4. The board invariants (sec. 4).  On every constructed board: each enemy has
     exactly three free neighbours, pairwise non-adjacent, each bordering no
     other enemy; the free hexes minus the enemy hexes fall into exactly one
     connected region per X3C element; each region holds exactly one deployment
     hex, on a dead end; and the set of enemies a deployed stack can strike is
     exactly the set of 3-sets containing its element.

  5. The reduction itself.  On small instances, EVERY allocation is tried (no
     count vector is pruned by the construction's own logic) and for each one
     every attack-only play is searched (passing allowed), branching over targets
     and over each legal approach hex; player WAIT and pure moves are not
     branched -- WAIT is discharged on paper (paper sec. 4.1) and pure movement
     is dominated by the --vacate branch below.  The resulting yes/no answer,
     and the set of winning allocations, are compared against X3C decided by
     exhaustive search over covers.

Run:  python3 scripts/verify_x3c.py            (default suite)
      python3 scripts/verify_x3c.py --full     (adds q = 3, 4 instances, slow)
      python3 scripts/verify_x3c.py --vacate   (admit pure movement, see below)
      python3 scripts/verify_x3c.py --defend   (defence executes (‡) literally
                                                instead of holding)

`--vacate` turns on VACATE_BRANCH, which adds a "this stack vanishes" branch to
the play search.  Vanishing dominates every pure move -- a move deals no damage
and affects the rest of the round only through the hex the stack occupies, and
occupying nothing is the most generous such change -- so the search becomes a
sound upper bound over plays that include MOVE-only actions, which neither this
search nor sol's branches over otherwise.  It roughly doubles the search and can
only ever turn a no-instance into a (spurious) yes, so it is the no-instances
that it is worth running on.  Off by default because of the cost.
"""

from __future__ import annotations

import itertools
import math
import os
import random
import sys
import time
from collections import deque

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import homm3_model as M
from homm3_model import Battle, Battlefield, CreatureType, Stack, compute_damage

# --- creature statistics of the construction -------------------------------
#
# candidate-D-singletype.md sec. 2.  The player has ONE type.  The enemy's
# defence exceeds the player's attack by 40, and 0.025 * 40 = 1.0 is well past
# the cap 0.7, so the defence factor sits on the flat part of the curve:
# f_def = 1 - 0.7 = 0.3.  Being far from the kink is deliberate; see sec. 3.3.
PLAYER_ATT = 1
ENEMY_DEF = 41          # 41 - 1 = 40 defence points, cap reached at 28
PLAYER_HP = 5           # survives the single retaliation an enemy has per round
ENEMY_HP = 3            # the "3" of Exact Cover by 3-Sets


def creature_types(speed: int):
    """The two types used by the construction.  `speed` must exceed the enemy's."""
    player = CreatureType(
        name="P", attack=PLAYER_ATT, defense=1, dmg_min=1, dmg_max=1,
        hp=PLAYER_HP, speed=speed, value=0,
    )
    enemy = CreatureType(
        name="E", attack=1, defense=ENEMY_DEF, dmg_min=1, dmg_max=1,
        hp=ENEMY_HP, speed=1, value=1,
    )
    return player, enemy


def stack_damage(c: int) -> int:
    """Damage a player stack of `c` creatures deals to an enemy stack."""
    player, enemy = creature_types(2)
    a = Stack(player, c, 0, 0, 0)
    d = Stack(enemy, 1, 1, 0, 1)
    return compute_damage(a, d)


# --- 1. the resource lemma -------------------------------------------------


def check_resource_lemma(max_stacks: int = 6, max_count: int = 40) -> list[str]:
    """Exhaustive check of Lemma 3.1 of the writeup.

    For every multiset of stack sizes whose damages sum to at least ENEMY_HP,
    the total number of creatures spent is at least ENEMY_HP, with equality
    only for ENEMY_HP stacks of one creature each.
    """
    fails = []
    dmg = {c: stack_damage(c) for c in range(1, max_count + 1)}

    # sanity: the function really is max(1, floor(mu*c)).  Derive mu from the
    # actual statistics rather than assuming the cap is reached -- sol's variant
    # (crosscheck_sol.py) deliberately stays below the cap, and hard-coding
    # 1 - cap here silently mis-stated its multiplier.
    mu = 1.0 - M.defense_skill_factor(PLAYER_ATT, ENEMY_DEF)
    if mu >= 1.0:
        fails.append(f"defence factor mu = {mu!r} is not < 1; Lemma 3.1 does not apply")
    for c in range(1, max_count + 1):
        want = max(1, math.floor(c * mu))
        if dmg[c] != want:
            fails.append(f"D({c}) = {dmg[c]}, expected max(1, floor({mu}*{c})) = {want}")

    best_cost = None
    witnesses = []
    for r in range(1, max_stacks + 1):
        for combo in itertools.combinations_with_replacement(range(1, max_count + 1), r):
            if sum(dmg[c] for c in combo) < ENEMY_HP:
                continue
            cost = sum(combo)
            if best_cost is None or cost < best_cost:
                best_cost = cost
                witnesses = [combo]
            elif cost == best_cost:
                witnesses.append(combo)
    if best_cost != ENEMY_HP:
        fails.append(f"cheapest way to deal {ENEMY_HP} damage costs {best_cost}, expected {ENEMY_HP}")
    if witnesses != [(1,) * ENEMY_HP]:
        fails.append(f"cheapest kill is not unique: {witnesses}")

    # the two quantitative claims the writeup states explicitly
    one_stack = min(c for c in range(1, max_count + 1) if dmg[c] >= ENEMY_HP)
    two_stack = min(
        a + b for a in range(1, max_count + 1) for b in range(1, max_count + 1)
        if dmg[a] + dmg[b] >= ENEMY_HP
    )
    if one_stack <= ENEMY_HP:
        fails.append(f"a single stack reaches {ENEMY_HP} damage with only {one_stack} creatures")
    if two_stack <= ENEMY_HP:
        fails.append(f"two stacks reach {ENEMY_HP} damage with only {two_stack} creatures")
    return fails


def check_resource_lemma_both_caps() -> list[str]:
    """Run the lemma under Python's 0.7 and under the constant VCMI loads.

    ../engine-check/REPORT.md: VCMI's JSON parser accumulates 0.1*d, so the
    literal 0.7 becomes 0.7000000000000001, one ULP high.  The two worlds
    disagree on D(10) (3 versus 2).  The lemma must hold in both.
    """
    fails = []
    original = M.DEFENSE_POINT_DAMAGE_FACTOR_CAP
    for cap, tag in ((0.7, "python 0.7"), (0.7000000000000001, "vcmi 0.7000000000000001")):
        M.DEFENSE_POINT_DAMAGE_FACTOR_CAP = cap
        for f in check_resource_lemma():
            fails.append(f"[{tag}] {f}")
    M.DEFENSE_POINT_DAMAGE_FACTOR_CAP = original
    return fails


# --- 2. the board ----------------------------------------------------------
#
# Layout.  Everything not listed as free is an impassable hex (MODEL.md sec. 2).
#
#   enemy gadget for a 3-set S, anchored at (X, Y) with Y EVEN:
#       z_S = (X, Y)            the enemy stack
#       free neighbours         (X, Y-1)  TOP_LEFT
#                               (X+1, Y)  RIGHT
#                               (X, Y+1)  BOTTOM_LEFT
#       impassable neighbours   (X+1, Y-1), (X+1, Y+1), (X-1, Y)
#     The three free ones are the alternating triple of the neighbour cycle, so
#     they are pairwise NON-adjacent -- that is what disconnects the regions.
#
#   element gadget for e, anchored at (X, Y):
#       p_e = (X, Y)            the deployment hex, kept a dead end
#       hub = (X+1, Y)          its single free neighbour
#     The region of e then grows as a tree: each corridor is routed from one of
#     e's dockings until it meets a hex already known to be connected to the hub.
#     Because p_e is a leaf, a stack standing there is never on a path between
#     two other hexes and so can block nothing.
#
#   corridors: hex paths, routed so that no hex of one element's region is
#   adjacent to a hex of another element's region or to an enemy hex (other
#   than a docking touching its own enemy).

CELL = 8  # spacing of the placement lattice, in hexes

# When true the play search also branches on "this stack vanishes", which
# dominates every pure move; see _best_value.  Off by default because it doubles
# the search and only matters for no-instances.  Enabled by `--vacate`.
# (crosscheck_sol.py does not use this flag: it runs its own vanish-admitting
# search over sol's two hand-built boards, in pure_movement_on_sols_own_board.)
VACATE_BRANCH = False

# The defence's scripted policy inside the reduction-level search.
#   "hold"       -- the enemy's turn is skipped (the historical baseline);
#   "waitdefend" -- the paper's `(‡)`: every enemy issues WAIT at its NORMAL
#                   activation and DEFEND at its postponed WAIT-phase activation,
#                   with the +20% (floor +1) bonus live in the damage formula.
# Round 8 of external review pointed out that no Theorem-3 reduction search had
# ever executed `(‡)` literally; this switch closes that.  Because the searched
# fragment is attack-only for the player, every searched blow lands in the
# NORMAL phase before any postponed DEFEND (the one-round lemma, paper sec. 2.4),
# so answers must be IDENTICAL to "hold" -- running it verifies exactly that.
ENEMY_POLICY = "hold"


def _neighbours(W: int, H: int, h: int):
    x, y = h % W, h // W
    odd = y % 2
    for nx, ny in ((x - 1, y), (x + 1, y),
                   (x - odd, y - 1), (x + 1 - odd, y - 1),
                   (x - odd, y + 1), (x + 1 - odd, y + 1)):
        if 0 <= nx < W and 0 <= ny < H:
            yield nx + ny * W


def build_board(n_elements: int, sets: list[tuple], rng: random.Random,
                tries: int = 400):
    """Lay the incidence structure of an X3C instance out on a hex grid.

    Returns a dict describing the board, or None if the router failed (which it
    does for instances whose incidence graph is not planar, and sometimes for
    planar ones -- the router is a heuristic; correctness of the reduction
    depends only on the invariants checked afterwards, never on the router).

    Retries are capped by attempt COUNT only, never by wall-clock time: an
    earlier revision also broke out of the loop after a 25-second deadline,
    which made the built/skipped split of a suite depend on machine load (the
    deadline cut the rng stream at a load-dependent point, shifting every
    subsequent board).  Round-8 review caught the symptom; with the deadline
    gone, a fixed seed reproduces the same boards bit-for-bit on any machine.
    """
    incident = {e: [] for e in range(n_elements)}
    for si, s in enumerate(sets):
        for e in s:
            incident[e].append(si)
    n_items = n_elements + len(sets)

    items = [("e", e) for e in range(n_elements)] + [("s", s) for s in range(len(sets))]
    edges = [(("e", e), ("s", si)) for e in range(n_elements) for si in incident[e]]

    for attempt in range(tries):
        # the router is a heuristic; when it fails, retry with a roomier lattice
        G = max(3, int(math.ceil(math.sqrt(n_items))) + 2 + attempt // 40)
        W = H = G * CELL
        cells = _place(items, edges, G, rng)
        anchors = {it: (i * CELL + 2, j * CELL + 2)      # j*CELL+2 is even
                   for it, (i, j) in cells.items()}

        owner = {}            # free hex -> ("e", element) or ("s", set)
        dockings = {}         # (set, element) -> hex
        for si in range(len(sets)):
            X, Y = anchors[("s", si)]
            owner[X + Y * W] = ("s", si)
            docks = [X + (Y - 1) * W, (X + 1) + Y * W, X + (Y + 1) * W]
            # which element gets which of the three arms is free, and the choice
            # is exactly what a planar embedding fixes; the router guesses it
            members = list(sets[si])
            rng.shuffle(members)
            for e, d in zip(members, docks):
                owner[d] = ("e", e)
                dockings[(si, e)] = d

        deploy = {}
        for e in range(n_elements):
            X, Y = anchors[("e", e)]
            deploy[e] = X + Y * W          # the deployment hex, a leaf
            owner[X + Y * W] = ("e", e)
            owner[(X + 1) + Y * W] = ("e", e)   # its single free neighbour

        if len(owner) != 4 * len(sets) + 2 * n_elements:
            continue                        # gadgets collided
        if not _regions_separated(W, H, owner, set(dockings.values())):
            continue

        # corridors must keep clear of the deployment hexes, so each stays a leaf
        keep_clear = set(deploy.values())
        jobs = [(si, e) for e in range(n_elements) for si in incident[e]]
        routed = None
        for _order in range(12):
            rng.shuffle(jobs)
            trial = dict(owner)
            # hexes of element e already known to be connected to its hub; a
            # corridor must land on one of these, otherwise two dockings can end
            # up joined to each other but not to the deployment hex
            hub = {e: {deploy[e], deploy[e] + 1} for e in range(n_elements)}
            ok = True
            for si, e in jobs:
                src = dockings[(si, e)]
                path = _route(W, H, trial, src, ("e", e), hub[e], keep_clear)
                if path is None:
                    ok = False
                    break
                for h in path:
                    trial[h] = ("e", e)
                hub[e].update(path)
                hub[e].add(src)
            if ok:
                routed = trial
                break
        if routed is None:
            continue

        obstacles = frozenset(h for h in range(W * H) if h not in routed)
        return {
            "width": W, "height": H, "obstacles": obstacles,
            "owner": routed,
            "enemy_hex": {si: anchors[("s", si)][0] + anchors[("s", si)][1] * W
                          for si in range(len(sets))},
            "deploy": deploy,
            "dockings": dockings,
            "sets": sets, "n_elements": n_elements,
        }
    return None


def _place(items, edges, G, rng):
    """Assign lattice cells to gadgets, hill-climbing on total incidence length.

    Placement quality is a convenience, not a correctness matter: whatever comes
    out is checked by `check_geometry`.
    """
    cells = [(i, j) for i in range(G) for j in range(G)]
    rng.shuffle(cells)
    pos = {it: cells[n] for n, it in enumerate(items)}
    free = cells[len(items):]

    def cost():
        return sum(abs(pos[a][0] - pos[b][0]) + abs(pos[a][1] - pos[b][1])
                   for a, b in edges)

    cur = cost()
    for _ in range(400):
        a = rng.choice(items)
        old = pos[a]
        if free and rng.random() < 0.4:
            k = rng.randrange(len(free))
            pos[a] = free[k]
            new = cost()
            if new <= cur:
                cur = new
                free[k] = old
            else:
                pos[a] = old
        else:
            b = rng.choice(items)
            if b is a:
                continue
            pos[a], pos[b] = pos[b], pos[a]
            new = cost()
            if new <= cur:
                cur = new
            else:
                pos[a], pos[b] = pos[b], pos[a]
    return pos


def _regions_separated(W, H, owner, dockings) -> bool:
    """No two differently-owned hexes touch, except a docking and its own enemy."""
    for h, o in owner.items():
        for n in _neighbours(W, H, h):
            if n in owner and owner[n] != o:
                pair = (h, n) if o[0] == "e" else (n, h)
                if pair[0] in dockings and owner[pair[1]][0] == "s":
                    # a docking is allowed to touch exactly one enemy; that it is
                    # the right one is re-checked by check_geometry (I1)
                    continue
                return False
    return True


def _route(W, H, owner, src, tag, hub, keep_clear=frozenset()):
    """BFS a corridor from the docking `src` to the region already owned by `tag`.

    A hex may be entered only if it is unclaimed and none of its neighbours is
    claimed by a different owner.  That single rule enforces both "regions of
    different elements never touch" and "a corridor never runs alongside an
    enemy", which together give invariants I1-I3.  The corridor may end anywhere
    on its own element's region, so the region grows as a tree.
    """
    def usable(h):
        if h in owner:
            return False
        for n in _neighbours(W, H, h):
            if n in owner and owner[n] != tag:
                return False
            if n in keep_clear:
                return False
        return True

    prev = {src: None}
    q = deque([src])
    while q:
        cur = q.popleft()
        for nxt in _neighbours(W, H, cur):
            if nxt in prev:
                continue
            if nxt in hub:
                path = []
                p = cur
                while p is not None and p != src:
                    path.append(p)
                    p = prev[p]
                return list(reversed(path))
            if usable(nxt):
                prev[nxt] = cur
                q.append(nxt)
    return None


def build_instance(n_elements: int, sets: list[tuple], rng: random.Random):
    """Full ARMY-ALLOCATION instance: board, army, defence, R, W."""
    board = build_board(n_elements, sets, rng)
    if board is None:
        return None
    q = n_elements // 3
    speed = board["width"] * board["height"]
    player, enemy = creature_types(speed)
    board.update({
        "player_type": player, "enemy_type": enemy,
        "stock": 3 * q, "target": q, "rounds": 1, "q": q,
    })
    return board


def build_battle(inst, alloc: dict) -> tuple[Battle, dict]:
    """`alloc` maps element -> creature count."""
    field = Battlefield(width=inst["width"], height=inst["height"],
                        obstacles=inst["obstacles"])
    stacks = []
    slot_of = {}
    for e in sorted(inst["deploy"]):
        c = alloc.get(e, 0)
        if c <= 0:
            continue
        slot_of[e] = len(stacks)
        stacks.append(Stack(inst["player_type"], c, 0, e, inst["deploy"][e]))
    enemy_index = {}
    for si in sorted(inst["enemy_hex"]):
        enemy_index[si] = len(stacks)
        stacks.append(Stack(inst["enemy_type"], 1, 1, si, inst["enemy_hex"][si]))
    battle = Battle(field, stacks)
    initial = {i: s.count() for i, s in enumerate(stacks)}
    return battle, initial


# --- 2a. the enemy adapter, four cases ------------------------------------
#
# In an orthogonal drawing a degree-3 vertex is met by its three edges along
# three of the four axis directions; which three is not ours to choose.  The
# enemy's three free neighbours, on the other hand, are forced to be an
# alternating triple of the neighbour ring -- here TOP_LEFT, RIGHT, BOTTOM_LEFT.
# The gap is bridged by a constant-size box that routes the three incoming
# corridors to the three dockings.  There are four cases, one per missing
# direction; all four are written out below and checked.
#
# Local frame: a 9 x 9 patch, the enemy at (4,4), row 4 even.
#   U = (4,3)  TOP_LEFT      R = (5,4)  RIGHT      D = (4,5)  BOTTOM_LEFT
# Ports (where a corridor crosses the box boundary): top (4,0), right (8,4),
# bottom (4,8), left (0,4).

ADAPTERS = {
    # missing LEFT: everything is straight
    "TRB": {"top":    [(4, 0), (4, 1), (4, 2), (4, 3)],
            "right":  [(8, 4), (7, 4), (6, 4), (5, 4)],
            "bottom": [(4, 8), (4, 7), (4, 6), (4, 5)]},
    # missing RIGHT: the left arm dips to BOTTOM_LEFT, the bottom arm swings
    # around to RIGHT, preserving the cyclic order top -> bottom -> left
    "TBL": {"top":    [(4, 0), (4, 1), (4, 2), (4, 3)],
            "bottom": [(4, 8), (4, 7), (5, 7), (6, 7), (6, 6), (6, 5), (6, 4), (5, 4)],
            "left":   [(0, 4), (1, 4), (2, 4), (2, 5), (3, 5), (4, 5)]},
    # missing BOTTOM
    "TRL": {"top":    [(4, 0), (4, 1), (4, 2), (4, 3)],
            "right":  [(8, 4), (7, 4), (6, 4), (5, 4)],
            "left":   [(0, 4), (1, 4), (2, 4), (2, 5), (3, 5), (4, 5)]},
    # missing TOP
    "RBL": {"right":  [(8, 4), (7, 4), (6, 4), (5, 4)],
            "bottom": [(4, 8), (4, 7), (4, 6), (4, 5)],
            "left":   [(0, 4), (1, 4), (2, 4), (2, 3), (3, 3), (4, 3)]},
}

_PORTS = {"top": (4, 0), "right": (8, 4), "bottom": (4, 8), "left": (0, 4)}


def check_enemy_adapters() -> list[str]:
    """Lemma 4.3: each of the four adapters is a legal enemy gadget."""
    fails = []
    f = Battlefield(width=9, height=9)
    z = f.index(4, 4)
    docks = {f.index(4, 3), f.index(5, 4), f.index(4, 5)}
    for name, arms in ADAPTERS.items():
        paths = {k: [f.index(x, y) for (x, y) in v] for k, v in arms.items()}
        if len(paths) != 3:
            fails.append(f"adapter {name}: {len(paths)} arms, expected 3")
        # each arm starts at its port and ends at a docking, one docking each
        ends = set()
        for side, p in paths.items():
            if p[0] != f.index(*_PORTS[side]):
                fails.append(f"adapter {name}: {side} arm does not start at the port")
            if p[-1] not in docks:
                fails.append(f"adapter {name}: {side} arm does not end at a docking")
            ends.add(p[-1])
            for a, b in zip(p, p[1:]):
                if not f.adjacent(a, b):
                    fails.append(f"adapter {name}: {side} arm is not a path at {a}->{b}")
            # only the last hex of an arm may touch the enemy
            for h in p[:-1]:
                if f.adjacent(h, z):
                    fails.append(f"adapter {name}: {side} arm touches the enemy at {h}")
        if ends != docks:
            fails.append(f"adapter {name}: arms cover {sorted(ends)}, expected the "
                         f"alternating triple {sorted(docks)}")
        # arms of different elements must never touch
        for (s1, p1), (s2, p2) in itertools.combinations(paths.items(), 2):
            touch = [(a, b) for a in p1 for b in p2 if a == b or f.adjacent(a, b)]
            if touch:
                fails.append(f"adapter {name}: arms {s1} and {s2} touch at {touch[:3]}")
        # arms stay inside the box and clear of its unused sides
        used = {h for p in paths.values() for h in p}
        for side, port in _PORTS.items():
            if side not in paths and f.index(*port) in used:
                fails.append(f"adapter {name}: uses the unused {side} port")
    return fails


# --- 2b. the board invariants ---------------------------------------------


def check_geometry(inst) -> list[str]:
    """Invariants I1-I4 of the writeup, checked on the constructed board."""
    fails = []
    W, H = inst["width"], inst["height"]
    field = Battlefield(width=W, height=H, obstacles=inst["obstacles"])
    free = set(inst["owner"])
    enemies = set(inst["enemy_hex"].values())

    # I1: every enemy has exactly three free neighbours, pairwise non-adjacent
    for si, z in inst["enemy_hex"].items():
        nb = [n for n in field.neighbours(z) if n in free]
        if len(nb) != 3:
            fails.append(f"enemy {si} has {len(nb)} free neighbours, expected 3")
            continue
        for a, b in itertools.combinations(nb, 2):
            if field.adjacent(a, b):
                fails.append(f"enemy {si}: docking hexes {a},{b} are adjacent")
        got = {inst["owner"][n] for n in nb}
        want = {("e", e) for e in inst["sets"][si]}
        if got != want:
            fails.append(f"enemy {si}: dockings belong to {got}, expected {want}")
        # I3: a docking borders its own enemy and no other
        for d in nb:
            touched = [t for t in enemies if field.adjacent(d, t)]
            if touched != [z]:
                fails.append(f"enemy {si}: docking {d} borders enemies {touched}, "
                             f"expected only {z}")

    # I2/I3: free hexes minus enemy hexes split into one region per element,
    # each containing exactly one deployment hex
    seen = set()
    regions = []
    for h in free - enemies:
        if h in seen:
            continue
        comp = {h}
        stack = [h]
        while stack:
            cur = stack.pop()
            for n in field.neighbours(cur):
                if n in free and n not in enemies and n not in comp:
                    comp.add(n)
                    stack.append(n)
        seen |= comp
        regions.append(comp)
    if len(regions) != inst["n_elements"]:
        fails.append(f"{len(regions)} regions, expected {inst['n_elements']}")
    for comp in regions:
        deployed = [e for e, p in inst["deploy"].items() if p in comp]
        if len(deployed) != 1:
            fails.append(f"a region holds {len(deployed)} deployment hexes, expected 1")

    # the deployment hex is a leaf: a stack standing there blocks no path
    for e, p in inst["deploy"].items():
        nb = [n for n in field.neighbours(p) if n in free]
        if len(nb) != 1:
            fails.append(f"deployment hex of element {e} has {len(nb)} free neighbours, expected 1")

    # I4: with every slot occupied, slot e can strike exactly the sets containing e
    alloc = {e: 1 for e in inst["deploy"]}
    battle, _ = build_battle(inst, alloc)
    enemy_of_hex = {h: si for si, h in inst["enemy_hex"].items()}
    for s in battle.stacks:
        if s.side != 0:
            continue
        got = {enemy_of_hex[t.hex] for t in battle.attackable(s)}
        want = {si for si, st in enumerate(inst["sets"]) if s.slot in st}
        if got != want:
            fails.append(f"slot {s.slot} reaches sets {sorted(got)}, expected {sorted(want)}")
        for t in battle.attackable(s):
            spots = battle.attack_spots(s, t)
            if len(spots) != 1:
                fails.append(f"slot {s.slot} has {len(spots)} approach hexes on "
                             f"enemy {enemy_of_hex[t.hex]}, expected 1")
    return fails


# --- 3. exhaustive game solver --------------------------------------------


def _state_key(battle: Battle, i: int):
    return (i, tuple((s.full_units, s.first_hp_left, s.hex, s.retaliations_left,
                      s.defending)
                     for s in battle.stacks))


def _upper_bound(battle: Battle, order, i, initial) -> int:
    """Admissible bound on the value still obtainable from this state.

    Every player stack strikes at most once in the round and delivers at most
    D(count) damage (overkill is discarded, MODEL.md sec. 3), so the damage still
    to come is bounded by the sum of D over the stacks that have not acted.  An
    enemy dies only when 3 damage has accumulated on it.  Ignoring reachability
    entirely and packing the cheapest enemies first therefore over-counts kills,
    which is what makes this a bound.  It says nothing about geometry, so it
    cannot mask a mistake in the part of the proof that is actually delicate.
    """
    capacity = 0
    enemy = None
    for idx in order[i:]:
        s = battle.stacks[idx]
        if s.side == 0 and s.alive():
            if enemy is None:
                enemy = next(t for t in battle.stacks if t.side == 1)
            capacity += compute_damage(s, enemy)
    need = sorted(s.available() for s in battle.stacks if s.side == 1 and s.alive())
    extra = 0
    for n in need:
        if capacity >= n:
            capacity -= n
            extra += 1
        else:
            break
    return M.destroyed_value(battle, initial) + extra


def _best_value(battle: Battle, order, i, initial, target, memo):
    """Max destroyed value from this point, with early exit once `target` is hit.

    Mirrors empirics/scripts/solve.py::_play -- branch over targets and over every
    legal approach hex, never over a canonical one -- plus memoisation on the full
    battle state, which is sound because the state is all that the future depends on.
    """
    if i == len(order):
        return M.destroyed_value(battle, initial)
    key = _state_key(battle, i)
    if key in memo:
        return memo[key]
    if _upper_bound(battle, order, i, initial) < target:
        memo[key] = 0
        return 0            # only "< target" is ever asked of this number

    idx = order[i]
    stack = battle.stacks[idx]
    if not stack.alive():
        return _best_value(battle, order, i + 1, initial, target, memo)
    if stack.side == 1:
        if ENEMY_POLICY == "hold":                # policy: the defence holds
            return _best_value(battle, order, i + 1, initial, target, memo)
        # `(‡)`: this is the enemy's postponed WAIT-phase activation -> DEFEND.
        # Deterministic, so no branching; clone so sibling branches and memo
        # entries never see the mutation (the round-7a state-leak lesson).
        nxt = battle.clone()
        e = nxt.stacks[idx]
        nxt.activate(e)
        nxt.act_defend(e)
        return _best_value(nxt, order, i + 1, initial, target, memo)

    best = _best_value(battle, order, i + 1, initial, target, memo)  # pass
    if VACATE_BRANCH and best < target:
        # Over-approximation of PURE MOVEMENT, which neither this search nor
        # sol's branches over (both branch only on pass and attack).  A stack
        # that moves without attacking deals no damage and changes the rest of
        # the round only through which hex it occupies; the most generous such
        # change is to occupy nothing at all.  Removing the stack outright
        # therefore dominates every pure move, so if the value stays below the
        # target here, no pure move could have reached it either.
        ghost = battle.clone()
        g = ghost.stacks[order[i]]
        g.apply_damage(g.available())
        best = max(best, _best_value(ghost, order, i + 1, initial, target, memo))
    if best < target:
        for t in battle.attackable(stack):
            t_idx = battle.stacks.index(t)
            for dest in battle.attack_spots(stack, t):
                nxt = battle.clone()
                nxt.resolve_attack(nxt.stacks[idx], nxt.stacks[t_idx], dest=dest)
                best = max(best, _best_value(nxt, order, i + 1, initial, target, memo))
                if best >= target:
                    break
            if best >= target:
                break
    memo[key] = best
    return best


def play_value(inst, alloc: dict, target: int) -> int:
    battle, initial = build_battle(inst, alloc)
    order = [battle.stacks.index(s) for s in battle.turn_order()]
    if ENEMY_POLICY == "waitdefend":
        # The `(‡)` schedule: enemies issue WAIT at their NORMAL activation
        # (deterministic and otherwise effect-free, so the flags are set up
        # front), and their postponed activations run in the WAIT phase --
        # increasing speed, after ALL normal turns (CBattleInfoCallback.cpp:
        # 495-519; engine-executed in engine-check T-wait-increasing).
        for s in battle.stacks:
            if s.side == 1:
                s.waited = True
        order = [j for j in order if battle.stacks[j].side == 0]
        order += [battle.stacks.index(s) for s in battle.wait_phase_order()
                  if s.side == 1]
    return _best_value(battle, order, 0, initial, target, {})


def _allocations(k: int, stock: int):
    """Every vector of k non-negative counts summing to at most `stock`."""
    def rec(i, left, acc):
        if i == k:
            yield tuple(acc)
            return
        for c in range(left + 1):
            acc.append(c)
            yield from rec(i + 1, left - c, acc)
            acc.pop()
    return rec(0, stock, [])


def winning_allocations(inst, stop_at_first=False) -> list[tuple]:
    """Every allocation of the single type that admits a play reaching W.

    No allocation is pruned: all vectors of counts summing to at most the stock
    are tried, so a construction that could be beaten by an unintended stack
    sizing would show up here as an extra winner.
    """
    elements = sorted(inst["deploy"])
    target = inst["target"]
    out = []
    for vec in _allocations(len(elements), inst["stock"]):
        alloc = dict(zip(elements, vec))
        if play_value(inst, alloc, target) >= target:
            out.append(vec)
            if stop_at_first:
                break
    return out


def game_is_yes(inst) -> tuple[bool, tuple | None]:
    wins = winning_allocations(inst, stop_at_first=True)
    return (bool(wins), wins[0] if wins else None)


def x3c_is_yes(n_elements: int, sets: list[tuple]) -> bool:
    q = n_elements // 3
    for combo in itertools.combinations(range(len(sets)), q):
        seen = set()
        for si in combo:
            seen |= set(sets[si])
        if len(seen) == n_elements:
            return True
    return False


# --- instance families -----------------------------------------------------


def random_instances(q: int, n_sets: int, count: int, seed: int):
    rng = random.Random(seed)
    universe = list(range(3 * q))
    n_sets = min(n_sets, math.comb(3 * q, 3))
    out = []
    seen = set()
    guard = 0
    while len(out) < count and guard < 4000:
        guard += 1
        sets = set()
        while len(sets) < n_sets:
            sets.add(tuple(sorted(rng.sample(universe, 3))))
        sets = tuple(sorted(sets))
        if sets in seen:
            continue
        seen.add(sets)
        out.append((3 * q, list(sets)))
    return out


def planted_instances(q: int, extra: int, count: int, seed: int):
    """Instances that certainly contain an exact cover, plus decoy sets."""
    rng = random.Random(seed)
    universe = list(range(3 * q))
    out = []
    for _ in range(count):
        perm = universe[:]
        rng.shuffle(perm)
        sets = {tuple(sorted(perm[3 * i:3 * i + 3])) for i in range(q)}
        while len(sets) < q + extra:
            sets.add(tuple(sorted(rng.sample(universe, 3))))
        out.append((3 * q, sorted(sets)))
    return out


def run_suite(families, seed=7, verbose=True):
    rng = random.Random(seed)
    stats = {"built": 0, "skipped": 0, "yes": 0, "no": 0}
    fails = []
    for n_elements, sets in families:
        inst = build_instance(n_elements, sets, rng)
        if inst is None:
            stats["skipped"] += 1
            continue
        stats["built"] += 1
        geo = check_geometry(inst)
        if geo:
            fails += [f"{sets}: {g}" for g in geo]
            continue
        want = x3c_is_yes(n_elements, sets)
        wins = winning_allocations(inst)
        got = bool(wins)
        stats["yes" if want else "no"] += 1
        if want != got:
            fails.append(f"{sets}: X3C={want} but game={got} (allocs {wins[:3]})")
        elif got:
            # the construction predicts exactly one winner: one creature per slot
            if wins != [(1,) * n_elements]:
                fails.append(f"{sets}: winning allocations are {wins[:5]}, "
                             f"expected only all-ones")
        if verbose:
            mark = "ok " if want == got else "FAIL"
            print(f"  {mark} q={n_elements // 3} sets={len(sets)} "
                  f"X3C={'Y' if want else 'N'} game={'Y' if got else 'N'} "
                  f"winners={len(wins)}")
    return stats, fails


def check_negative_control(rng: random.Random) -> list[str]:
    """Show the suite is not vacuous: break the resource lemma, see the check fail.

    Set the enemy's defence equal to the player's attack.  Then `Delta = 0`, no
    defence factor applies, and D(c) = c: three creatures in ONE slot now kill an
    enemy on their own.  Killing q enemies no longer forces disjoint 3-sets, only
    q distinct ones, so a no-instance of X3C should turn into a yes-instance of the
    game.  If it did not, the suite would be passing for the wrong reason.
    """
    fails = []
    # a no-instance of X3C (the two 3-sets overlap, so they cannot cover 6
    # elements) whose incidence graph is planar, with q = 2 sets available
    sets = [(0, 1, 2), (0, 1, 3)]
    n = 6
    if x3c_is_yes(n, sets):
        return ["negative control: the fixture is a yes-instance of X3C"]

    original = globals()["ENEMY_DEF"]
    try:
        globals()["ENEMY_DEF"] = PLAYER_ATT          # no defence factor at all
        if stack_damage(3) != 3:
            fails.append(f"negative control: D(3) = {stack_damage(3)}, expected 3")
        inst = build_instance(n, sets, rng)
        if inst is None:
            return ["negative control: the router could not build the fixture"]
        geo = check_geometry(inst)
        if geo:
            return [f"negative control: {g}" for g in geo]
        wins = winning_allocations(inst)
        if not wins:
            fails.append("negative control: the game is still a no-instance with the "
                         "resource lemma disabled, so the suite would not notice its loss")
    finally:
        globals()["ENEMY_DEF"] = original
    if stack_damage(3) != 1:
        fails.append("negative control: failed to restore the enemy's defence")
    return fails


def main() -> int:
    full = "--full" in sys.argv
    if "--vacate" in sys.argv:
        globals()["VACATE_BRANCH"] = True
    if "--defend" in sys.argv:
        globals()["ENEMY_POLICY"] = "waitdefend"
    print("=" * 72)
    print("candidate D: single-type strong NP-hardness, machine check")
    print("=" * 72)
    print(f"pure-movement branch (VACATE_BRANCH): "
          f"{'ON -- plays may also vacate a hex' if VACATE_BRANCH else 'off'}")
    print(f"defence policy: "
          f"{'(‡) WAIT-then-DEFEND, executed literally' if ENEMY_POLICY == 'waitdefend' else 'hold'}")

    print("\n[1] resource lemma, both defence caps")
    fails = check_resource_lemma_both_caps()
    if fails:
        for f in fails:
            print("   FAIL", f)
        return 1
    print("   damage table:", {c: stack_damage(c) for c in (1, 2, 3, 6, 7, 9, 10)})
    print("   cheapest 3 damage = 3 creatures, uniquely as (1,1,1); "
          "1 stack needs >= 10, 2 stacks need >= 8")

    print("\n[2] the four enemy adapters")
    fails = check_enemy_adapters()
    if fails:
        for f in fails:
            print("   FAIL", f)
        return 1
    print(f"   {len(ADAPTERS)} adapters: arms are paths, land on the alternating "
          f"triple, touch the enemy only at their docking, never touch each other")

    print("\n[3] negative control: disable the resource lemma, the check must fail")
    fails = check_negative_control(random.Random(99))
    if fails:
        for f in fails:
            print("   FAIL", f)
        return 1
    print("   with def(Q) = att(P) a no-instance of X3C becomes a yes-instance of "
          "the game, as it must")

    print("\n[4] reduction on q=1 instances (smoke test)")
    # exactly one q=1 family exists on three elements (round 9 removed a
    # literal duplicate of it that inflated the published count by one)
    s1, f1 = run_suite([(3, [(0, 1, 2)])], seed=101)
    print("\n[5] reduction on q=2 instances (planted covers + random)")
    fams = (planted_instances(2, 2, 10, seed=3)
            + random_instances(2, 3, 10, seed=5)
            + random_instances(2, 4, 10, seed=41))
    s2, f2 = run_suite(fams, seed=202)

    allfails = f1 + f2
    stats = [s1, s2]
    if full:
        print("\n[6] reduction on q=3 and q=4 instances (slower)")
        fams3 = (planted_instances(3, 2, 8, seed=13)
                 + random_instances(3, 6, 10, seed=17)
                 + planted_instances(4, 2, 5, seed=23)
                 + random_instances(4, 7, 5, seed=29))
        s3, f3 = run_suite(fams3, seed=303)
        allfails += f3
        stats.append(s3)

    built = sum(s["built"] for s in stats)
    skipped = sum(s["skipped"] for s in stats)
    yes = sum(s["yes"] for s in stats)
    no = sum(s["no"] for s in stats)
    print("\n" + "-" * 72)
    print(f"instances built {built}, skipped by the router {skipped}, "
          f"X3C yes {yes} / no {no}, "
          f"vacate branch {'ON' if VACATE_BRANCH else 'off'}")
    if allfails:
        print(f"FAILURES ({len(allfails)}):")
        for f in allfails[:40]:
            print("  ", f)
        return 1
    print("ALL PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
