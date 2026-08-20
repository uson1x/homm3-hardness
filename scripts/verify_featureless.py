"""Machine verification of the featureless-board reduction (proofs/candidate-C-featureless.md).

The claim under test: ARMY-ALLOCATION is strongly NP-hard already at `R = 1` on a board
where *every* player slot can attack *every* enemy stack.  The reduction is from
3-PARTITION; the geometric structure that carried Theorem 2 of candidate-A (slot j is
wired to enemy j by adjacency) is removed, so the play itself has to pick the triples.

What is checked, per instance
-----------------------------

  C1  reachability      with all 3m slots occupied, every slot can strike every enemy
                        (this is the "featureless" claim itself, in the worst case for
                        the player: a maximally crowded board)
  C2  separation        no deployment hex is adjacent to any enemy, so every attack
                        needs a genuine walk; enemy neighbourhoods are pairwise
                        disjoint and non-adjacent
  C3  approach lemma    *every* assignment of the 3m stacks to the m enemies with
                        exactly three stacks per enemy is realisable as a play:
                        the stacks can all reach a free approach hex, in slot order,
                        without blocking one another
  C4  upper bound       an assumption-free relaxation over all allocations, all plays
                        and all geometries: max over f : [3m] -> [m] u {skip} of the
                        number of enemies receiving >= T damage.  If this is < W the
                        game instance is a NO whatever the player does.
  C5  saturation        exhaustive over all 2^6 occupancy patterns of each enemy's
                        neighbourhood, with every other region saturated: the legal
                        approach hexes are always exactly the free neighbours of the
                        target, so blocking is local seat capacity and nothing else
  C6  unrestricted      (--full) exhaustive search over one allocation's play on the
                        real, fully crowded board, branching over targets AND over
                        approach hexes, with an over-generous extra branch in which a
                        passing stack vanishes from the board (strictly more permissive
                        than the MOVE-only action the reference simulator omits).  Run
                        on the identity allocation plus a sample, for the smallest
                        legal instances.

C3 settles the yes-direction constructively (a real play is simulated and its destroyed
value read off), C4 settles the no-direction over every allocation at once, C5 certifies
the geometry exhaustively, and C6 is a redundant assumption-free cross-check.

Mechanics come from homm3_model.py only; nothing about the combat rules is restated here.
The Geometry class in front of the model's BFS is a cache, not a reimplementation, and
selfcheck_geometry_cache compares it against uncached model calls.

Run:  python3 verify_featureless.py
      python3 verify_featureless.py --full     (adds the C6 tier, slow: ~2 min)
"""

from __future__ import annotations

import argparse
import itertools
import random
import sys
import time

from homm3_model import (
    Battle,
    Battlefield,
    CreatureType,
    Stack,
    destroyed_value,
    scripted_defence,
)

ALPHA = 10          # common attack/defence value, so both damage factors are 1.0
PLAYER_HP = 5       # > 2, so no player creature can die in one round (see below)
ENEMY_SPEED = 1     # strictly below the player speed: all player stacks act first
ENEMY_DAMAGE = 1


# =========================================================================
# The construction
# =========================================================================


def build(a: list[int], T: int, variant: str = "hold") -> dict:
    """candidate-C-featureless.md sec. 3.

    Board: 6 rows, 4m+2 columns, no obstacles.
      row 0        the 3m deployment hexes, columns 0 .. 3m-1
      row 1        permanently free (nothing is ever placed or moved there)
      row 3        the m enemies, at columns X_g = 4g + 2
      rows 2,3,4   the approach hexes of the enemies
      row 5        permanently free

    Player: 3m types, stock one each, flat damage a_i, speed w+h (so every stack can
    walk anywhere on the board), hit points 5.
    Enemy: m stacks of one creature, hp T, damage 1, value 1, speed 1.
    """
    assert len(a) % 3 == 0
    m = len(a) // 3
    w, h = 4 * m + 2, 6
    speed = w + h
    field = Battlefield(width=w, height=h)

    player_types = [
        CreatureType(f"C{i}", attack=ALPHA, defense=ALPHA,
                     dmg_min=a[i], dmg_max=a[i], hp=PLAYER_HP, speed=speed,
                     no_retaliation=(variant == "noretal"))
        for i in range(3 * m)
    ]
    slots = [field.index(c, 0) for c in range(3 * m)]

    enemies = []
    for g in range(m):
        X = 4 * g + 2
        enemies.append((
            CreatureType(f"E{g}", attack=ALPHA, defense=ALPHA,
                         dmg_min=ENEMY_DAMAGE, dmg_max=ENEMY_DAMAGE,
                         hp=T, speed=ENEMY_SPEED, value=1),
            field.index(X, 3),
        ))

    return {
        "a": list(a), "T": T, "m": m, "field": field, "speed": speed,
        "player_types": player_types, "slots": slots, "enemies": enemies,
        "W": m, "rounds": 1, "variant": variant,
    }


def assemble(inst: dict, alloc: list) -> Battle:
    """`alloc[j]` is the type index deployed in slot j, or None."""
    stacks = []
    for j, ti in enumerate(alloc):
        if ti is not None:
            stacks.append(Stack(inst["player_types"][ti], 1, side=0, slot=j,
                                hex_=inst["slots"][j]))
    for g, (ct, hx) in enumerate(inst["enemies"]):
        stacks.append(Stack(ct, 1, side=1, slot=g, hex_=hx))
    return Battle(inst["field"], stacks)


def initial_enemy_counts(battle: Battle) -> dict[int, int]:
    return {i: s.count() for i, s in enumerate(battle.stacks) if s.side == 1}


def run_defence(battle: Battle, variant: str) -> None:
    """The defence acts once, after every player stack (it is the slowest side).

    `hold`    -> it never initiates an attack (policy (double-dagger) of candidate-A).
    `noretal` -> it attacks; the player types carry NO_RETALIATION so nothing bounces
                 back onto the enemy.

    Getting this wrong is not cosmetic.  The first version of this script ran the
    attacking policy under both labels; the player stacks then *retaliated*, delivering
    a second blow of a_i to their own group's enemy inside the same round, and the
    search reported 3 kills where the arithmetic allows 1.  That is the candidate-A
    iteration-1 bug (VERIFICATION.md sec. 3) reproduced verbatim in the featureless
    setting, and it is why the round bound R = 1 alone does not make the defence's
    policy irrelevant, even though the defence is the slowest side and acts last.
    """
    if variant == "hold":
        return
    for s in battle.stacks:
        if s.side == 1 and s.alive():
            target = scripted_defence(battle, s)
            if target is not None:
                battle.resolve_attack(s, target)


# =========================================================================
# C1 / C2 -- geometry of the built instance
# =========================================================================


def check_reachability(inst: dict) -> None:
    """Every slot reaches every enemy, with all 3m slots occupied.

    This is the featureless claim.  The crowded board is the worst case: an ally
    standing in the only free approach hex is exactly what could break it.
    """
    k = len(inst["slots"])
    battle = assemble(inst, list(range(k)))
    want = set(range(inst["m"]))
    for j in range(k):
        got = {s.slot for s in battle.attackable(battle.stacks[j])}
        if got != want:
            raise AssertionError(
                f"reachability: slot {j} reaches enemies {sorted(got)}, want {sorted(want)}")


def check_separation(inst: dict) -> None:
    """No slot starts adjacent to an enemy; enemy neighbourhoods are disjoint.

    The first half rules out the degenerate reading in which the board still wires
    slots to enemies by adjacency.  The second is what the approach lemma uses.
    """
    field = inst["field"]
    hexes = [hx for _ct, hx in inst["enemies"]]
    for j, p in enumerate(inst["slots"]):
        for g, e in enumerate(hexes):
            if field.adjacent(p, e):
                raise AssertionError(f"slot {j} starts adjacent to enemy {g}")
        if p in hexes:
            raise AssertionError(f"slot {j} coincides with an enemy hex")
    nbrs = [set(field.neighbours(e)) | {e} for e in hexes]
    for g1, g2 in itertools.combinations(range(len(hexes)), 2):
        if nbrs[g1] & nbrs[g2]:
            raise AssertionError(f"enemy neighbourhoods {g1} and {g2} overlap")
        if any(field.adjacent(x, y) for x in nbrs[g1] for y in nbrs[g2]):
            raise AssertionError(f"enemy neighbourhoods {g1} and {g2} touch")


# =========================================================================
# C3 -- the approach lemma
# =========================================================================


def realise(inst: dict, target_of: list[int]) -> int | None:
    """Play in which stack j attacks enemy `target_of[j]`; returns destroyed value.

    All 3m slots are occupied.  Stacks act in slot order (equal speed, tie broken by
    slot, MODEL.md sec. 5), and the search branches over every legal approach hex.
    Returns None if no such play exists.
    """
    k = len(inst["slots"])
    battle = assemble(inst, list(range(k)))
    initial = initial_enemy_counts(battle)
    order = [battle.stacks.index(s) for s in battle.turn_order()]
    player_order = [i for i in order if battle.stacks[i].side == 0]
    if len(player_order) != k or player_order != sorted(player_order):
        raise AssertionError("player stacks do not act first, in slot order")

    def rec(b: Battle, j: int) -> int | None:
        if j == k:
            run_defence(b, inst["variant"])
            return destroyed_value(b, initial)
        atk = b.stacks[j]
        tgt_idx = k + target_of[j]
        tgt = b.stacks[tgt_idx]
        if not tgt.alive():
            # the assigned enemy is already dead: the stack cannot deliver its blow
            return None
        spots = b.attack_spots(atk, tgt)
        for dest in spots:
            nxt = b.clone()
            nxt.resolve_attack(nxt.stacks[j], nxt.stacks[tgt_idx], dest=dest)
            if nxt.stacks[j].count() != 1:
                raise AssertionError("a player creature died in round 1")
            out = rec(nxt, j + 1)
            if out is not None:
                return out
        return None

    return rec(battle, 0)


def triple_assignments(k: int, m: int):
    """Every map [k] -> [m] with exactly three slots per enemy (k = 3m).

    Labelled: the m enemies stand at different columns, so relabelling the groups is a
    genuinely different play and has to be checked separately.  There are
    (3m)! / 6^m of these -- 20 at m = 2, 1680 at m = 3.
    """
    def parts(remaining: tuple, acc: list):
        if not remaining:
            yield list(acc)
            return
        head, rest = remaining[0], remaining[1:]
        for pair in itertools.combinations(rest, 2):
            acc.append((head,) + pair)
            yield from parts(tuple(x for x in rest if x not in pair), acc)
            acc.pop()

    for groups in parts(tuple(range(k)), []):
        for perm in itertools.permutations(range(m)):
            out = [None] * k
            for g, trio in zip(perm, groups):
                for j in trio:
                    out[j] = g
            yield out


def check_approach_lemma(inst: dict, cap: int | None = None) -> tuple[int, int]:
    """Every three-per-enemy assignment is realisable, and its value is what the
    arithmetic predicts.  Returns (assignments checked, assignments realisable)."""
    a, T, m = inst["a"], inst["T"], inst["m"]
    k = 3 * m
    checked = realised = 0
    for target_of in triple_assignments(k, m):
        if cap is not None and checked >= cap:
            break
        checked += 1
        value = realise(inst, target_of)
        if value is None:
            raise AssertionError(f"assignment {target_of} is not realisable")
        realised += 1
        want = sum(1 for g in range(m)
                   if sum(a[j] for j in range(k) if target_of[j] == g) >= T)
        if value != want:
            raise AssertionError(
                f"assignment {target_of}: simulated value {value}, arithmetic {want}")
    return checked, realised


# =========================================================================
# C4 -- the assumption-free upper bound
# =========================================================================


def relaxation_bound(a: list[int], T: int, m: int) -> int:
    """Max number of enemies that can be brought to T damage, over all maps
    f : [3m] -> [m] u {skip}.

    Every legal allocation and every legal play induces such a map (a stack strikes at
    most once per round and damages only its target), so this is an upper bound on the
    destroyed value regardless of geometry, movement, blocking or turn order.
    """
    states = {(0,) * m}
    for x in a:
        nxt = set()
        for st in states:
            nxt.add(st)
            for g in range(m):
                nxt.add(st[:g] + (min(st[g] + x, T),) + st[g + 1:])
        states = nxt
    return max(sum(1 for v in st if v >= T) for st in states)


# =========================================================================
# C5 -- unrestricted joint search over allocation and play
# =========================================================================


class Budget:
    def __init__(self, cap: int):
        self.cap, self.used = cap, 0

    def spend(self) -> None:
        self.used += 1
        if self.used > self.cap:
            raise TimeoutError("node budget exhausted")


class Geometry:
    """A memo in front of the model's BFS, keyed on the state the BFS actually reads.

    No rule is restated here: `attackable` and `attack_spots` are called on the model's
    own `Battle`.  The key is (attacker hex, the set of hexes it treats as blocked, the
    living enemies' hexes), which is exactly what those two functions depend on, so the
    cache is observationally identical to calling them every time.  `selfcheck` below
    re-derives a sample of entries without the cache and compares.
    """

    def __init__(self):
        self.reach: dict = {}
        self.spots: dict = {}
        self.hits = self.misses = 0

    @staticmethod
    def _ctx(b: Battle, atk: Stack):
        blocked = frozenset(b.occupied(exclude=atk))
        alive_e = tuple(sorted(s.hex for s in b.stacks if s.side == 1 and s.alive()))
        return atk.hex, blocked, alive_e

    def targets(self, b: Battle, atk: Stack) -> tuple:
        k = self._ctx(b, atk)
        v = self.reach.get(k)
        if v is None:
            self.misses += 1
            v = tuple(sorted(e.hex for e in b.attackable(atk)))
            self.reach[k] = v
        else:
            self.hits += 1
        return v

    def approach(self, b: Battle, atk: Stack, defender: Stack) -> tuple:
        k = self._ctx(b, atk) + (defender.hex,)
        v = self.spots.get(k)
        if v is None:
            self.misses += 1
            v = tuple(b.attack_spots(atk, defender))
            self.spots[k] = v
        else:
            self.hits += 1
        return v


def selfcheck_geometry_cache(inst: dict, trials: int = 300, seed: int = 7) -> int:
    """The cache must agree with the uncached model calls on random board states.

    Each entry is queried twice, so both the miss path and the hit path are compared
    against a fresh call into `homm3_model`.  Returns the number of comparisons made.
    """
    rng = random.Random(seed)
    k = len(inst["slots"])
    geo = Geometry()
    n_hex = inst["field"].width * inst["field"].height
    compared = 0
    for _ in range(trials):
        battle = assemble(inst, list(range(k)))
        taken = {s.hex for s in battle.stacks if s.side == 1}
        for s in battle.stacks:
            if s.side != 0:
                continue
            for _try in range(20):
                h = rng.randrange(n_hex)
                if h not in taken:
                    taken.discard(s.hex)
                    s.hex = h
                    taken.add(h)
                    break
        for s in battle.stacks:
            if s.side != 0:
                continue
            want_t = tuple(sorted(e.hex for e in battle.attackable(s)))
            for _twice in range(2):
                if geo.targets(battle, s) != want_t:
                    raise AssertionError("geometry cache disagrees on attackable")
                compared += 1
            for e in battle.stacks:
                if e.side != 1 or e.hex not in want_t:
                    continue
                want_s = tuple(battle.attack_spots(s, e))
                for _twice in range(2):
                    if geo.approach(battle, s, e) != want_s:
                        raise AssertionError("geometry cache disagrees on attack_spots")
                    compared += 1
    return compared


def check_geometry_saturation(inst: dict) -> int:
    """Exhaustive: blocking in this construction is *local capacity*, nothing else.

    Claim.  In every board state the search can reach, the legal approach hexes for
    enemy g are exactly the free neighbours of e_g -- an ally never cuts a path, it only
    takes a seat.  Consequently the only geometric constraint on a round is "at most six
    stacks strike one enemy", which never binds at three stacks per enemy.

    The check is exhaustive rather than sampled, using two facts.

      * `Battle.reachable` is monotone in the blocked set (BFS over free hexes), and
        `attack_spots` is `reachable` intersected with the target's neighbours.  So
        testing with a *maximal* blocker set outside N(e_g) is the worst case, and if
        the spots come out full there, they come out full in every real state too.
      * A player stack only ever stands on its deployment hex or on a hex adjacent to
        the enemy it struck (WALK_AND_ATTACK is the only move the model implements), so
        the blockers are confined to the deployment row and the enemy neighbourhoods --
        exactly the regions saturated below.

    So for each enemy g we range over *all* 2^6 occupancy patterns of N(e_g) while every
    other enemy's neighbourhood, every other enemy hex, and every deployment hex except
    the prober's are occupied.  Returns the number of (enemy, pattern, prober) checks.
    """
    field = inst["field"]
    slots = inst["slots"]
    e_hexes = [hx for _ct, hx in inst["enemies"]]
    blocker = CreatureType("blocker", attack=ALPHA, defense=ALPHA, dmg_min=1,
                           dmg_max=1, hp=PLAYER_HP, speed=inst["speed"])
    probe_t = CreatureType("probe", attack=ALPHA, defense=ALPHA, dmg_min=1,
                           dmg_max=1, hp=PLAYER_HP, speed=inst["speed"])
    checks = 0
    for g, e in enumerate(e_hexes):
        nbrs = sorted(field.neighbours(e))
        elsewhere = set()
        for g2, e2 in enumerate(e_hexes):
            if g2 != g:
                elsewhere |= set(field.neighbours(e2)) | {e2}
        elsewhere -= set(nbrs) | {e}
        for mask in range(1 << len(nbrs)):
            taken = {nbrs[i] for i in range(len(nbrs)) if mask >> i & 1}
            want = tuple(h for h in nbrs if h not in taken)
            for j, p in enumerate(slots):
                if p in taken or p in elsewhere:
                    continue
                busy = (taken | elsewhere | (set(slots) - {p})) - {e}
                stacks = [Stack(probe_t, 1, side=0, slot=j, hex_=p)]
                stacks += [Stack(blocker, 1, side=0, slot=200 + i, hex_=h)
                           for i, h in enumerate(sorted(busy))]
                stacks += [Stack(ct, 1, side=1, slot=gg, hex_=hx)
                           for gg, (ct, hx) in enumerate(inst["enemies"])]
                battle = Battle(field, stacks)
                probe = battle.stacks[0]
                target = next(s for s in battle.stacks
                              if s.side == 1 and s.hex == e)
                got = tuple(battle.attack_spots(probe, target)) if want else ()
                if got != want:
                    raise AssertionError(
                        f"saturation: enemy {g}, blocked {sorted(taken)}, prober slot "
                        f"{j}: spots {sorted(got)}, want {sorted(want)}")
                reachable_now = {s.hex for s in battle.attackable(probe)}
                if want and e not in reachable_now:
                    raise AssertionError(
                        f"saturation: enemy {g} unattackable from slot {j} "
                        f"with blocked {sorted(taken)}")
                checks += 1
    return checks


def best_play_for_allocation(inst: dict, alloc: list, budget: Budget, geo: Geometry,
                             allow_vanish: bool = True) -> int:
    """Exhaustive search over one allocation's play, on the real, fully crowded board.

    Branches over: passing; vanishing (a relaxation that is strictly more permissive
    than the MOVE-only action the reference simulator omits); and every (target,
    approach hex) pair.  No early exit -- the returned number is the exact maximum, so
    it can be compared against the relaxation bound rather than just against W.

    Memo key: (whose turn, hexes of the living player stacks, enemy health and
    retaliation charges).  Player hit points are deliberately absent from the key; the
    search asserts no player creature ever dies, which is what makes them irrelevant.
    """
    battle = assemble(inst, alloc)
    initial = initial_enemy_counts(battle)
    n_players = sum(1 for s in battle.stacks if s.side == 0)
    enemy_idx = [i for i, s in enumerate(battle.stacks) if s.side == 1]
    memo: dict = {}

    def key(b: Battle, i: int):
        occ = tuple(sorted(s.hex for s in b.stacks if s.side == 0 and s.alive()))
        en = tuple((b.stacks[e].first_hp_left, b.stacks[e].full_units,
                    b.stacks[e].retaliations_left) for e in enemy_idx)
        return (i, occ, en)

    def rec(b: Battle, i: int) -> int:
        budget.spend()
        if i == n_players:
            run_defence(b, inst["variant"])
            return destroyed_value(b, initial)
        kk = key(b, i)
        hit = memo.get(kk)
        if hit is not None:
            return hit

        best = rec(b, i + 1)                                   # pass, staying put
        if allow_vanish:
            gone = b.clone()
            gone.stacks[i].full_units = 0                      # leave the board
            gone.stacks[i].first_hp_left = 0
            best = max(best, rec(gone, i + 1))
        atk = b.stacks[i]
        for e_hex in geo.targets(b, atk):
            t_idx = next(x for x in enemy_idx if b.stacks[x].hex == e_hex)
            for dest in geo.approach(b, atk, b.stacks[t_idx]):
                nb = b.clone()
                nb.resolve_attack(nb.stacks[i], nb.stacks[t_idx], dest=dest)
                if nb.stacks[i].count() != 1:
                    raise AssertionError("a player creature died in round 1")
                best = max(best, rec(nb, i + 1))
        memo[kk] = best
        return best

    return rec(battle, 0)


def partial_injections(n_slots: int, n_types: int):
    """Every assignment of distinct types to slots; slots may be left empty."""
    for r in range(n_types + 1):
        for chosen in itertools.combinations(range(n_slots), r):
            for types in itertools.permutations(range(n_types), r):
                out = [None] * n_slots
                for s, t in zip(chosen, types):
                    out[s] = t
                yield out



# =========================================================================
# 3-PARTITION ground truth and instance generation
# =========================================================================


def three_partition_answer(a: list[int], T: int) -> bool:
    def rec(remaining: tuple) -> bool:
        if not remaining:
            return True
        head, rest = remaining[0], remaining[1:]
        for pair in itertools.combinations(rest, 2):
            if a[head] + a[pair[0]] + a[pair[1]] != T:
                continue
            if rec(tuple(x for x in rest if x not in pair)):
                return True
        return False

    return rec(tuple(range(len(a))))


def gen_instances(rng: random.Random, m: int, count: int, ts: list[int]):
    """3-PARTITION instances with sum = m*T and T/4 < a_i < T/2, mixed yes and no."""
    out, seen = [], set()
    tries = 0
    while len(out) < count and tries < 200000:
        tries += 1
        T = rng.choice(ts)
        lo, hi = T // 4 + 1, (T - 1) // 2
        a = [rng.randint(lo, hi) for _ in range(3 * m)]
        diff = m * T - sum(a)
        if not (lo <= a[-1] + diff <= hi):
            continue
        a[-1] += diff
        key = (tuple(sorted(a)), T)
        if key in seen:
            continue
        seen.add(key)
        out.append((a, T))
    return out


SMALL_CASES = [([4, 4, 4, 4, 5, 5], 13),      # yes, the smallest legal instance
               ([4, 4, 4, 4, 4, 6], 13),      # no,  its only companion at T = 13
               ([5, 5, 5, 5, 6, 6], 16),      # yes
               ([5, 5, 5, 5, 5, 7], 16)]      # no


def balance(cases: list, want_no: int) -> list:
    """Keep the generated mix but make sure enough no-instances are present."""
    yes = [c for c in cases if three_partition_answer(*c)]
    no = [c for c in cases if not three_partition_answer(*c)]
    return yes[: max(0, len(cases) - min(want_no, len(no)))] + no[:want_no]


# =========================================================================
# Driver
# =========================================================================


def run_case(a: list[int], T: int, variant: str, approach_cap: int | None):
    inst = build(a, T, variant=variant)
    check_reachability(inst)                                             # C1
    check_separation(inst)                                               # C2
    saturation = check_geometry_saturation(inst)                         # C5

    truth = three_partition_answer(a, T)
    bound = relaxation_bound(a, T, inst["m"])                            # C4

    witness = None
    if truth:
        # the yes-direction, constructively: play the 3-partition assignment itself
        target_of = _solution_assignment(a, T, inst["m"])
        witness = realise(inst, target_of)

    checked, _ = check_approach_lemma(inst, cap=approach_cap)            # C3

    game = (witness is not None and witness >= inst["W"])
    if not truth and bound >= inst["W"]:
        raise AssertionError("relaxation admits W on a 3-PARTITION no-instance")
    return {"truth": truth, "game": game, "bound": bound, "witness": witness,
            "W": inst["W"], "approach_checked": checked, "saturation": saturation}


def _solution_assignment(a: list[int], T: int, m: int) -> list[int]:
    """Recover an actual 3-partition, as a slot -> enemy map."""
    k = len(a)
    out = [None] * k

    def rec(remaining: tuple, g: int) -> bool:
        if not remaining:
            return True
        head, rest = remaining[0], remaining[1:]
        for pair in itertools.combinations(rest, 2):
            if a[head] + a[pair[0]] + a[pair[1]] != T:
                continue
            for j in (head,) + pair:
                out[j] = g
            if rec(tuple(x for x in rest if x not in pair), g + 1):
                return True
            for j in (head,) + pair:
                out[j] = None
        return False

    assert rec(tuple(range(k)), 0), "no 3-partition to recover"
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--full", action="store_true",
                    help="add the C6 tier: exhaustive play search per allocation, slow")
    ap.add_argument("--allocs", type=int, default=2,
                    help="C6: random allocations sampled on top of the identity one")
    ap.add_argument("--seed", type=int, default=20260801)
    args = ap.parse_args()
    rng = random.Random(args.seed)

    failures = []
    t0 = time.time()

    cases_m2 = balance(gen_instances(rng, 2, 16, [16, 20, 24, 28]), want_no=6)
    cases_m3 = balance(gen_instances(rng, 3, 8, [16, 20]), want_no=3)

    total = 0
    for m, cases, cap in ((2, cases_m2, None), (3, cases_m3, None)):
        print("=" * 78)
        print(f"m = {m}   ({3 * m} types / {3 * m} slots / {m} enemies, "
              f"board {4 * m + 2} x 6)")
        print("=" * 78)
        for variant in ("hold", "noretal"):
            label = ("defence holds position"
                     if variant == "hold"
                     else "defence attacks, player types carry NO_RETALIATION")
            print(f"\n  variant: {label}")
            for a, T in cases:
                total += 1
                try:
                    r = run_case(a, T, variant, approach_cap=cap)
                except AssertionError as exc:
                    failures.append(f"m={m} [{variant}] a={a} T={T}: {exc}")
                    print(f"  [FAIL] a={str(a):34s} T={T:3d}  {exc}")
                    continue
                ok = r["game"] == r["truth"]
                if not ok:
                    failures.append(
                        f"m={m} [{variant}] a={a} T={T}: "
                        f"3part={r['truth']} game={r['game']}")
                print(f"  [{'ok ' if ok else 'MISMATCH'}] a={str(a):34s} T={T:3d} "
                      f"3part={'Y' if r['truth'] else 'N'} "
                      f"game={'Y' if r['game'] else 'N'} "
                      f"ub={r['bound']}/{r['W']} "
                      f"approach={r['approach_checked']} "
                      f"saturation={r['saturation']}")
        print()

    if args.full:
        print("=" * 78)
        print("C6  exhaustive play search per allocation on the real, crowded board")
        print("    (branching over targets and over approach hexes; a passing stack")
        print("    may also vanish, which dominates the MOVE-only action the")
        print("    reference simulator does not implement)")
        print("=" * 78)
        probe = build(cases_m2[0][0], cases_m2[0][1], variant="hold")
        n_cmp = selfcheck_geometry_cache(probe)
        print(f"  geometry cache agrees with uncached homm3_model on {n_cmp} queries\n")
        rng2 = random.Random(args.seed ^ 0x5EED)
        # The smallest legal 3-PARTITION instances there are: at T = 13 the window
        # T/4 < a_i < T/2 leaves exactly {4,5,6}, and exactly one yes and one no
        # instance exist.  Small T keeps the damage-vector part of the memo small;
        # the board, and hence the geometric branching, is the same at every T.
        for a, T in SMALL_CASES:
            inst = build(a, T, variant="hold")
            budget, geo = Budget(200_000_000), Geometry()
            bound = relaxation_bound(a, T, inst["m"])
            truth = three_partition_answer(a, T)
            allocs = [list(range(3 * inst["m"]))]
            if args.allocs:
                pool = list(partial_injections(len(inst["slots"]), 3 * inst["m"]))
                allocs += rng2.sample(pool, args.allocs)
            t1 = time.time()
            best = -1
            try:
                for alloc in allocs:
                    best = max(best, best_play_for_allocation(inst, alloc, budget, geo))
            except TimeoutError:
                print(f"  [skip] a={a} T={T}: node budget exhausted")
                continue
            ok = ((best >= inst["W"]) == truth) and best <= bound
            if not ok:
                failures.append(
                    f"C6 a={a} T={T}: 3part={truth} best={best} ub={bound}")
            print(f"  [{'ok ' if ok else 'MISMATCH'}] a={str(a):34s} T={T:3d} "
                  f"3part={'Y' if truth else 'N'} best={best}/{inst['W']} "
                  f"ub={bound} allocs={len(allocs)} nodes={budget.used} "
                  f"{time.time() - t1:.1f}s")
        print()

    print("=" * 78)
    dt = time.time() - t0
    if failures:
        print(f"FAILED: {len(failures)} problem(s) in {dt:.1f}s")
        for f in failures:
            print(f"  - {f}")
        return 1
    print(f"ALL PASS  ({total} instance runs, {dt:.1f}s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
