"""Brute-force verification of the candidate-A reductions.

For each construction we

  1. generate small instances of the source problem (PARTITION / 3-PARTITION),
  2. compute the source answer independently by exhaustive subset enumeration,
  3. build the game instance exactly as specified in ../proofs/candidate-A.md,
  4. machine-check the geometry lemma on the built instance,
  5. enumerate *every* feasible allocation and, for each, every player action
     sequence of the ATTACK-ONLY fragment (each stack passes or performs
     WALK_AND_ATTACK), simulating with the reference mechanics in homm3_model.py,
  6. compare "max destroyed value >= W" with the source answer.

Nothing about the reduction's combinatorics is assumed: the search branches over the
"pass" action, every reachable (target, approach hex) pair, and every allocation. It
does not assume that a slot only attacks its own enemy or that the optimum uses
exactly a_j creatures per slot. Player WAIT and MOVE-only actions are OUTSIDE the
searched fragment; they are discharged on paper (candidate-A.md sec. 2.1, paper
sec. 4.1), and the searcher must not be described as exhaustive over the full model.

The defence runs in three variants: `hold` (never acts), `noretal` (attacks, with
NO_RETALIATION players — the backup repair), and `waitdefend` — the paper's policy
(‡): every enemy issues WAIT at its NORMAL-phase activation and DEFEND at its
postponed WAIT-phase activation, with the +20 % (floor +1) bonus live in the damage
formula from that moment on. On these constructions `waitdefend` must agree with
`hold`, because every searched player action lands in the NORMAL phase, before any
postponed DEFEND; running it exercises that argument in the mechanics instead of
assuming it.

Run:  python3 brute_force.py            (default sizes)
      python3 brute_force.py --full     (adds the slow exhaustive tier)
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
    compute_damage,
    destroyed_value,
    kills_for_damage,
    scripted_defence,
)

ALPHA = 10          # common attack/defence value, so the damage factors are 1.0
PLAYER_HP = 5       # large enough that no player creature dies in one round
PLAYER_SPEED = 2
ENEMY_SPEED = 1

# =========================================================================
# Generic search over player play
# =========================================================================


def policy_hold(battle: Battle, stack: Stack, phase: str):
    """The defence never initiates an attack and takes no action at all.

    This is the corpus policy of the empirical section, kept as a search variant
    here; the paper's policy (‡) is `policy_wait_defend` below. It matters which
    one runs: if the defence attacks, the player's stack *retaliates*, which
    doubles the damage the player delivers to that enemy. See VERIFICATION.md,
    iteration 1.
    """
    return None


def policy_attack(battle: Battle, stack: Stack, phase: str):
    """The defence strikes an adjacent player stack (homm3_model.scripted_defence)."""
    return scripted_defence(battle, stack)


def policy_wait_defend(battle: Battle, stack: Stack, phase: str):
    """The paper's policy (‡): WAIT at the NORMAL-phase activation, DEFEND at the
    postponed WAIT-phase activation (candidate-A.md sec. 2.1)."""
    return "wait" if phase == "N" else "defend"


def max_destroyed_value(battle: Battle, rounds: int, policy=policy_hold) -> int:
    """Exhaustive search over the ATTACK-ONLY fragment of player plays.

    Each player stack, at its NORMAL-phase activation, either passes or performs
    WALK_AND_ATTACK, branching over every reachable (target, approach hex) pair;
    the defence plays `policy`. Player WAIT and MOVE-only actions are NOT
    searched — they are outside the fragment and are discharged on paper
    (candidate-A.md sec. 2.1, paper sec. 4.1). An earlier version of this
    docstring said "all player action sequences", which was wrong.

    The memo only merges identical simulator states. It does not remove any legal
    target or approach-hex action from the searched fragment.
    """
    initial = {i: s.count() for i, s in enumerate(battle.stacks) if s.side == 1}
    score_cap = sum(initial[i] * battle.stacks[i].ctype.value for i in initial)
    return _play(battle, None, 0, initial, rounds, policy, {}, score_cap)


def relaxed_upper_bound(battle: Battle, order, i: int, initial) -> int:
    """Upper-bound the value reachable by the unprocessed player stacks.

    For each future stack, remove all other player blockers and sum its maximum
    damage independently into every enemy it can reach. Reusing a stack across
    enemies makes this deliberately over-generous, so the result is safe for
    branch-and-bound and does not discard any legal action.
    """
    enemies = [(idx, stack) for idx, stack in enumerate(battle.stacks)
               if stack.side == 1]
    future_damage = {idx: 0 for idx, _ in enemies}
    for idx, _phase in order[i:]:
        attacker = battle.stacks[idx]
        if attacker.side != 0 or not attacker.alive():
            continue
        probe = attacker.clone()
        relaxed_enemies = [stack.clone() for _, stack in enemies]
        relaxed = Battle(battle.field, [probe] + relaxed_enemies)
        enemy_index = {id(stack): original_idx
                       for stack, (original_idx, _) in zip(relaxed_enemies, enemies)}
        for target in relaxed.attackable(probe):
            future_damage[enemy_index[id(target)]] += compute_damage(probe, target)

    upper = destroyed_value(battle, initial)
    for idx, enemy in enemies:
        upper += kills_for_damage(enemy, future_damage[idx]) * enemy.ctype.value
    return upper


def _play(battle: Battle, order, i: int, initial, rounds_left: int, policy,
          memo: dict, score_cap: int) -> int:
    if order is None:
        # NORMAL phase in initiative order; under the policy (‡) every enemy
        # waits, so its terminal DEFEND is scheduled in the WAIT phase, which
        # runs in *increasing* speed order (MODEL.md sec. 5). The searched
        # player actions all sit in the NORMAL phase: the attack-only fragment
        # contains no player WAIT.
        order = tuple((battle.stacks.index(s), "N") for s in battle.turn_order())
        if policy is policy_wait_defend:
            waiting = sorted((s for s in battle.living() if s.side == 1),
                             key=lambda s: (s.ctype.speed, s.side, s.slot))
            order += tuple((battle.stacks.index(s), "W") for s in waiting)
        i = 0

    # In the one-round cases used by both reductions, a player stack that has
    # already acted can affect only future movement as an occupied hex. Under
    # `hold` and `waitdefend`, its health is irrelevant after its action
    # because no enemy ever strikes it; under the backup `noretal` variant it
    # is also irrelevant because it cannot retaliate. This coarser exact key
    # merges destination permutations without merging states that can still
    # affect a later action. Multi-round searches retain all health fields
    # because those can matter in the next round.
    simplify_acted_players = rounds_left == 1 and (
        policy is policy_hold
        or policy is policy_wait_defend
        or all(s.ctype.no_retaliation for s in battle.stacks if s.side == 0))
    processed = {idx for idx, _ph in order[:i]}
    stack_state = []
    for idx, s in enumerate(battle.stacks):
        if simplify_acted_players and idx in processed and s.side == 0:
            stack_state.append((s.side, s.hex if s.alive() else None))
        else:
            stack_state.append((s.side, s.slot, s.hex, s.full_units,
                                s.first_hp_left, s.retaliations_left, s.acted,
                                s.defending, s.waited))
    state = (order, i, rounds_left, tuple(stack_state))
    if state in memo:
        return memo[state]

    if i == len(order):
        if rounds_left > 1:
            # Clone before end_round: mutating `battle` here would leak the
            # round transition into the caller's sibling branches.
            nxt = battle.clone()
            nxt.end_round()
            result = _play(nxt, None, 0, initial, rounds_left - 1, policy,
                           memo, score_cap)
        else:
            result = destroyed_value(battle, initial)
        memo[state] = result
        return result

    idx, phase = order[i]
    stack = battle.stacks[idx]
    if not stack.alive():
        result = _play(battle, order, i + 1, initial, rounds_left, policy,
                       memo, score_cap)
        memo[state] = result
        return result

    if stack.side == 1:
        act = policy(battle, stack, phase)
        if act is None and not stack.defending:
            # No action and no lingering bonus to expire: nothing mutates.
            result = _play(battle, order, i + 1, initial, rounds_left, policy,
                           memo, score_cap)
        else:
            # Clone before the enemy acts. The previous version mutated
            # `battle` in place here, which leaked the enemy's action into the
            # caller's sibling branches (the pass branch of the last player
            # entry runs before the attack branches clone the battle); see
            # test_regressions.py::test_enemy_branch_no_state_leak.
            nxt = battle.clone()
            st = nxt.stacks[idx]
            nxt.activate(st)          # STACK_GETS_TURN bonuses expire (R13)
            if act == "wait":
                nxt.act_wait(st)
            elif act == "defend":
                nxt.act_defend(st)
            elif act is not None:
                nxt.resolve_attack(st, nxt.stacks[battle.stacks.index(act)])
            result = _play(nxt, order, i + 1, initial, rounds_left, policy,
                           memo, score_cap)
        memo[state] = result
        return result

    # player stack: try passing and every legal (target, approach hex) action
    best = _play(battle, order, i + 1, initial, rounds_left, policy,
                 memo, score_cap)
    if best >= score_cap:
        memo[state] = best
        return best
    if rounds_left == 1 and relaxed_upper_bound(battle, order, i, initial) <= best:
        memo[state] = best
        return best
    for target in battle.attackable(stack):
        target_idx = battle.stacks.index(target)
        for dest in battle.attack_spots(stack, target):
            nxt = battle.clone()
            nxt.resolve_attack(nxt.stacks[idx], nxt.stacks[target_idx], dest=dest)
            best = max(best, _play(nxt, order, i + 1, initial, rounds_left,
                                   policy, memo, score_cap))
            if best >= score_cap:
                memo[state] = best
                return best
    memo[state] = best
    return best


# =========================================================================
# Construction 1 (Theorem 1): PARTITION
# =========================================================================


def build_partition_instance(a: list[int], player_no_retaliation: bool = False):
    """candidate-A.md sec. 3.1. Returns (field, enemy_specs, player_type, slots, B, W)."""
    n = len(a)
    total = sum(a)
    assert total % 2 == 0, "PARTITION instance must have even sum"
    B = total // 2

    field = Battlefield(width=5 * n, height=1)
    player = CreatureType("C", attack=ALPHA, defense=ALPHA, dmg_min=1, dmg_max=1,
                          hp=PLAYER_HP, speed=PLAYER_SPEED,
                          no_retaliation=player_no_retaliation)
    slots, enemies = [], []
    for j in range(n):
        slots.append(5 * j)                       # p_j
        enemies.append((
            CreatureType(f"E{j}", attack=ALPHA, defense=ALPHA, dmg_min=1, dmg_max=1,
                         hp=a[j], speed=ENEMY_SPEED, value=a[j]),
            5 * j + 1,                            # e_j
        ))
    return field, enemies, player, slots, B, B


def assemble(field, enemies, player_stacks):
    """player_stacks: list of (ctype, count, slot, hex)."""
    stacks = []
    for ctype, count, slot, hex_ in player_stacks:
        if count > 0:
            stacks.append(Stack(ctype, count, side=0, slot=slot, hex_=hex_))
    for slot, (ctype, hex_) in enumerate(enemies):
        stacks.append(Stack(ctype, 1, side=1, slot=slot, hex_=hex_))
    return Battle(field, stacks)


def check_geometry_partition(field, enemies, slots) -> None:
    """Machine-check candidate-A.md Lemma 3.1 on the built instance."""
    for j, p in enumerate(slots):
        probe = Battle(field, [Stack(
            CreatureType("probe", attack=ALPHA, defense=ALPHA, dmg_min=1, dmg_max=1,
                         hp=PLAYER_HP, speed=PLAYER_SPEED), 1, 0, j, p)]
            + [Stack(ct, 1, 1, s, h) for s, (ct, h) in enumerate(enemies)])
        reach = {st.slot for st in probe.attackable(probe.stacks[0])}
        if reach != {j}:
            raise AssertionError(
                f"Lemma 3.1 violated: slot {j} reaches enemies {sorted(reach)}, want {{{j}}}")


def allocations(n: int, budget: int):
    """All (c_1..c_n) in Z_{>=0}^n with sum <= budget."""
    if n == 0:
        yield ()
        return
    for first in range(budget + 1):
        for rest in allocations(n - 1, budget - first):
            yield (first,) + rest


def partition_answer(a: list[int]) -> bool:
    target = sum(a) // 2
    reachable = {0}
    for x in a:
        reachable |= {r + x for r in reachable}
    return target in reachable


POLICIES = {"hold": policy_hold, "noretal": policy_attack,
            "waitdefend": policy_wait_defend}

VARIANT_LABELS = {
    "hold": "defence holds position",
    "noretal": "defence attacks, player has NO_RETALIATION",
    "waitdefend": "defence waits, then defends -- the paper's policy (‡)",
}


def run_partition_case(a: list[int], rounds: int = 1,
                       variant: str = "hold") -> tuple[bool, bool, int]:
    """variant 'hold':       defence takes no action, player retaliates normally.
       variant 'noretal':    defence attacks, player creature has NO_RETALIATION.
       variant 'waitdefend': defence plays the paper's (‡): WAIT then DEFEND.
    All must reproduce PARTITION; see VERIFICATION.md iteration 2.
    """
    policy = POLICIES[variant]
    field, enemies, player, slots, B, W = build_partition_instance(
        a, player_no_retaliation=(variant == "noretal"))
    check_geometry_partition(field, enemies, slots)

    best = -1
    for c in allocations(len(a), B):
        battle = assemble(field, enemies,
                          [(player, c[j], j, slots[j]) for j in range(len(a))])
        best = max(best, max_destroyed_value(battle, rounds, policy))
    return best >= W, partition_answer(a), best


# =========================================================================
# Construction 2 (Theorem 2): 3-PARTITION
# =========================================================================


def build_3partition_instance(a: list[int], T: int, player_no_retaliation: bool = False):
    """candidate-A.md sec. 4.1, corrected to a 3-row 'flower' layout.

    In a single row an enemy hex has only two neighbours, so three player slots
    cannot all engage it. The flower puts the enemy at (X, 1) and its three
    deployment hexes at three of its six neighbours.
    """
    m = len(a) // 3
    field = Battlefield(width=8 * m + 2, height=3)

    player_types = [
        CreatureType(f"C{i}", attack=ALPHA, defense=ALPHA, dmg_min=a[i], dmg_max=a[i],
                     hp=PLAYER_HP, speed=PLAYER_SPEED,
                     no_retaliation=player_no_retaliation)
        for i in range(len(a))
    ]
    slots, enemies = [], []
    for g in range(m):
        X = 8 * g + 1
        e = field.index(X, 1)
        # three of the six neighbours of (X,1): LEFT, TOP_RIGHT, BOTTOM_RIGHT
        group = [field.index(X - 1, 1), field.index(X, 0), field.index(X, 2)]
        for h in group:
            assert field.adjacent(h, e), "flower hex is not adjacent to its enemy"
        slots.extend(group)
        enemies.append((
            CreatureType(f"E{g}", attack=ALPHA, defense=ALPHA, dmg_min=1, dmg_max=1,
                         hp=T, speed=ENEMY_SPEED, value=1),
            e,
        ))
    return field, enemies, player_types, slots, m


def check_geometry_3partition(field, enemies, slots) -> None:
    """Machine-check candidate-A.md Lemma 4.1 on the built instance.

    Checked in the worst case for the player: all slots occupied, so that a stack
    cannot walk through a hex held by an ally.
    """
    probe_type = CreatureType("probe", attack=ALPHA, defense=ALPHA, dmg_min=1, dmg_max=1,
                              hp=PLAYER_HP, speed=PLAYER_SPEED)
    players = [Stack(probe_type, 1, 0, s, h) for s, h in enumerate(slots)]
    enemy_stacks = [Stack(ct, 1, 1, g, h) for g, (ct, h) in enumerate(enemies)]
    battle = Battle(field, players + enemy_stacks)
    for s, _ in enumerate(slots):
        reach = {st.slot for st in battle.attackable(battle.stacks[s])}
        want = {s // 3}
        if reach != want:
            raise AssertionError(
                f"Lemma 4.1 violated: slot {s} reaches groups {sorted(reach)}, want {sorted(want)}")


def three_partition_answer(a: list[int], T: int) -> bool:
    """Ground truth by exhaustive search over partitions into triples."""
    idx = list(range(len(a)))

    def rec(remaining: tuple) -> bool:
        if not remaining:
            return True
        first, rest = remaining[0], remaining[1:]
        for pair in itertools.combinations(rest, 2):
            if a[first] + a[pair[0]] + a[pair[1]] != T:
                continue
            nxt = tuple(x for x in rest if x not in pair)
            if rec(nxt):
                return True
        return False

    return rec(tuple(idx))


def partial_injections(n_slots: int, n_types: int):
    """Every assignment of distinct types to slots, including leaving slots empty."""
    for k in range(n_types + 1):
        for chosen_slots in itertools.combinations(range(n_slots), k):
            for types in itertools.permutations(range(n_types), k):
                assign = [None] * n_slots
                for s, t in zip(chosen_slots, types):
                    assign[s] = t
                yield assign


def bijections(n_slots: int, n_types: int):
    """Only the assignments that deploy every type (n_slots == n_types)."""
    assert n_slots == n_types
    for types in itertools.permutations(range(n_types)):
        yield list(types)


def run_3partition_case(a: list[int], T: int, exhaustive: bool, rounds: int = 1,
                        variant: str = "hold"):
    policy = POLICIES[variant]
    field, enemies, player_types, slots, m = build_3partition_instance(
        a, T, player_no_retaliation=(variant == "noretal"))
    check_geometry_3partition(field, enemies, slots)

    gen = partial_injections(len(slots), len(a)) if exhaustive else bijections(len(slots), len(a))
    best = -1
    for assign in gen:
        ps = [(player_types[t], 1, s, slots[s])
              for s, t in enumerate(assign) if t is not None]
        battle = assemble(field, enemies, ps)
        best = max(best, max_destroyed_value(battle, rounds, policy))
        if best >= m:
            break                      # cannot do better than killing everything
    return best >= m, three_partition_answer(a, T), best


# =========================================================================
# Instance generation
# =========================================================================


def gen_partition_instances(rng: random.Random, n: int, count: int, hi: int):
    seen, out = set(), []
    while len(out) < count:
        a = sorted(rng.randint(1, hi) for _ in range(n))
        if sum(a) % 2 or tuple(a) in seen:
            continue
        seen.add(tuple(a))
        out.append(a)
    return out


def gen_3partition_instances(rng: random.Random, m: int, count: int):
    """Instances with sum = m*T and T/4 < a_i < T/2, a mix of yes and no."""
    out, seen = [], set()
    tries = 0
    while len(out) < count and tries < 20000:
        tries += 1
        T = rng.choice([20, 24, 28])
        lo, hi = T // 4 + 1, (T - 1) // 2
        a = [rng.randint(lo, hi) for _ in range(3 * m)]
        diff = m * T - sum(a)
        # nudge the last element into range if possible
        if not (lo <= a[-1] + diff <= hi):
            continue
        a[-1] += diff
        key = (tuple(sorted(a)), T)
        if key in seen:
            continue
        seen.add(key)
        out.append((a, T))
    return out


# =========================================================================
# Driver
# =========================================================================


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--full", action="store_true",
                    help="also run the exhaustive partial-injection tier for Theorem 2")
    ap.add_argument("--seed", type=int, default=20260801)
    args = ap.parse_args()
    rng = random.Random(args.seed)

    failures = []
    t0 = time.time()

    # ---- Theorem 1 -----------------------------------------------------
    print("=" * 72)
    print("Theorem 1  (PARTITION -> ARMY-ALLOCATION, single creature type)")
    print("=" * 72)

    hand = [[1, 1], [2, 2], [1, 3], [3, 5], [2, 4, 6], [1, 2, 3], [1, 1, 2, 4],
            [2, 3, 4, 5], [1, 5, 6, 8], [3, 3, 3, 3], [2, 2, 3, 7], [1, 2, 3, 6],
            [1, 4, 6, 9], [2, 5, 5, 8]]
    cases = [a for a in hand if sum(a) % 2 == 0]
    cases += gen_partition_instances(rng, 3, 6, 9)
    cases += gen_partition_instances(rng, 4, 8, 7)

    for variant in ("hold", "waitdefend", "noretal"):
        print(f"\n  variant: {VARIANT_LABELS[variant]}")
        yes_n = no_n = 0
        for a in cases:
            game, truth, best = run_partition_case(a, variant=variant)
            ok = game == truth
            yes_n += truth
            no_n += not truth
            status = "ok " if ok else "MISMATCH"
            print(f"  [{status}] a={str(a):22s} B={sum(a)//2:3d} "
                  f"partition={'Y' if truth else 'N'} game={'Y' if game else 'N'} "
                  f"best_value={best}")
            if not ok:
                failures.append(
                    f"Theorem 1 [{variant}], a={a}: partition={truth} game={game} best={best}")
        print(f"  -> {len(cases)} instances ({yes_n} yes, {no_n} no)")

    # ---- Theorem 2 -----------------------------------------------------
    print()
    print("=" * 72)
    print("Theorem 2  (3-PARTITION -> ARMY-ALLOCATION, strong hardness)")
    print("=" * 72)

    tri = gen_3partition_instances(rng, 2, 14)
    tri_yes = tri_no = 0
    for variant in ("hold", "waitdefend", "noretal"):
        print(f"\n  variant: {VARIANT_LABELS[variant]}")
        yes_n = no_n = 0
        for a, T in tri:
            game, truth, best = run_3partition_case(a, T, exhaustive=False, variant=variant)
            ok = game == truth
            yes_n += truth
            no_n += not truth
            status = "ok " if ok else "MISMATCH"
            print(f"  [{status}] a={str(a):26s} T={T:3d} "
                  f"3part={'Y' if truth else 'N'} game={'Y' if game else 'N'} "
                  f"kills={best}")
            if not ok:
                failures.append(
                    f"Theorem 2 [{variant}], a={a}, T={T}: 3part={truth} game={game} best={best}")
        print(f"  -> {len(tri)} instances ({yes_n} yes, {no_n} no), bijection tier")
        tri_yes, tri_no = yes_n, no_n   # identical across variants: the
        # 3-PARTITION truth does not depend on the defence variant

    if args.full:
        print()
        print("  exhaustive tier (all partial injections, slots may be left empty)")
        for a, T in tri[:4]:
            game, truth, best = run_3partition_case(a, T, exhaustive=True)
            ok = game == truth
            status = "ok " if ok else "MISMATCH"
            print(f"  [{status}] a={str(a):26s} T={T:3d} "
                  f"3part={'Y' if truth else 'N'} game={'Y' if game else 'N'}")
            if not ok:
                failures.append(f"Theorem 2 exhaustive, a={a}, T={T}")

    # ---- summary -------------------------------------------------------
    print()
    print("=" * 72)
    dt = time.time() - t0
    if failures:
        print(f"FAILED: {len(failures)} mismatch(es) in {dt:.1f}s")
        for f in failures:
            print(f"  - {f}")
        return 1
    # round 11 (thm2.6): the 3-PARTITION tier's scope — m = 2 only, and its
    # yes/no split — joins the pinned final line, so the disclosure the
    # sibling rows already make cannot be silently absent here
    print(f"ALL PASS  ({len(cases)} + {len(tri)} instances, 3-PARTITION "
          f"tier m = 2: {tri_yes} yes + {tri_no} no, {dt:.1f}s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
