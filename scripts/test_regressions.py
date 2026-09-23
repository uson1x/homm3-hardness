"""Small regressions for search state, movement, and retaliation bookkeeping.

Run:  python3 test_regressions.py
"""

from __future__ import annotations

from homm3_model import Battle, Battlefield, CreatureType, Stack, destroyed_value
from brute_force import max_destroyed_value, policy_attack, policy_wait_defend


FAILURES: list[str] = []
PASSED = 0


def check(label: str, got, want) -> None:
    global PASSED
    if got == want:
        PASSED += 1
    else:
        FAILURES.append(f"{label}: got {got!r}, want {want!r}")


def make(name: str, *, hp: int = 100, speed: int = 1, value: int = 0,
         no_retaliation: bool = False) -> CreatureType:
    return CreatureType(name, 10, 10, 1, 1, hp, speed, value=value,
                        no_retaliation=no_retaliation)


def destination_case() -> list[Stack]:
    """The smallest useful two-destination blocking gadget."""
    field = Battlefield(width=4, height=2)
    player = make("P", speed=1, no_retaliation=True)
    quiet = make("quiet", speed=0, no_retaliation=True)
    valuable = make("valuable", hp=2, speed=0, value=10, no_retaliation=True)
    return [
        Stack(player, 1, side=0, slot=0, hex_=1),
        Stack(player, 2, side=0, slot=1, hex_=0),
        Stack(quiet, 1, side=1, slot=0, hex_=5),
        Stack(valuable, 1, side=1, slot=1, hex_=2),
    ]


def canonical_value(battle: Battle) -> int:
    """The old canonical-destination search, kept only as a regression oracle."""
    initial = {i: s.count() for i, s in enumerate(battle.stacks) if s.side == 1}

    def rec(b: Battle, order, i: int) -> int:
        if order is None:
            order = [b.stacks.index(s) for s in b.turn_order()]
            i = 0
        if i == len(order):
            return destroyed_value(b, initial)
        idx = order[i]
        stack = b.stacks[idx]
        if not stack.alive() or stack.side == 1:
            return rec(b, order, i + 1)

        best = rec(b, order, i + 1)  # pass
        for target in b.attackable(stack):
            target_idx = b.stacks.index(target)
            nxt = b.clone()
            nxt.resolve_attack(nxt.stacks[idx], nxt.stacks[target_idx])
            best = max(best, rec(nxt, order, i + 1))
        return best

    return rec(battle, None, 0)


def test_exhaustive_destinations() -> None:
    """A non-canonical approach frees hex 1 for the ally at slot 1."""
    battle = Battle(Battlefield(width=4, height=2), destination_case())
    attacker, ally, target = battle.stacks[0], battle.stacks[1], battle.stacks[2]
    check("two legal approach hexes", battle.attack_spots(attacker, target), [1, 6])
    check("canonical approach", min(battle.attack_spots(attacker, target),
                                    key=lambda h: (battle.field.distance(h, attacker.hex), h)), 1)
    check("canonical search misses valuable kill", canonical_value(battle.clone()), 0)
    check("exhaustive search finds better destination", max_destroyed_value(battle, 1), 10)
    check("ally was initially blocked", battle.attack_spots(ally, battle.stacks[3]), [])


def test_moved_stack_frees_hex() -> None:
    """Moving the first stack off its slot opens the ally's only path."""
    battle = Battle(Battlefield(width=4, height=2), destination_case())
    attacker, ally, target, valuable = battle.stacks
    check("ally cannot reach before move", battle.attack_spots(ally, valuable), [])
    battle.resolve_attack(attacker, target, dest=6)
    check("moved stack leaves its deployment hex", attacker.hex, 6)
    check("ally can use the freed approach", battle.attack_spots(ally, valuable), [1])
    battle.resolve_attack(ally, valuable, dest=1)
    check("freed-hex attack kills target", valuable.count(), 0)


def test_iteration_one_retaliation() -> None:
    """The [1, 3] iteration-1 mismatch: the defence attack enables retaliation."""
    field = Battlefield(width=4, height=1)
    player = make("player", hp=100, speed=2)
    enemy = make("enemy", hp=3, speed=1, value=3)
    battle = Battle(field, [
        Stack(player, 2, side=0, slot=0, hex_=0),
        Stack(enemy, 1, side=1, slot=0, hex_=1),
    ])
    first = battle.resolve_attack(battle.stacks[0], battle.stacks[1])
    check("first attack deals two", first["damage"], 2)
    check("enemy survives first attack", battle.stacks[1].count(), 1)
    check("enemy retaliation happens", first["retaliation"], 1)
    check("enemy retaliation is consumed", battle.stacks[1].retaliations_left, 0)

    second = battle.resolve_attack(battle.stacks[1], battle.stacks[0])
    check("defence takes its normal turn", second["damage"], 1)
    check("player retaliation doubles the round's output", second["retaliation"], 2)
    check("player retaliation kills the enemy", battle.stacks[1].count(), 0)
    check("iteration-1 value is recovered", destroyed_value(battle, {1: 1}), 3)


def test_speed_widening_breaks_matching_reach() -> None:
    """§2.1's SIDE_COLUMN remark states — "checked against the executable
    model", says the paper — that the naive speed+2 widening breaks
    Theorem 1's matching-reach structure on the PARTITION instance (2, 4):
    at speed 4 the second slot reaches E1 as well as E2. Round 10 found no
    artifact pinned that sentence; this regression is the artifact."""
    def corridor(speed: int) -> Battle:
        p = CreatureType("P", attack=5, defense=5, dmg_min=1, dmg_max=1,
                         hp=5, speed=speed)
        es = [CreatureType(f"E{j}", attack=5, defense=5, dmg_min=1,
                           dmg_max=1, hp=t, speed=0, value=1)
              for j, t in enumerate((2, 4))]
        stacks = [Stack(p, 1, side=0, slot=0, hex_=0),
                  Stack(p, 1, side=0, slot=1, hex_=5),
                  Stack(es[0], 1, side=1, slot=0, hex_=1),
                  Stack(es[1], 1, side=1, slot=1, hex_=6)]
        return Battle(Battlefield(width=10, height=1), stacks)

    def reach_map(b: Battle) -> dict:
        out = {}
        for s in b.stacks:
            if s.side != 0:
                continue
            cells = set(b.reachable(s)) | {s.hex}
            out[s.slot] = {t.slot for t in b.stacks if t.side == 1
                           and any(abs(c - t.hex) == 1 for c in cells)}
        return out

    check("speed 2: reach is the perfect matching",
          reach_map(corridor(2)), {0: {0}, 1: {1}})
    check("speed 4: slot 2 reaches E1 too — the matching is gone",
          reach_map(corridor(4)), {0: {0}, 1: {0, 1}})


def render_hex_figure(grid: list[list[str]]) -> list[str]:
    """The ONE renderer for every hex figure this suite checks: 2-char glyph
    pitch inside a row, even rows indented one character (half a step)
    right — the engine's convention. Both the figure blocks below and the
    parity pin read THIS function's output, so a parity flip here fails the
    adjacency check instead of silently agreeing with flipped figures
    (round 10 caught the previous version keeping a second, unlinked copy
    of the parity formula)."""
    return [("" if y % 2 else " ") + " ".join(row)
            for y, row in enumerate(grid)]


def test_adapter_figures_match_code() -> None:
    """The paper's hex figures must still be the code's coordinates.

    Three layers, each closing a hole a review round found:
    (a) Appendix C's four adapter figures must appear in BOTH papers as
        contiguous, ordered blocks — round 10 showed per-line membership
        let a reversed or wholesale-swapped figure pass;
    (b) the renderer's parity is pinned THROUGH its own output: glyph
        columns are read back out of the rendered strings and compared to
        Battlefield adjacency, so the strings the papers show and the
        convention being checked cannot diverge (round 9 had both sides
        share one wrong assumption; round 10 found the fix kept a second
        unlinked copy of it);
    (c) the candidate-D gadget schematic and the §3.3 local picture —
        outside every previous guard — are parsed and their half-step
        offsets verified.
    """
    from pathlib import Path

    from verify_x3c import ADAPTERS

    dockings = {(4, 3): "U", (5, 4): "R", (4, 5): "D"}
    root = Path(__file__).resolve().parent.parent
    paper = (root / "paper" / "main.md").read_text()
    tex = (root / "paper" / "main.tex").read_text()

    # (a) contiguous blocks in both papers, each ANCHORED to its own
    # caption and in the declared order. Round 11 (P11-5) showed the bare
    # `block in paper` membership let two whole figures swap places while
    # their captions stayed put — the docstring's "ordered" was prose.
    missing = {"TRB": "LEFT", "TBL": "RIGHT", "TRL": "BOTTOM", "RBL": "TOP"}
    check("adapter keys are exactly the four dockings of Lemma D.3",
          sorted(ADAPTERS), sorted(missing))
    for doc, text, cap_fmt in (
            ("Appendix C", paper, "Missing `{}`"),
            ("main.tex", tex, "Missing \\texttt{{{}}}")):
        prev_end = -1
        for name, arms in ADAPTERS.items():
            grid = [["#"] * 9 for _ in range(9)]
            for path in arms.values():
                for (x, y) in path:
                    grid[y][x] = "."
            for (x, y), label in dockings.items():
                grid[y][x] = label
            grid[4][4] = "Z"
            block = "\n".join(render_hex_figure(grid))
            cap = cap_fmt.format(missing[name])
            ci = text.find(cap)
            check(f"adapter {name}: caption '{cap}' present in {doc}",
                  ci >= 0, True)
            if ci < 0:
                continue
            bi = text.find(block, ci)
            check(f"adapter {name}: figure block directly follows its "
                  f"caption in {doc}", 0 <= bi - ci <= 700, True)
            check(f"adapter {name}: caption+block in declared order in "
                  f"{doc}", ci > prev_end, True)
            prev_end = bi

    # (b) the parity pin, derived from the rendered strings themselves: on
    # a uniform 9×9 frame, read each cell's character column back out of
    # render_hex_figure's output and demand that two cells are drawn
    # touching (same row, glyph columns one pitch apart; adjacent rows,
    # glyph columns half a pitch apart) exactly when Battlefield adjacency
    # says they are neighbours. No second parity formula exists here.
    bf = Battlefield(9, 9)
    frame = render_hex_figure([["."] * 9 for _ in range(9)])
    cols = [[i for i, ch in enumerate(line) if ch != " "] for line in frame]
    mismatches = []
    for y1 in range(9):
        for x1 in range(9):
            neigh = set(bf.neighbours(x1 + y1 * 9))
            for y2 in range(9):
                for x2 in range(9):
                    if (y1, x1) >= (y2, x2):
                        continue
                    c1, c2 = cols[y1][x1], cols[y2][x2]
                    drawn = (y1 == y2 and abs(c1 - c2) == 2) or (
                        abs(y1 - y2) == 1 and abs(c1 - c2) == 1)
                    if drawn != (x2 + y2 * 9 in neigh):
                        mismatches.append(((x1, y1), (x2, y2), drawn))
    check("rendered-string adjacency == Battlefield adjacency (9×9 frame)",
          mismatches, [])

    # (c1) the candidate-D gadget schematic: z sits on an even row Y, so
    # the row-Y±1 glyphs sit half a step LEFT — d¹/d³ one character left
    # of z, the impassable '#' one character left of d²; the row-Y '#'
    # (the third impassable neighbour, (X−1, Y)) is left of z
    cand = (root / "proofs" / "candidate-D-singletype.md").read_text()
    lines = cand.splitlines()
    idx = next((i for i, ln in enumerate(lines)
                if ln.strip().startswith("row Y−1")), None)
    check("candidate-D gadget schematic found", idx is not None, True)
    if idx is not None:
        top, mid, bot = lines[idx], lines[idx + 1], lines[idx + 2]
        ok = ("z" in mid and "d²" in mid and "d¹" in top and "d³" in bot
              and "#" in top and "#" in bot and "#" in mid)
        check("candidate-D gadget schematic has all six glyphs", ok, True)
        if ok:
            z, d2 = mid.index("z"), mid.index("d²")
            check("candidate-D schematic: d¹ half a step left of z",
                  top.index("d¹"), z - 1)
            check("candidate-D schematic: d³ half a step left of z",
                  bot.index("d³"), z - 1)
            check("candidate-D schematic: top # half a step left of d²",
                  top.index("#"), d2 - 1)
            check("candidate-D schematic: bottom # half a step left of d²",
                  bot.index("#"), d2 - 1)
            check("candidate-D schematic: row-Y # left of z",
                  mid.index("#") < z, True)

    # (c2) the §3.3 local picture, in both papers: five contiguous lines
    # around "# Z R", with the even rows (Z's row and the two outermost)
    # indented exactly one character right of the odd rows (U's and D's)
    for label, text in (("main.md", paper), ("main.tex", tex)):
        plines = text.splitlines()
        zi = next((i for i, ln in enumerate(plines) if "# Z R" in ln), None)
        check(f"§3.3 local picture found in {label}", zi is not None, True)
        if zi is None:
            continue
        block = plines[zi - 2:zi + 3]
        ind = [len(ln) - len(ln.lstrip(" ")) for ln in block]
        check(f"§3.3 picture in {label}: U row present", "U" in block[1],
              True)
        check(f"§3.3 picture in {label}: D row present", "D" in block[3],
              True)
        check(f"§3.3 picture in {label}: even rows half a step right",
              (ind[0], ind[2], ind[4]) ==
              (ind[1] + 1, ind[1] + 1, ind[3] + 1), True)
        # round 11 (P11-5): indentation alone let the glyphs drift inside
        # their rows — pin every glyph's column against Z's, engine
        # convention (2-char pitch in a row, half a step across rows)
        zc = block[2].index("Z")
        check(f"§3.3 picture in {label}: # one pitch left of Z",
              block[2].index("#"), zc - 2)
        check(f"§3.3 picture in {label}: R one pitch right of Z",
              block[2].index("R"), zc + 2)
        check(f"§3.3 picture in {label}: corridor dots continue R's row",
              block[2][zc + 4] + block[2][zc + 6], "..")
        for gi, glyph in ((1, "U"), (3, "D")):
            gc = block[gi].index(glyph)
            check(f"§3.3 picture in {label}: {glyph} half a step left of Z",
                  gc, zc - 1)
            check(f"§3.3 picture in {label}: walls one pitch around {glyph}",
                  (block[gi].index("#"), block[gi].rindex("#")),
                  (gc - 2, gc + 2))
        for gi, where in ((0, "above"), (4, "below")):
            check(f"§3.3 picture in {label}: corridor dot {where} in Z's "
                  f"column", block[gi].index("."), zc)
            check(f"§3.3 picture in {label}: walls one pitch around the "
                  f"{where} dot", (block[gi].index("#"), block[gi].rindex("#")),
                  (zc - 2, zc + 2))


def leaky_enemy_value(battle: Battle) -> int:
    """Replica of the pre-fix enemy branch, kept only as a regression oracle.

    The old `_play` executed the scripted defence's action by mutating the
    shared battle object in place. The pass branch of a player entry runs
    before its attack branches clone the battle, so an enemy action taken
    inside the pass branch leaked into every attack branch — and the enemy
    entry then acted a second time inside them.
    """
    initial = {i: s.count() for i, s in enumerate(battle.stacks) if s.side == 1}

    def rec(b: Battle, order, i: int) -> int:
        if order is None:
            order = [b.stacks.index(s) for s in b.turn_order()]
            i = 0
        if i == len(order):
            return destroyed_value(b, initial)
        stack = b.stacks[order[i]]
        if not stack.alive():
            return rec(b, order, i + 1)
        if stack.side == 1:
            target = policy_attack(b, stack, "N")
            if target is not None:
                b.resolve_attack(stack, target)          # the leak: in place
            return rec(b, order, i + 1)
        best = rec(b, order, i + 1)                      # pass branch first
        for target in b.attackable(stack):
            t_idx = b.stacks.index(target)
            for dest in b.attack_spots(stack, target):
                nxt = b.clone()
                nxt.resolve_attack(nxt.stacks[order[i]], nxt.stacks[t_idx], dest=dest)
                best = max(best, rec(nxt, order, i + 1))
        return best

    return rec(battle, None, 0)


def enemy_leak_case() -> Battle:
    """One fragile player creature that must strike before the enemy does."""
    field = Battlefield(width=3, height=1)
    glass = CreatureType("glass", 10, 10, 5, 5, hp=1, speed=2)
    prey = CreatureType("prey", 10, 10, 1, 1, hp=5, speed=1, value=1)
    return Battle(field, [
        Stack(glass, 1, side=0, slot=0, hex_=0),
        Stack(prey, 1, side=1, slot=0, hex_=1),
    ])


def test_enemy_branch_no_state_leak() -> None:
    """An enemy action must not leak across sibling search branches.

    The player (speed 2) legally strikes first and kills the enemy for value 1.
    In the leaky searcher, the pass branch lets the enemy kill the fragile
    player stack on the shared battle object, so the attack branches inherit a
    dead attacker and the search reports 0.
    """
    check("leaky searcher loses the kill", leaky_enemy_value(enemy_leak_case()), 0)
    check("fixed searcher finds the kill",
          max_destroyed_value(enemy_leak_case(), 1, policy_attack), 1)


def test_wait_defend_lands_after_normal_blows() -> None:
    """The Dragon Fly mechanism of the companion note (formerly paper sec. 5.1),
    as a search-level check.

    Enemy speed 13 against player speed 6: an enemy that DEFENDs at its
    NORMAL-phase activation (the paper's old policy) raises its defence from 10
    to 12 before the player's blow, and floor(5*4*0.95) = 19 misses the
    20-hit-point kill. Under (‡) = WAIT-then-DEFEND the same blow lands in the
    NORMAL phase, before the postponed DEFEND, and kills. This is the pair of
    behaviours that made six recorded optima unattainable under the old policy
    and attainable under the new one.
    """
    def build() -> Battle:
        field = Battlefield(width=3, height=1)
        striker = CreatureType("striker", 10, 10, 4, 4, hp=100, speed=6)
        fly = CreatureType("fly", 10, 10, 1, 1, hp=20, speed=13, value=1)
        return Battle(field, [
            Stack(striker, 5, side=0, slot=0, hex_=0),
            Stack(fly, 1, side=1, slot=0, hex_=1),
        ])

    def policy_immediate_defend(battle, stack, phase):
        return "defend"

    check("immediate DEFEND denies the kill",
          max_destroyed_value(build(), 1, policy_immediate_defend), 0)
    check("WAIT-then-DEFEND admits the kill",
          max_destroyed_value(build(), 1, policy_wait_defend), 1)


def test_waiting_player_strikes_defended_target() -> None:
    """Round-8 codex leg: in the `(‡)` search runs no blow ever lands on a
    defending target — the searched player never waits, and every non-waiting
    blow precedes the postponed DEFENDs (paper sec. 2.4/4.1; instrumenting the
    damage calls shows zero such calls). The capped branch therefore needs its
    own witness. Walk the phase order by hand with a player that DOES wait,
    under the published Theorem 3 constants (att 1 vs def 27): undefended,
    Delta = 26 and floor(12 * 0.35) = 4; defended, def 32, Delta = 31,
    0.025 * 31 = 0.775 crosses the cap and clamps to 0.7, so the same blow
    deals floor(12 * 0.3) = 3. Flag, clamp, and contrast are all asserted.
    """
    def build() -> Battle:
        field = Battlefield(width=3, height=1)
        p = CreatureType("p", 1, 10, 1, 1, 100, 6)     # att 1, flat damage 1
        e = CreatureType("e", 10, 27, 1, 1, 100, 3)    # def 27, slower
        return Battle(field, [
            Stack(p, 12, side=0, slot=0, hex_=0),
            Stack(e, 1, side=1, slot=0, hex_=1),
        ])

    # contrast: the same blow at the player's NORMAL activation, target not
    # defending -- the case every searched (‡) blow is in
    b = build()
    player, enemy = b.stacks
    before = enemy.available()
    b.activate(player)
    b.resolve_attack(player, enemy, dest=player.hex)
    check("undefended blow at def 27: floor(12*0.35)",
          before - enemy.available(), 4)

    # the capped branch: both wait; WAIT phase runs in increasing speed, so
    # the slower enemy DEFENDs first and the waiting player strikes def 32
    b = build()
    player, enemy = b.stacks
    b.activate(player)
    b.act_wait(player)                  # NORMAL phase: speed 6 activates first
    b.activate(enemy)
    b.act_wait(enemy)                   # (‡) first half
    b.activate(enemy)
    b.act_defend(enemy)                 # (‡) second half, WAIT phase, speed 3
    check("the postponed DEFEND is live on the target", enemy.defending, True)
    before = enemy.available()
    b.activate(player)
    b.resolve_attack(player, enemy, dest=player.hex)
    check("blow on the defending target clamps at the cap: floor(12*0.3)",
          before - enemy.available(), 3)


def test_docs_match_artifacts() -> None:
    """Round-8 structural fix, extended by the round-8 codex leg.

    Rounds 6, 7 and 8 each caught the same failure shape: a fix landed where
    the reviewer pointed and nowhere else ("65 checks" vs 90, "43 cases" vs 49,
    `μ=2` vs `μ=6` in one file, shipped-game transfer claims). The battery
    makes the drift a suite failure instead of a review finding, in four
    layers: (a) the paper's verification tables are RENDERED from
    verification_manifest.json and re-checked here; (b) the manifest's
    counters are recomputed by RUNNING the artifacts that generate them and
    parsing each suite's own final line (the engine verdicts are re-derived
    offline from the shipped results file — the C++ harness itself is not
    rebuilt here — and the EIGHT `--full`-tier Theorem-3 counters are the
    one exception, pinned only by layer (c): x3c_full_vacate_{built,yes,no,
    skipped} and crosscheck_full_{built,yes,no,skipped}; round 10 (B6)
    found the previous wording said "six", undercounted, and left the
    default tiers unpinned too — the default tiers of both suites are now
    run right here); (c) every prose citation of a counter that has ever
    drifted is swept against the manifest, in the sibling documents AND in
    the paper body; (d) retired claims stay banned by regex, and the ban
    count itself is a manifest counter. Round 9 (fable F2) proved layer
    (b)'s previous wording was an overclaim by falsifying a counter under
    a green battery; this block is the repair, and `--fast` skips only the
    six slow subprocess pins.
    """
    import json
    import re
    import subprocess
    import sys as _sys
    from pathlib import Path

    root = Path(__file__).resolve().parent.parent
    man = json.loads((root / "verification_manifest.json").read_text())
    cnt = man["counters"]

    # (a) the README's suite table is exactly the manifest's render (round
    # 15: the table left the paper; Section 4.4 points at README.md)
    gen = subprocess.run(
        [_sys.executable, str(root / "scripts" / "gen_verification_table.py")],
        capture_output=True, text=True)
    check("the README verification table matches the manifest render "
          "(gen_verification_table.py check mode)", gen.returncode, 0)
    # round 10 (fable): deleting a manifest row used to drop a suite from
    # both rendered tables with a green battery — the row list is now pinned
    check("manifest rows: the expected suites, in order",
          [r["id"] for r in man["rows"]],
          ["verify_mechanics", "brute_force", "test_obstacles",
           "dp_single_type", "verify_featureless", "verify_featureless_full",
           "verify_x3c_default",
           "verify_x3c_vacate", "verify_x3c_defend", "verify_x3c_full_vacate",
           "crosscheck_full", "crosscheck_defend", "search_free_order",
           "verify_embedding", "check_stub",
           "verify_hp_objective", "verify_full_model_optima",
           "certify_scores", "check_defend_policy",
           "exact_arithmetic_crosscheck", "test_regressions",
           "engine_harness"])

    # round 11 (P11-1/2): a guard's sentence about its own coverage is a
    # claim like any other — the only way to check it is to drill the
    # mutation. Both round-11 demonstrated mutations are rebuilt in memory
    # on every run, and each must FAIL the validator: (1) a counter
    # retyped as a digit the row already declared in `literals` (the
    # digit audit alone let it through); (2) two placeholders swapped
    # inside one row (set equality does not see order).
    import copy

    import gen_verification_table as gvt

    def drilled(mutate) -> bool:
        bad = copy.deepcopy(man)
        mutate(bad)
        try:
            gvt.validate_placeholders(bad)
        except SystemExit:
            return True
        return False

    def retype(bad):
        for row in bad["rows"]:
            if row["id"] == "verify_x3c_default":
                row["md"] = [c.replace("{x3c_default_built}", "3")
                             for c in row["md"]]

    def swap(bad):
        for row in bad["rows"]:
            if row["id"] == "verify_embedding":
                row["md"] = [
                    c.replace("{lemma_built}", "\0")
                    .replace("{lemma_nonplanar}", "{lemma_built}")
                    .replace("\0", "{lemma_nonplanar}")
                    for c in row["md"]]

    check("mutation drill: counter retyped as a declared literal is caught",
          drilled(retype), True)
    check("mutation drill: placeholder swap inside a row is caught",
          drilled(swap), True)

    # round 12 (P12-7): two more escaping mutations, demonstrated live by
    # the panel, drilled the same way. (3) a counter moved across a CELL
    # boundary — the flat sequence was blind to it and (while the table had
    # two renders) the renders put the number in different table columns;
    # since round 15 the per-cell placement is held to the manifest's own
    # `cells` declaration instead of to a second render; (4) deleting one
    # occurrence of a digit that appears twice — set equality was blind to
    # multiplicity.
    def cellmove(bad):
        for row in bad["rows"]:
            if row["id"] == "verify_embedding":
                md = row["md"]
                # sep_pairs opens cell 2; moving it to the END of cell 1
                # leaves the FLAT sequence unchanged — only the per-cell
                # audit can see it
                md[2] = md[2].replace("{sep_pairs} ", "", 1)
                md[1] = md[1] + " {sep_pairs}"

    def dupdigit(bad):
        for row in bad["rows"]:
            if row["id"] == "verify_embedding":
                # round 13: the minima became counters, so the duplicate
                # digit deleted here is one of the four `4`s of that row
                row["md"] = [c.replace("(4|C| boxes", "(|C| boxes")
                             for c in row["md"]]

    def drilled_literals(mutate) -> bool:
        bad = copy.deepcopy(man)
        mutate(bad)
        try:
            gvt.validate_literals(bad)
        except SystemExit:
            return True
        return False

    check("mutation drill: counter moved across a cell boundary is caught",
          drilled(cellmove), True)
    check("mutation drill: deleted duplicate digit-run is caught",
          drilled_literals(dupdigit), True)

    # round 13 (fable F-05, codex Check 05): two more escaping mutations,
    # demonstrated live by the panel. (5) the (SEP') class minima swapped
    # 12/16/20 -> 20/16/12 — a multiset of literals does not see order, so
    # the minima are now counters and the swap is a placeholder-sequence
    # change; (6) a sign: `def 41` -> `def -41` — unsigned digit-runs did
    # not see it. Round 13 also drilled two tex-only mutations (a deleted
    # digit-run, a 27 <-> 41 swap in the LaTeX render only); round 15
    # retired the LaTeX render with the table's place in the paper, and
    # those two drills with it — there is one render now.
    def minswap(bad):
        for row in bad["rows"]:
            if row["id"] == "verify_embedding":
                row["md"] = [c.replace("{sep_min_bb}", "\0")
                             .replace("{sep_min_cc}", "{sep_min_bb}")
                             .replace("\0", "{sep_min_cc}")
                             for c in row["md"]]

    def sign(bad):
        for row in bad["rows"]:
            if row["id"] == "verify_x3c_default":
                row["md"] = [c.replace("def 41", "def -41")
                             for c in row["md"]]

    check("mutation drill: (SEP') class minima reordered is caught",
          drilled(minswap), True)
    check("mutation drill: a sign in front of a literal is caught",
          drilled_literals(sign), True)

    # (b) manifest counters against their generating artifacts
    engine_doc = json.loads(
        (root / "engine-check" / "engine_results.json").read_text())
    results = engine_doc["results"]
    check("manifest engine_cases == len(engine_results.json)",
          len(results), cnt["engine_cases"])
    # round 10 (M7): the ULP story of Section 4.2 is now pinned to the
    # shipped engine header — the cap the harness read back from VCMI's
    # JSON parser must be the double one ULP ABOVE 0.7, not 0.7 itself
    cap = engine_doc["engine"]["defense_point_damage_factor_cap"]
    check("engine-reported defence cap is one ULP above 0.7",
          (cap == 0.7000000000000001, cap != 0.7), (True, True))
    # the exact/explained split is re-derived offline: compare.py's own
    # predict() and diff() against the shipped engine outputs, no binary
    _sys.path.insert(0, str(root / "engine-check"))
    import compare as _ec
    if not _ec.CASES:
        _ec.build_cases()
    by_id = {res["id"]: res for res in results}
    exact = explained = mismatched = 0
    explained_deltas: dict[str, list[str]] = {}
    for case in _ec.CASES:
        actual = by_id.get(case["id"])
        if actual is None:
            mismatched += 1
            continue
        problems = _ec.diff(_ec.predict(case), actual)
        if problems and case.get("known_issue"):
            explained += 1
            explained_deltas[case["id"]] = problems
        elif problems:
            mismatched += 1
        else:
            exact += 1
    check("engine verdicts re-derived offline: (exact, explained, mismatched)",
          (exact, explained, mismatched),
          (cnt["engine_exact"], cnt["engine_explained"], 0))
    # round 11 (P11-3): "explained" used to accept ANY corruption inside a
    # known-issue case — the count was pinned, the content was not
    # (kills→12345 stayed green). PANEL-10 §5 item 6 promised these pins;
    # here they are: each explained case must show EXACTLY the one-point
    # damage drop the ULP story of Section 4.2 predicts, field by field.
    KNOWN_DELTAS = {
        "S-defense-38": ["damage_min: model=30, engine=29",
                         "damage_max: model=30, engine=29"],
        "S-defense-200": ["damage_min: model=30, engine=29",
                          "damage_max: model=30, engine=29"],
        "S-floor-3": ["damage_min: model=3, engine=2",
                      "damage_max: model=3, engine=2"],
    }
    check("known-issue deltas: exactly the pinned cases, exactly the pinned "
          "field-level diffs", explained_deltas, KNOWN_DELTAS)
    # the corresponding drill: corrupt one explained case in memory and
    # demand the pin above would have gone red
    corrupt = dict(by_id["S-floor-3"])
    corrupt["damage_min"] = 12345
    drill_problems = _ec.diff(
        _ec.predict(next(c for c in _ec.CASES if c["id"] == "S-floor-3")),
        corrupt)
    check("mutation drill: corrupted known-issue delta no longer matches "
          "its pin", drill_problems != KNOWN_DELTAS["S-floor-3"], True)
    check("engine-check/REPORT.md cites the manifest case count",
          f"{cnt['engine_cases']} кейс"
          in (root / "engine-check" / "REPORT.md").read_text(), True)

    out = subprocess.run(
        [_sys.executable, str(root / "scripts" / "verify_mechanics.py")],
        capture_output=True, text=True)
    m = re.search(r"all (\d+) checks passed", out.stdout)
    check("verify_mechanics.py reports a count", m is not None, True)
    if m:
        check("manifest mechanics_checks == the count the suite reports",
              int(m.group(1)), cnt["mechanics_checks"])

    # the Lemma D.4 embedding suite is cheap enough to run whole: its final
    # line carries every counter the manifest quotes for it
    emb = subprocess.run(
        [_sys.executable, str(root / "scripts" / "verify_embedding.py")],
        capture_output=True, text=True)
    check("verify_embedding.py passes", emb.returncode, 0)
    m = re.search(r"\((\d+) boards, (\d+) certified non-planar, (\d+) "
                  r"certified degenerate-no of which (\d+) also non-planar, "
                  r"(\d+) malformed certificates, "
                  r"1 planted non-planar control, G_no played as a genuine "
                  r"no, real \(SEP'\) on (\d+) pairs, end-to-end game "
                  r"on (\d+) board\(s\) under historical and published "
                  r"constants", emb.stdout)
    check("manifest lemma counters == what verify_embedding.py reports",
          tuple(int(g) for g in m.groups()) if m else None,
          (cnt["lemma_built"], cnt["lemma_nonplanar"],
           cnt["lemma_degenerate_no"], cnt["lemma_degenerate_nonplanar"],
           cnt["lemma_malformed"], cnt["sep_pairs"], cnt["lemma_endtoend"]))
    # round 11 (P11-4): the (SEP') class statistics are pinned — a starved
    # feature export can no longer leave the separation check vacuous
    m = re.search(r"exercised on (\d+) non-incident feature pairs: class "
                  r"minima L∞ = (\d+)/(\d+)/(\d+)", emb.stdout)
    check("(SEP') pair count and class minima == the pinned values",
          tuple(int(g) for g in m.groups()) if m else None,
          (cnt["sep_pairs"], cnt["sep_min_bb"], cnt["sep_min_bc"],
           cnt["sep_min_cc"]))
    check("(SEP') required separation == the paper's λ - 2ρ",
          cnt["sep_required"], 20 - 2 * 4)
    # round 16 (Opus F8): step 5 of Lemma D.4 said "nothing else on the board
    # is within distance 12 of the stub (SEP')" — false, (SEP') covers only
    # non-incident features and the incident corridors come within L∞ 5. The
    # corrected sentence (every free hex within λ−2ρ of the stub lies in R_e)
    # is checked on every corpus board and both numbers are pinned here.
    m = re.search(r"deployment stubs: (\d+) free hexes within L∞ < (\d+) of a "
                  r"stub, every one in its own element's region; nearest free "
                  r"hex outside the own vertex box at L∞ (\d+)", emb.stdout)
    check("stub margin: count, required margin and corpus minimum == manifest",
          tuple(int(g) for g in m.groups()) if m else None,
          (cnt["stub_near_hexes"], cnt["sep_required"], cnt["stub_margin_min"]))
    check("stub margin: the retired 'nothing within 12' sentence is refuted "
          "by the measured minimum",
          cnt["stub_margin_min"] < cnt["sep_required"], True)

    # round 13 (codex Check 10): the G_no payload is played AS ENCODED —
    # a corrupted encoding (slot off the board, its hex impassable, the
    # slot missing, ownership gone) must be rejected, not replaced by a
    # substitute battle inside the checker
    import copy as _copy

    import embed_lemma as _B
    import verify_embedding as _VE
    _, gno = _B.build_board_lemma(3, [(0, 1)])
    check("G_no payload plays out as a no", _VE.g_no_is_a_no(gno), [])
    for field, value in (("deploy", {0: 999}), ("obstacles", frozenset({0})),
                         ("deploy", {}), ("owner", {})):
        bad_gno = _copy.deepcopy(gno)
        bad_gno["instance"][field] = value
        check(f"mutation drill: corrupted G_no ({field}) is rejected",
              bool(_VE.g_no_is_a_no(bad_gno)), True)
    m = re.search(r"\((\d+) distinct families\)", emb.stdout)
    check("manifest lemma_families == the corpus size the suite reports",
          int(m.group(1)) if m else None, cnt["lemma_families"])

    # round 9 (fable F2 / harness §3): the counters below used to be merely
    # WRITTEN in the manifest — a falsified value flowed into both papers
    # with a green battery. Now each is pinned by running its artifact and
    # parsing the artifact's own final line. --fast skips the three slow
    # suites; a full (default) run pins everything in this block.
    fast = "--fast" in _sys.argv

    obs = subprocess.run(
        [_sys.executable, str(root / "scripts" / "test_obstacles.py")],
        capture_output=True, text=True)
    m = re.search(r"OK: all (\d+) checks passed", obs.stdout)
    check("manifest obstacle_checks == test_obstacles.py's own count",
          int(m.group(1)) if m else None, cnt["obstacle_checks"])

    hp = subprocess.run(
        [_sys.executable, str(root / "scripts" / "verify_hp_objective.py")],
        capture_output=True, text=True)
    m = re.search(r"ALL PASS: (\d+) instances \((\d+) yes / (\d+) no\)",
                  hp.stdout)
    check("manifest hp_objective counters == verify_hp_objective.py's",
          tuple(int(g) for g in m.groups()) if m else None,
          (cnt["hp_objective_instances"], cnt["hp_objective_yes"],
           cnt["hp_objective_no"]))

    dp_ = subprocess.run(
        [_sys.executable, str(root / "scripts" / "dp_single_type.py")],
        capture_output=True, text=True)
    m = re.search(r"OK: dp == brute on (\d+) random instances", dp_.stdout)
    check("manifest dp_random_instances == dp_single_type.py's loop bound",
          int(m.group(1)) if m else None, cnt["dp_random_instances"])
    # round 10 (B1): the suite gained a tier that PLAYS the built corridors
    # and a negative control where the knapsack abstraction must disagree
    # with the game — pin both, so the tier cannot be quietly dropped
    m = re.search(r"OK: dp == game on (\d+) single-creature corridor "
                  r"instances", dp_.stdout)
    check("manifest dp_game_instances == dp_single_type.py's game tier",
          int(m.group(1)) if m else None, cnt["dp_game_instances"])
    check("dp_single_type.py's multi-creature negative control fires",
          "OK: negative control (multi-creature stacks): dp 0 != game 3"
          in dp_.stdout, True)

    # round 11 (P11-6, promised by PANEL-10 §5 item 8): the ability
    # projection shifts the certified OPTIMUM on the paper's own example —
    # restoring the Efreet's hateGenies moves naturalS-k6-02 from 1136 to
    # 2020, with the projected value re-certified before and after
    shift = subprocess.run(
        [_sys.executable,
         str(root / "empirics" / "scripts" / "check_ability_shift.py")],
        capture_output=True, text=True)
    check("check_ability_shift.py passes", shift.returncode, 0)
    check("ability shift on naturalS-k6-02 is the pinned 1136 -> 2020 (56%)",
          "OK: ability shift on naturalS-k6-02: certified optimum 1136 "
          "under the projection, 2020 with hateGenies restored — the "
          "projected optimum is 56% of the ability-aware one"
          in shift.stdout, True)

    if not fast:
        feat = subprocess.run(
            [_sys.executable, str(root / "scripts" / "verify_featureless.py")],
            capture_output=True, text=True)
        m = re.search(r"ALL PASS\s+\((\d+) instance runs", feat.stdout)
        check("manifest featureless_runs == verify_featureless.py's count",
              int(m.group(1)) if m else None, cnt["featureless_runs"])
        # round 16 (Opus F5): the exhaustive play tier C6 is a DEFAULT tier
        # now — the only tier of this suite that searches plays of a
        # no-instance — and its scale is the suite's own final line; the
        # --full extension is pinned in-process (test_round16_apparatus)
        m = re.search(r"C6 on (\d+) instances x (\d+) allocations", feat.stdout)
        check("manifest C6 default scale == verify_featureless.py's own line",
              tuple(int(g) for g in m.groups()) if m else None,
              (cnt["featureless_c6_instances"], cnt["featureless_c6_allocs"]))
        check("C6 ran on both smallest cases and passed",
              feat.stdout.count("best=") == cnt["featureless_c6_instances"]
              and "MISMATCH" not in feat.stdout and feat.returncode == 0, True)

        bfo = subprocess.run(
            [_sys.executable, str(root / "scripts" / "brute_force.py")],
            capture_output=True, text=True)
        m = re.search(r"ALL PASS\s+\((\d+) \+ (\d+) instances, 3-PARTITION "
                      r"tier m = 2: (\d+) yes \+ (\d+) no", bfo.stdout)
        check("manifest brute_force counters == brute_force.py's counts "
              "(incl. the m = 2 tier's yes/no split, round 11 thm2.6)",
              tuple(int(g) for g in m.groups()) if m else None,
              (cnt["brute_force_base"], cnt["brute_force_sharp"],
               cnt["brute_force_tri_yes"], cnt["brute_force_tri_no"]))

        leg = subprocess.run(
            [_sys.executable,
             str(root / "empirics" / "scripts" / "check_defend_policy.py"),
             "--legacy-defend"],
            capture_output=True, text=True)
        m = re.search(r"\((\d+) violations\), plus exactly (\d+) more",
                      leg.stdout)
        check("manifest legacy counters == the negative control's own count",
              (int(m.group(1)), int(m.group(1)) + int(m.group(2)))
              if m else None,
              (cnt["legacy_round5_violations"], cnt["legacy_mismatches"]))

        # round 10 (B6): the DEFAULT tiers of both Theorem-3 suites join the
        # battery — verify_x3c.py (~20 s) and crosscheck_sol.py (~2.5 min).
        # crosscheck_default_instances was previously pinned by NOTHING;
        # only the two --full tiers remain excepted (layer (c) sweeps them).
        x3c = subprocess.run(
            [_sys.executable, str(root / "scripts" / "verify_x3c.py")],
            capture_output=True, text=True)
        check("verify_x3c.py (default tier) passes", x3c.returncode, 0)
        m = re.search(r"instances built (\d+), skipped by the router (\d+), "
                      r"X3C yes (\d+) / no (\d+)", x3c.stdout)
        check("manifest x3c default counters == verify_x3c.py's own line",
              tuple(int(g) for g in m.groups()) if m else None,
              (cnt["x3c_default_built"], 0,
               cnt["x3c_default_yes"], cnt["x3c_default_no"]))

        ccs = subprocess.run(
            [_sys.executable, str(root / "scripts" / "crosscheck_sol.py")],
            capture_output=True, text=True)
        check("crosscheck_sol.py (default tier) passes", ccs.returncode, 0)
        m = re.search(r"built (\d+), skipped (\d+), yes (\d+) / no (\d+)",
                      ccs.stdout)
        check("manifest crosscheck default counters == the suite's own line",
              tuple(int(g) for g in m.groups()) if m else None,
              (cnt["crosscheck_default_instances"], 0,
               cnt["crosscheck_default_yes"], cnt["crosscheck_default_no"]))

        # round 12 (backlog 19a): the free-order enlargement as a permanent
        # suite -- the default tier's final line is the pin, like the others.
        sfo = subprocess.run(
            [_sys.executable, str(root / "scripts" / "search_free_order.py")],
            capture_output=True, text=True)
        check("search_free_order.py (default tier) passes", sfo.returncode, 0)
        m = re.search(r"free-order: (\d+) built, (\d+) yes / (\d+) no, "
                      r"(\d+) skipped, one corpus x both constant sets, "
                      r"every allocation, (\d+) discriminating controls, "
                      r"negative control flips (\d+) no-instance, corpus "
                      r"trace (\d+)/(\d+)/(\d+) reorder/vanish/multi-spot",
                      sfo.stdout)
        # round 13 (fable F-04/F-13, codex Check 04): the controls certify
        # that each branch exists on a fixture; the corpus TRACE certifies
        # that it acted on the corpus — reorder and vanish must be live,
        # and the measured "no state ever offered a second approach hex"
        # is pinned as the number it is
        check("manifest free-order counters == the suite's own line",
              tuple(int(g) for g in m.groups()) if m else None,
              (cnt["free_order_built"], cnt["free_order_yes"],
               cnt["free_order_no"], 0, cnt["free_order_controls"],
               cnt["free_order_flips"], cnt["free_order_reorder"],
               cnt["free_order_vanish"], cnt["free_order_multispot"]))
        check("free-order corpus trace: reorder and vanish are live",
              (cnt["free_order_reorder"] > 0, cnt["free_order_vanish"] > 0),
              (True, True))

        # merge of the burn-session line (2026-09-10): step 5 of Lemma D.4
        # now claims the deployment stub has EXACTLY ONE free neighbour and
        # points at check_stub.py (64 local configurations, adjacency from
        # the model's own neighbour rule). The clean-room line shipped the
        # script without a battery pin; here the count is the manifest's
        # and both paper renders must quote it.
        stub = subprocess.run(
            [_sys.executable, str(root / "scripts" / "check_stub.py")],
            capture_output=True, text=True)
        check("check_stub.py (deployment-stub clause) passes",
              stub.returncode, 0)
        m = re.search(r"deployment-stub clause: (\d+) \(port set, u, parity\) "
                      r"cases, (\d+) failures", stub.stdout)
        check("manifest stub_cases == check_stub.py's own line",
              tuple(int(g) for g in m.groups()) if m else None,
              (cnt["stub_cases"], 0))
        stub_phrase = f"{cnt['stub_cases']} cases, 0 failures"
        for name in ("main.md", "main.tex"):
            flat = re.sub(r"\s+", " ",
                          (root / "paper" / name).read_text())
            check(f"{name} quotes the stub case count",
                  stub_phrase in flat, True)

        # round 14 (gpt-6-astra pro F2): the empirical optima are defined by
        # the float simulator, the theorems by exact rationals, and the two
        # split on some calls. exact_arithmetic_crosscheck.py (out of the
        # battery: it re-runs the 84 s scoring suite twice) measured the
        # agreement on this corpus; its recorded final line is pinned here,
        # and its cheap half — every recorded optimum replayed under (‡)
        # with the EXACT routine installed — is re-run in-process (~10 s).
        import exact_damage as E
        import homm3_model as M
        _sys.path.insert(0, str(root / "empirics" / "scripts"))
        import solve as _solve
        import instance as _inst
        import check_defend_policy as _cdp
        xlog = (root / "empirics" / "results"
                / "exact_arithmetic_crosscheck.log").read_text()
        m = re.search(r"exact-arithmetic cross-check: (\d+) damage calls, (\d+) "
                      r"with a fractional factor, (\d+) call-level float/exact "
                      r"splits, 0 certified numbers moved; suites under floats "
                      r"pass, under exact rationals pass", xlog)
        check("manifest exact-arithmetic counters == the recorded final line "
              "of exact_arithmetic_crosscheck.py (0 certified numbers moved)",
              tuple(int(g) for g in m.groups()) if m else None,
              (cnt["exact_calls"], cnt["exact_fractional"],
               cnt["exact_splits"]))
        check("exact_arithmetic_crosscheck.py's recorded run ends in ALL PASS",
              "ALL PASS" in xlog.strip().splitlines()[-1], True)
        saved = (M.compute_damage, _solve.compute_damage)
        M.compute_damage = E.exact_compute_damage
        _solve.compute_damage = E.exact_compute_damage
        try:
            optima_x = json.loads(
                (root / "empirics" / "instances" / "optima.json").read_text())
            replayed = mism = 0
            for path in sorted((root / "empirics" / "instances").glob("*.json")):
                if path.name in ("optima.json", "index.json"):
                    continue
                inst = _inst.load(path)
                rec = optima_x[inst["id"]]
                alloc = _inst.normalise_allocation(inst, rec["allocation"])
                best = _cdp.best_under_policy(inst, alloc, legacy=False)
                replayed += 1
                mism += best != rec["optimum"]
        finally:
            M.compute_damage, _solve.compute_damage = saved
        check("every recorded optimum is reproduced by the (‡) replay under "
              "EXACT rational arithmetic (in-process, exact routine installed)",
              (replayed, mism), (cnt["empirical_instances"], 0))
        check("the exact routine is uninstalled after the replay",
              M.compute_damage.__name__, "compute_damage")

    # the empirical counters are the lengths of shipped artifacts, and the
    # turn-order count is the T-* subset of the engine case list itself
    optima_rec = json.loads(
        (root / "empirics" / "instances" / "optima.json").read_text())
    check("manifest empirical_instances == len(instances/optima.json)",
          len(optima_rec), cnt["empirical_instances"])
    n_resp = sum(1 for line in (root / "empirics" / "responses_final.jsonl")
                 .read_text().splitlines() if line.strip())
    check("manifest scored_responses == len(responses_final.jsonl)",
          n_resp, cnt["scored_responses"])
    check("manifest engine_turn_order_cases == the T-* cases in cases.json",
          sum(1 for case in _ec.CASES if str(case["id"]).startswith("T-")),
          cnt["engine_turn_order_cases"])
    # round 16 (Opus F10): the R-* cases are 11 damage / kill-threshold blows
    # and ONE retaliation blow — §4.1 used to file all 12 under retaliation
    r_cases = [case for case in _ec.CASES if str(case["id"]).startswith("R-")]
    check("manifest engine_reduction_cases == the R-* cases in cases.json",
          len(r_cases), cnt["engine_reduction_cases"])
    check("exactly one reduction-drawn engine case is a retaliation blow",
          sum(1 for case in r_cases if "retaliation" in str(case["id"])), 1)

    # round 9 (DeepSeek API): the observation-2 statistics — the Spearman
    # pair, the k-bucket table and the natural-family sequence — now have a
    # generating artifact (stats_recheck.py, from results/llm.json), and the
    # quoting document must quote its output verbatim. Round 15: the
    # quoting document is the empirical companion note; the paper's Section
    # 5 moved there verbatim (paper/companion-empirics.md, Markdown only —
    # a LaTeX mirror of the note is backlog, so the former main.tex pins
    # have no target and are gone, not silently kept vacuous).
    st = subprocess.run(
        [_sys.executable,
         str(root / "empirics" / "scripts" / "stats_recheck.py")],
        capture_output=True, text=True)
    check("stats_recheck.py runs", st.returncode, 0)
    paper_md = (root / "paper" / "main.md").read_text()
    paper_tex = (root / "paper" / "main.tex").read_text()
    note_md = (root / "paper" / "companion-empirics.md").read_text()
    m = re.search(r"Spearman\(k, ratio\) all = (-\d+\.\d+); "
                  r"natural = (-\d+\.\d+)", st.stdout)
    check("stats_recheck.py reports both Spearman coefficients",
          m is not None, True)
    if m:
        sp_all, sp_nat = m.group(1), m.group(2)
        check("companion note quotes the recomputed Spearman pair",
              f"Spearman `{sp_all}`, and `{sp_nat}`" in note_md, True)

    for line in st.stdout.splitlines():
        if line.startswith("| `claude-") and "%" not in line:
            check(f"companion note k-bucket row matches llm.json "
                  f"({line[2:24]}…)", line in note_md, True)
        # round 10: the headline rows, the baseline rows and the
        # observation-3 percentage points are generated now too
        if (line.startswith("| `claude-") and "%" in line) or \
                line.startswith("| greedy-") or \
                line.startswith("| 100-sample"):
            check(f"companion note headline/baseline row matches the "
                  f"artifacts ({line[2:26]}…)", line in note_md, True)
        if line.startswith("geometry-removal cost: "):
            phrase = "cost " + line.split(": ", 1)[1]
            check("companion note quotes the geometry-removal percentage "
                  "points", phrase in note_md, True)
        if line.startswith("natural-family haiku sequence: "):
            seq = line.split(": ", 1)[1]
            check("companion note quotes the natural-family haiku sequence",
                  seq in note_md, True)
    # round 15: the paper itself must NOT carry the study's numbers any more
    # — the one sentence it keeps (Section 1.2) names the instance count only
    for label, text in (("main.md", paper_md), ("main.tex", paper_tex)):
        check(f"{label} no longer prints the ratio table or the Spearman "
              f"pair (moved to the companion note)",
              ("claude-haiku-4-5" in text, "Spearman" in text), (False, False))

    # round 10 (M2): the ability-projection numbers are pinned to the
    # committed audit artifact (the audit itself needs a VCMI checkout, so
    # the battery pins the note to the shipped JSON, not the JSON to VCMI)
    ab = json.loads(
        (root / "empirics" / "results" / "ability_projection.json")
        .read_text())
    for name, n in {**ab["tally_melee"], **ab["tally_extended"]}.items():
        m = re.search(rf"`{name}` on\s+(\d+)", note_md)
        check(f"companion note quotes the {name} slot count",
              int(m.group(1)) if m else None, n)
    for label, text in (("companion-empirics.md", note_md),):
        m = re.search(r"(\d+) of the (\d+) natural instances name at least",
                      text)
        check(f"{label} quotes the melee-scope affected count",
              tuple(int(g) for g in m.groups()) if m else None,
              (ab["affected_instances_melee"], ab["natural_instances"]))
        m = re.search(r"raises that to (\d+)", text)
        check(f"{label} quotes the extended-scope affected count",
              int(m.group(1)) if m else None,
              ab["affected_instances_melee_or_extended"])
        m = re.search(r"all (\d+) are affected", text)
        check(f"{label} quotes the any-ability affected count",
              int(m.group(1)) if m else None,
              ab["affected_instances_any_ability"])
        m = re.search(r"alone marks (\d+) type-slots", text)
        check(f"{label} quotes the FLYING slot count",
              int(m.group(1)) if m else None, ab["tally_any_ability"]["FLYING"])
        m = re.search(r"HATE`?\}? (\d+)", text)
        check(f"{label} quotes the HATE slot count",
              int(m.group(1)) if m else None, ab["tally_any_ability"]["HATE"])

    # (c) prose sweep: every spot where a counter has ever drifted (rounds
    # 5-8 findings), tied back to the manifest. A missing match fails too —
    # if the sentence is rewritten, rewrite the pattern with it.
    sweep = [
        ("proofs/candidate-D-singletype.md",
         r"\| `verify_x3c\.py` \| (\d+) \| (\d+) / (\d+) \| (\d+) \|",
         (cnt["x3c_default_built"], cnt["x3c_default_yes"],
          cnt["x3c_default_no"], 0)),
        ("proofs/candidate-D-singletype.md",
         r"\| `verify_x3c\.py --full --vacate` \| (\d+) \| (\d+) / (\d+) \| (\d+) \|",
         (cnt["x3c_full_vacate_built"], cnt["x3c_full_vacate_yes"],
          cnt["x3c_full_vacate_no"], cnt["x3c_full_vacate_skipped"])),
        ("proofs/candidate-D-singletype.md",
         r"\| `crosscheck_sol\.py --full` \| (\d+) \| (\d+) / (\d+) \| (\d+) \|",
         (cnt["crosscheck_full_built"], cnt["crosscheck_full_yes"],
          cnt["crosscheck_full_no"], cnt["crosscheck_full_skipped"])),
        ("proofs/candidate-D-singletype.md",
         r"exercised on (\d+) \(default\) and (\d+) \(`--full`\)",
         (cnt["x3c_default_built"], cnt["x3c_full_vacate_built"])),
        ("proofs/candidate-D-singletype.md",
         r"\*\*(\d+) instances \((\d+) yes, (\d+) no\), all agreeing",
         (cnt["crosscheck_full_built"], cnt["crosscheck_full_yes"],
          cnt["crosscheck_full_no"])),
        ("proofs/candidate-C-featureless.md",
         r"(\d+) cases, (\d+) exact",
         (cnt["engine_cases"], cnt["engine_exact"])),
        ("VERIFICATION.md", r"(\d+) проверок механики",
         (cnt["mechanics_checks"],)),
        ("STATE.md", r"verify_mechanics\.py (\d+) проверок",
         (cnt["mechanics_checks"],)),
        ("ASSESSMENT.md", r"(\d+) проверок механики",
         (cnt["mechanics_checks"],)),
        # round 9: the paper body joins the sweep — the recipe's hard-coded
        # comments and the §1.2 instance count previously had no guard at all;
        # round 15: the full recipe moved to README.md, the paper keeps a
        # four-line summary and the §1.2 instance count
        ("README.md", r"# (\d+) checks: damage formula",
         (cnt["mechanics_checks"],)),
        ("README.md", r"# (\d+) checks on geometry and blocking",
         (cnt["obstacle_checks"],)),
        ("README.md", r"stub clause, (\d+) cases", (cnt["stub_cases"],)),
        ("paper/main.md", r"language\s+models on (\d+) instances",
         (cnt["empirical_instances"],)),
        ("paper/main.tex", r"language\s+models on (\d+) instances",
         (cnt["empirical_instances"],)),
        # round 15: the suite table left the paper, so the paper's prose is
        # the only place it prints the engine and arithmetic counts — pinned
        # here in both renders (the tex wraps lines, hence \s+)
        ("paper/main.md", r"engine numbers: (\d+) checks",
         (cnt["mechanics_checks"],)),
        ("paper/main.tex", r"engine numbers:\s+(\d+) checks",
         (cnt["mechanics_checks"],)),
        ("paper/main.md",
         r"(\d+) cases, (\d+) exact agreements, the other (\d+) explained",
         (cnt["engine_cases"], cnt["engine_exact"], cnt["engine_explained"])),
        ("paper/main.tex",
         r"(\d+) cases, (\d+)\s+exact agreements, the other (\d+) explained",
         (cnt["engine_cases"], cnt["engine_exact"], cnt["engine_explained"])),
        ("paper/main.md", r"(\d+) of the (\d+) engine cases",
         (cnt["engine_explained"], cnt["engine_cases"])),
        ("paper/main.tex", r"(\d+) of the (\d+) engine cases",
         (cnt["engine_explained"], cnt["engine_cases"])),
        ("paper/main.md", r"(\d+) of (\d+) damage calls",
         (cnt["exact_splits"], cnt["exact_calls"])),
        ("paper/main.tex", r"(\d+) of\s+(\d+) damage calls",
         (cnt["exact_splits"], cnt["exact_calls"])),
        # and the companion note's own headline counts
        ("paper/companion-empirics.md",
         r"(\d+) instances of `ARMY-ALLOCATION`", (cnt["empirical_instances"],)),
        ("paper/companion-empirics.md", r"(\d+) model responses scored",
         (cnt["scored_responses"],)),
        ("paper/companion-empirics.md", r"The full matrix is (\d+) cells",
         (cnt["scored_responses"],)),
        ("paper/companion-empirics.md", r"certifies all (\d+) per-response",
         (cnt["scored_responses"],)),
        # round 10: candidate-D's non-table prose joins the sweep (M1 —
        # ":978 all 32 default instances" had drifted from 31), and §4.4's
        # rewritten skip/non-planarity remark is pinned to the manifest
        ("proofs/candidate-D-singletype.md",
         r"all (\d+) default instances",
         (cnt["x3c_default_built"],)),
        ("proofs/candidate-D-singletype.md",
         r"test_obstacles\.py`\*\* \((\d+) checks\)",
         (cnt["obstacle_checks"],)),
        # round 10 (fable): "the six round-5 violations" was literal text in
        # the rendered table — the count is a placeholder now, swept here;
        # round 15: the table and the built/skipped remark live in README.md
        ("README.md", r"reproduces the (\d+) round-5 violations",
         (cnt["legacy_round5_violations"],)),
        ("README.md", r"(\d+) router skip events",
         (cnt["x3c_full_vacate_skipped"] + cnt["crosscheck_full_skipped"],)),
        ("README.md",
         r"(\d+) in the `--full --vacate` tier, (\d+) in the crosscheck",
         (cnt["x3c_full_vacate_skipped"], cnt["crosscheck_full_skipped"])),
        ("README.md", r"exactly (\d+) non-planar famil",
         (cnt["lemma_degenerate_nonplanar"],)),
        # round 16 (Opus F5, F8): the paper's §4.1 now says what the Theorem 4
        # suite searches at which scale, and step 5 of Lemma D.4 quotes the
        # measured stub margin — both renders, both numbers from the manifest
        ("paper/main.md",
         r"runs on (\d+) instances × (\d+) allocations in the battery and on "
         r"(\d+) instances under",
         (cnt["featureless_c6_instances"], cnt["featureless_c6_allocs"],
          cnt["featureless_c6_full_instances"])),
        ("paper/main.tex",
         r"runs on (\d+) instances\s+\$\\times\$\s+(\d+) allocations in the "
         r"battery\s+and on\s+(\d+)\s+instances under",
         (cnt["featureless_c6_instances"], cnt["featureless_c6_allocs"],
          cnt["featureless_c6_full_instances"])),
        ("paper/main.md",
         r"come as close as `L∞` distance (\d+) on the\s+instance corpus",
         (cnt["stub_margin_min"],)),
        ("paper/main.tex",
         r"come as close as\s+\$L_\\infty\$\s+distance (\d+) on the\s+instance\s+corpus",
         (cnt["stub_margin_min"],)),
        # round 16 (Opus F10): §4.1 attributes the 12 reduction-drawn engine
        # cases to what they test (damage and kill thresholds, one retaliation
        # blow), and §4.2 quotes the battery's own float-vs-exact constants
        # (test_round14_apparatus: equality to c = 2000, first split at 180)
        ("paper/main.md",
         r"(\d+) damage and kill-threshold cases drawn from the reduction",
         (cnt["engine_reduction_cases"],)),
        ("paper/main.tex",
         r"(\d+) damage and kill-threshold cases drawn from the reduction",
         (cnt["engine_reduction_cases"],)),
        ("paper/main.md", r"equality up\s+to `c = (\d+)` creatures", (2000,)),
        ("paper/main.tex", r"equality up to \$c=(\d+)\$ creatures", (2000,)),
        ("paper/main.md", r"published undefended branch at `c = (\d+)`", (180,)),
        ("paper/main.tex", r"published undefended\s+branch at \$c=(\d+)\$", (180,)),
    ]
    for rel, pattern, want in sweep:
        found = re.search(pattern, (root / rel).read_text())
        got = tuple(int(g) for g in found.groups()) if found else None
        check(f"{rel}: counter sweep ({pattern[:36]})", got, want)

    # (d) retired claims stay retired: each pattern below was a confirmed
    # text-vs-artifact contradiction in rounds 7-8; reappearing = regression
    banned = [
        (root / "MODEL.md", r"is a restriction of the real game"),
        (root / "MODEL.md", r"special case.{0,40}of the real game"),
        (root / "proofs" / "candidate-D-singletype.md",
         r"packed board is\s+`?O\(N\) × O\(N\)"),
        (root / "proofs" / "candidate-D-singletype.md",
         r"still need checking against their sources"),
        (root / "paper" / "main.md", r"cap constant is never read"),
        (root / "paper" / "main.md", r"so that the question cannot bite"),
        (root / "paper" / "main.tex", r"cap constant\s+is never read"),
        (root / "paper" / "main.tex", r"so that the question cannot bite"),
        # round-8 codex leg: the same retired claims surviving in siblings
        (root / "proofs" / "candidate-D-singletype.md",
         r"cap constant never enters"),
        (root / "proofs" / "candidate-D-singletype.md",
         r"restriction of the real game"),
        (root / "engine-check" / "REPORT.md", r"не читается вообще"),
        # and the (‡)-runs coverage overclaim: no searched blow strikes a
        # defending target, so nothing in those runs "genuinely changes"
        (root / "paper" / "main.md", r"arithmetic genuinely changes"),
        (root / "paper" / "main.tex", r"arithmetic genuinely changes"),
        # round 10 (B2): "the published corpora contain no non-planar family
        # at all" was FALSE — three exist; the zero measured the order of
        # checks (degeneracy is certified before planarity), not absence
        (root / "paper" / "main.md", r"no non-planar famil"),
        (root / "paper" / "main.tex", r"no non-planar famil"),
        (root / "proofs" / "candidate-D-singletype.md",
         r"usually no[nt][- ]?planar"),
        # round 13 (P13-1/P13-2): the round-12 repair's strict "less than
        # nominal" (false at a_i = 1) and the pre-round-12 equality that
        # survived in candidate-C
        (root / "paper" / "main.md", r"delivers (?:less than nominal|even\s+less)"),
        (root / "paper" / "main.tex", r"delivers (?:less than nominal|even\s+less)"),
        (root / "proofs" / "candidate-C-featureless.md",
         r"=\s+min\( T , nominal"),
    ]
    check("manifest banned_claims == the length of the ban list itself",
          len(banned), cnt["banned_claims"])

    # round 12 (P12-1/P12-6): every artifact-relative path the paper cites
    # must exist in the LOCAL tree — the network-free sibling of
    # check_artifact_repo.py, which pins the same paths against the
    # published tag. This catches a renamed or deleted file at edit time;
    # only the network check catches a stale public tree.
    # Round 13 (fable F-02, codex Check 06): the round-12 regex saw only
    # backticked paths with a directory prefix — 13 files — and missed the
    # fenced `python3 scripts/...` commands, among them search_free_order.py,
    # the very file whose absence was the round-12 blocker. One extractor
    # now serves both sweeps (check_artifact_repo.cited_paths), its count is
    # pinned, and it is drilled on a synthetic text below.
    from check_artifact_repo import cited_paths
    cited = cited_paths(root=str(root))
    check("the cited-path count (paper + companion note + README) == the "
          "manifest's pin", len(cited), cnt["cited_paths"])
    check("the companion note is itself a cited path of the paper",
          "paper/companion-empirics.md" in cited, True)
    check("the round-12 drifted file is in the sweep",
          "scripts/search_free_order.py" in cited, True)
    for path in sorted(cited):
        check(f"cited artifact path exists locally: {path}",
              (root / path).is_file(), True)
    drill_text = ("see `scripts/verify_x3c.py` and `dp_single_type.py`;\n"
                  "```\npython3 empirics/scripts/certify_scores.py\n"
                  "cd engine-check && ./build.sh && python3 compare.py\n```")
    check("mutation drill: the path extractor sees fenced commands, bare "
          "basenames and the engine-check line",
          cited_paths(text=drill_text, root=str(root)) >= {
              "scripts/verify_x3c.py", "scripts/dp_single_type.py",
              "empirics/scripts/certify_scores.py", "engine-check/build.sh",
              "engine-check/compare.py", "verification_manifest.json"},
          True)
    for path, pattern in banned:
        check(f"{path.name}: retired claim absent ({pattern[:40]})",
              re.search(pattern, path.read_text(), re.DOTALL) is None, True)


def doorway_case() -> Battle:
    """Round 16 (Opus review, F6): a kill that opens a doorway.

    5x2 board; row 1 is impassable except (1,1), where P1 stands. P2 at (0,0)
    is walled in by E_A at (1,0). Both players have speed 3, damage 1; each
    enemy has 1 hit point and value 1; E_B stands at (4,0). The optimum is 2:
    P1 kills E_A from where it stands, P2 walks through the freed hex to (3,0)
    and kills E_B. A relaxation that keeps living enemies as blockers sees no
    path for P2 at the root, bounds the value by 1, and prunes the win.
    """
    W, H = 5, 2

    def idx(x: int, y: int) -> int:
        return x + y * W

    obst = frozenset({idx(0, 1), idx(2, 1), idx(3, 1), idx(4, 1)})
    field = Battlefield(width=W, height=H, obstacles=obst)
    P = CreatureType("P", 1, 1, 1, 1, hp=5, speed=3)
    EA = CreatureType("EA", 1, 1, 1, 1, hp=1, speed=1, value=1)
    EB = CreatureType("EB", 1, 1, 1, 1, hp=1, speed=1, value=1)
    return Battle(field, [
        Stack(P, 1, side=0, slot=0, hex_=idx(1, 1)),
        Stack(P, 1, side=0, slot=1, hex_=idx(0, 0)),
        Stack(EA, 1, side=1, slot=0, hex_=idx(1, 0)),
        Stack(EB, 1, side=1, slot=1, hex_=idx(4, 0)),
    ])


def _enemies_as_walls_bound(battle: Battle, order, i: int, initial) -> int:
    """The pre-round-16 relaxation, verbatim in effect: allied blockers removed,
    living enemies kept as blockers. Kept only as the mutation-drill fixture."""
    from homm3_model import compute_damage, kills_for_damage
    enemies = [(k, s) for k, s in enumerate(battle.stacks) if s.side == 1]
    future = {k: 0 for k, _ in enemies}
    for k, _phase in order[i:]:
        attacker = battle.stacks[k]
        if attacker.side != 0 or not attacker.alive():
            continue
        probe = attacker.clone()
        walls = [s.clone() for _, s in enemies]
        relaxed = Battle(battle.field, [probe] + walls)
        back = {id(w): k2 for w, (k2, _) in zip(walls, enemies)}
        for target in relaxed.attackable(probe):
            future[back[id(target)]] += compute_damage(probe, target)
    upper = destroyed_value(battle, initial)
    for k, enemy in enemies:
        upper += kills_for_damage(enemy, future[k]) * enemy.ctype.value
    return upper


def test_prune_survives_opened_doorway() -> None:
    """Round 16 (Opus F6): `brute_force.relaxed_upper_bound` must not treat
    living enemies as walls. The docstring promised the bound "does not discard
    any legal action"; on the doorway board the old bound discarded the win.
    No published number moved (on the Theorem 1–2 boards no kill extends reach,
    Lemmas E.4/E.11), but the promise was false in general and the searcher is
    described as assumption-free. The drill re-installs the old relaxation and
    requires the search to lose the second kill — 1 before the fix, truth 2.
    """
    import brute_force as bf
    from brute_force import policy_hold
    check("doorway board, hold: the fixed prune keeps both kills",
          max_destroyed_value(doorway_case(), 1, policy_hold), 2)
    check("doorway board, (‡): the fixed prune keeps both kills",
          max_destroyed_value(doorway_case(), 1, policy_wait_defend), 2)
    original = bf.relaxed_upper_bound
    try:
        bf.relaxed_upper_bound = lambda *a, **k: 10 ** 9      # prune disabled
        truth = max_destroyed_value(doorway_case(), 1, policy_hold)
        bf.relaxed_upper_bound = _enemies_as_walls_bound
        old = max_destroyed_value(doorway_case(), 1, policy_hold)
    finally:
        bf.relaxed_upper_bound = original
    check("doorway board: search without any prune agrees", truth, 2)
    check("mutation drill: the pre-round-16 relaxation (enemies as walls) "
          "prunes the winning branch", old, 1)


def test_round16_apparatus() -> None:
    """Round 16 (Opus review, in-process pins).

    (a) F9: the verifiers build the paper's `(★)` instances — `att = def = 1`
    in the Theorem 1–2, Theorem 4 / Corollary 4.2 and Proposition 1.1 suites
    (they used 10, 10 and 5: the same factors 1.0, but a DEFEND bonus of +2
    instead of the +1 the paper's arithmetic reasons about). Re-running every
    suite at α = 1 moved no counter and no C6 node count.
    (b) F5: the `--full` extension of C6 runs on the suite's own list of the
    four smallest legal instances; its length and the default allocation
    sample are the manifest's numbers.
    """
    import json
    from pathlib import Path

    import brute_force as bf
    import dp_single_type as dp
    import verify_featureless as vf
    root = Path(__file__).resolve().parent.parent
    cnt = json.loads((root / "verification_manifest.json").read_text())["counters"]
    check("(★) in the verifiers: brute_force.ALPHA, verify_featureless.ALPHA, "
          "dp_single_type.ALPHA == 1", (bf.ALPHA, vf.ALPHA, dp.ALPHA), (1, 1, 1))
    field, enemies, player, slots, _B, _W = bf.build_partition_instance([1, 3])
    check("Theorem 1 instance built at att = def = 1",
          (player.attack, player.defense, enemies[0][0].attack,
           enemies[0][0].defense), (1, 1, 1, 1))
    inst = vf.build([4, 4, 4, 4, 5, 5], 13)
    check("Theorem 4 instance built at att = def = 1",
          (inst["player_types"][0].attack, inst["enemies"][0][0].defense), (1, 1))
    check("manifest featureless_c6_full_instances == len(SMALL_CASES)",
          len(vf.SMALL_CASES), cnt["featureless_c6_full_instances"])
    check("manifest featureless_c6_instances == the default C6 slice",
          vf.C6_DEFAULT_INSTANCES, cnt["featureless_c6_instances"])
    check("manifest featureless_c6_allocs == identity + the default sample",
          1 + vf.C6_DEFAULT_ALLOCS, cnt["featureless_c6_allocs"])
    check("the default C6 slice is the T = 13 pair, one yes and one no",
          [(T, vf.three_partition_answer(a, T))
           for a, T in vf.SMALL_CASES[:vf.C6_DEFAULT_INSTANCES]],
          [(13, True), (13, False)])


def test_round13_apparatus():
    """Round 13: two apparatus pins drilled in-process.

    (a) `certify_scores.bind_row` — codex Check 16 changed one stored ratio
    from 1.0 to 0.0 and certify_scores still printed 870/870; every field
    stats_recheck consumes is now bound to the certified (value, optimum).
    (b) `search_free_order.TRACE` — fable F-04 passed three degraded
    searchers through the whole suite; the corpus trace must go to zero
    under the degradations it claims to detect, and be positive under the
    full search, on a real corpus board.
    """
    import json
    import sys as _sys
    from pathlib import Path

    root = Path(__file__).resolve().parent.parent
    _sys.path.insert(0, str(root / "empirics" / "scripts"))
    import certify_scores as CS
    rows = json.loads((root / "empirics" / "results" / "llm.json")
                      .read_text())["per_response"]
    optima = json.loads((root / "empirics" / "instances" / "optima.json")
                        .read_text())
    row = rows[0]
    opt = optima[row["instance_id"]]["optimum"]
    check("bind_row accepts a genuine scored row",
          CS.bind_row(row, row["value"], opt), [])
    for field, value in (("ratio", 0.0), ("optimum", opt + 1),
                         ("variant", "no-such-variant"),
                         ("exact", not row["exact"])):
        bad = dict(row)
        bad[field] = value
        check(f"mutation drill: scored row with corrupted {field} is caught",
              bool(CS.bind_row(bad, row["value"], opt)), True)

    import random

    import search_free_order as S
    import verify_x3c as V
    n, sets = V.planted_instances(2, 1, 1, seed=41001)[0]
    inst = V.build_instance(n, sets, random.Random(41))
    check("free-order trace drill: the corpus board builds",
          inst is not None, True)
    alloc = {e: 1 for e in inst["deploy"]}
    S._trace_reset()
    S.free_play_value(inst, alloc, inst["target"])
    check("free-order trace: full search reorders and vanishes on a corpus "
          "board", (S.TRACE["reorder"] > 0, S.TRACE["vanish"] > 0),
          (True, True))
    for flag, key in (("free_order", "reorder"), ("vanish", "vanish")):
        S._trace_reset()
        battle, _ = V.build_battle(inst, alloc)
        S._search_battle(battle, inst["target"], **{flag: False})
        check(f"mutation drill: degraded searcher ({flag}=False) zeroes "
              f"the {key} trace", S.TRACE[key], 0)


def test_round14_apparatus():
    """Round 14 (gpt-6-astra pro, web reviewer): three apparatus pins, in-process.

    (a) `certify_scores.check_coverage` — F5: the old coverage check compared
    SETS of (task_id, model) keys, so replacing one cell by a duplicate of
    another in both files kept 870 records, 869 keys per side, equal sets, and
    printed ALL PASS (reproduced on a shadow copy). The matrix check now runs
    on the raw lists against the DECLARED design (llm_tasks x three tiers);
    the drills rebuild the duplicate, a missing cell and an undeclared model.
    (b) `exact_damage` — F2: the reference simulator's floats and the
    exact rationals of MODEL.md section 4 split on some calls (base 90 /
    def 10 / DEFEND: 62 vs 63); the dual instrumentation must SEE that split
    (positive control), and on the constructions' own constants the two
    arithmetics must agree over every stack size the paper reasons about —
    the published Theorem-3 undefended branch is where they first part, at
    c = 180, which the paper now states and this drill pins as the number it is.
    (c) the slow block of `test_docs_match_artifacts` replays all 145 optima
    with the exact routine installed (the witness half of
    `exact_arithmetic_crosscheck.py`, ~10 s) and pins the script's recorded
    final line to the manifest.
    """
    import json
    import sys as _sys
    from pathlib import Path

    root = Path(__file__).resolve().parent.parent
    _sys.path.insert(0, str(root / "empirics" / "scripts"))
    import certify_scores as CS

    rows = json.loads((root / "empirics" / "results" / "llm.json")
                      .read_text())["per_response"]
    raw = [json.loads(l) for l in
           open(root / "empirics" / "responses_final.jsonl") if l.strip()]
    expected = CS.expected_keys(root / "empirics" / "llm_tasks.jsonl")
    raw_keys = [(r["task_id"], r["model"]) for r in raw]
    scored_keys = [(r["task_id"], r["model"]) for r in rows]
    check("coverage: the declared matrix is tasks x tiers",
          len(expected), len(rows))
    check("coverage: the genuine response and score lists fill the matrix "
          "exactly once", CS.check_coverage(raw_keys, scored_keys, expected), [])
    a, b = raw_keys[0], next(k for k in raw_keys if k != raw_keys[0])
    dup_raw = [a if k == b else k for k in raw_keys]
    dup_scored = [a if k == b else k for k in scored_keys]
    check("mutation drill (F5): one cell duplicated in both lists is caught",
          bool(CS.check_coverage(dup_raw, dup_scored, expected)), True)
    check("mutation drill (F5): a missing cell is caught",
          bool(CS.check_coverage(raw_keys[1:], scored_keys[1:], expected)), True)
    stray = [(a[0], "no-such-tier")]
    check("mutation drill (F5): an undeclared model is caught",
          bool(CS.check_coverage(raw_keys + stray, scored_keys + stray,
                                 expected)), True)

    import exact_damage as E
    import homm3_model as M
    import solve as _solve
    check("exact arithmetic positive control: the base-90 cell splits "
          "(float 62, exact 63)",
          (E.probe_call(M.compute_damage), E.probe_call(E.exact_compute_damage)),
          (62, 63))
    trace = E.DualTrace()
    undo = E.install_dual(trace, _solve)
    try:
        E.probe_call(M.compute_damage)
    finally:
        undo()
    check("exact arithmetic instrumentation records the split it is fed",
          (trace.calls, [d[-2:] for d in trace.disagreements]), (1, [(62, 63)]))
    check("exact arithmetic instrumentation is removed after use",
          (M.compute_damage.__name__, E.probe_call(M.compute_damage)),
          ("compute_damage", 62))

    def split_sizes(att, deff, defending, upto=2000):
        a = M.CreatureType("a", attack=att, defense=1, dmg_min=1, dmg_max=1,
                           hp=1, speed=1)
        d = M.CreatureType("d", attack=1, defense=deff, dmg_min=1, dmg_max=1,
                           hp=10**6, speed=1)
        out = []
        for c in range(1, upto + 1):
            s, t = M.Stack(a, c, 0, 0, 0), M.Stack(d, 1, 1, 0, 1)
            t.defending = defending
            if M.compute_damage(s, t) != E.exact_compute_damage(s, t):
                out.append(c)
        return out

    # (★): att = def = 1, a waiting blow meets the +1 DEFEND bonus (factor 0.975)
    check("floats == exact rationals on every (★) waiting blow up to c = 2000",
          split_sizes(1, 1, True), [])
    # Theorem 3, historical constants (def 41): both branches
    check("floats == exact rationals on Theorem 3's historical branches up "
          "to c = 2000", (split_sizes(1, 41, False), split_sizes(1, 41, True)),
          ([], []))
    # Theorem 3, published constants (def 27): defended branch agrees; the
    # undefended one (1 - 0.65, the double nearest 7/20 lies below it) first
    # splits at c = 180 — beyond every searched instance (3q <= 12), pinned
    # as the measurement the paper's Appendix D states
    check("floats == exact rationals on Theorem 3's published defended branch "
          "up to c = 2000", split_sizes(1, 27, True), [])
    pub = split_sizes(1, 27, False)
    check("Theorem 3's published undefended branch: floats first part from "
          "exact rationals at c = 180, well past every searched stock",
          (pub[:1], all(c > 12 for c in pub)), ([180], True))


def main() -> int:
    test_round16_apparatus()
    test_prune_survives_opened_doorway()
    test_round14_apparatus()
    test_round13_apparatus()
    test_exhaustive_destinations()
    test_moved_stack_frees_hex()
    test_iteration_one_retaliation()
    test_adapter_figures_match_code()
    test_speed_widening_breaks_matching_reach()
    test_enemy_branch_no_state_leak()
    test_wait_defend_lands_after_normal_blows()
    test_waiting_player_strikes_defended_target()
    test_docs_match_artifacts()

    # The manifest's counter for THIS suite, checked outside `check()` so the
    # comparison cannot change the number it verifies. The README's table row
    # is the manifest's render (checked above), so this covers it too.
    import json
    import sys
    from pathlib import Path
    man = json.loads((Path(__file__).resolve().parent.parent
                      / "verification_manifest.json").read_text())
    claimed = man["counters"]["regressions"]
    if "--fast" in sys.argv:
        # --fast skips the six slow subprocess pins, so PASSED here is not
        # the number the manifest documents; only the full run may pin it.
        print(f"note: --fast run ({PASSED} checks); the manifest count "
              f"({claimed}) is pinned by the full suite only")
    elif claimed != PASSED:
        FAILURES.append(f"manifest claims {claimed} regressions, "
                        f"suite ran {PASSED}")

    if FAILURES:
        print(f"FAILED ({len(FAILURES)}):")
        for failure in FAILURES:
            print(f"  - {failure}")
        return 1
    print(f"OK: {PASSED} search and mechanics regressions")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
