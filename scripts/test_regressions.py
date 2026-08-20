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
    """The Dragon Fly mechanism of paper sec. 5.1, as a search-level check.

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
    five slow subprocess pins.
    """
    import json
    import re
    import subprocess
    import sys as _sys
    from pathlib import Path

    root = Path(__file__).resolve().parent.parent
    man = json.loads((root / "verification_manifest.json").read_text())
    cnt = man["counters"]

    # (a) both paper tables are exactly the manifest's render
    gen = subprocess.run(
        [_sys.executable, str(root / "scripts" / "gen_verification_table.py")],
        capture_output=True, text=True)
    check("verification tables match the manifest render "
          "(gen_verification_table.py check mode)", gen.returncode, 0)
    # round 10 (fable): deleting a manifest row used to drop a suite from
    # both rendered tables with a green battery — the row list is now pinned
    check("manifest rows: the expected suites, in order",
          [r["id"] for r in man["rows"]],
          ["verify_mechanics", "brute_force", "test_obstacles",
           "dp_single_type", "verify_featureless", "verify_x3c_default",
           "verify_x3c_vacate", "verify_x3c_defend", "verify_x3c_full_vacate",
           "crosscheck_full", "crosscheck_defend", "verify_embedding",
           "verify_hp_objective", "verify_full_model_optima",
           "certify_scores", "check_defend_policy", "test_regressions",
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
                for kind in ("md", "tex"):
                    row[kind] = [c.replace("{x3c_default_built}", "3")
                                 for c in row[kind]]

    def swap(bad):
        for row in bad["rows"]:
            if row["id"] == "verify_embedding":
                for kind in ("md", "tex"):
                    row[kind] = [
                        c.replace("{lemma_built}", "\0")
                        .replace("{lemma_nonplanar}", "{lemma_built}")
                        .replace("\0", "{lemma_nonplanar}")
                        for c in row[kind]]

    check("mutation drill: counter retyped as a declared literal is caught",
          drilled(retype), True)
    check("mutation drill: placeholder swap inside a row is caught",
          drilled(swap), True)

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
          (cnt["sep_pairs"], 12, 16, 20))
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

    # round 9 (DeepSeek API): §5.2's observation-2 statistics — the Spearman
    # pair, the k-bucket table and the natural-family sequence — now have a
    # generating artifact (stats_recheck.py, from results/llm.json), and the
    # paper's prose must quote its output verbatim in both versions
    st = subprocess.run(
        [_sys.executable,
         str(root / "empirics" / "scripts" / "stats_recheck.py")],
        capture_output=True, text=True)
    check("stats_recheck.py runs", st.returncode, 0)
    paper_md = (root / "paper" / "main.md").read_text()
    paper_tex = (root / "paper" / "main.tex").read_text()
    m = re.search(r"Spearman\(k, ratio\) all = (-\d+\.\d+); "
                  r"natural = (-\d+\.\d+)", st.stdout)
    check("stats_recheck.py reports both Spearman coefficients",
          m is not None, True)
    if m:
        sp_all, sp_nat = m.group(1), m.group(2)
        check("main.md quotes the recomputed Spearman pair",
              f"Spearman `{sp_all}`, and `{sp_nat}`" in paper_md, True)
        check("main.tex quotes the recomputed Spearman pair",
              f"Spearman ${sp_all}$, and ${sp_nat}$" in paper_tex, True)
    def tex_row_pattern(mdline: str) -> str:
        # a printed markdown row, as the equivalent LaTeX tabular row: `x`
        # becomes \src{x}, — becomes ---, " %" becomes "\,\%", and cell
        # padding around & is free
        cells = [c.strip() for c in mdline.strip().strip("|").split("|")]
        out = []
        for c in cells:
            c = c.replace("—", "---")
            if c.startswith("`") and c.endswith("`"):
                c = "\\src{" + c[1:-1] + "}"
            c = c.replace(" %", "\\,\\%")
            out.append(re.escape(c))
        return r"\s*&\s*".join(out)

    for line in st.stdout.splitlines():
        if line.startswith("| `claude-") and "%" not in line:
            check(f"main.md k-bucket row matches llm.json ({line[2:24]}…)",
                  line in paper_md, True)
            check(f"main.tex k-bucket row matches llm.json ({line[2:24]}…)",
                  " & ".join(line.strip("| ").split(" | ")[1:]) in paper_tex,
                  True)
        # round 10: the §5.2 headline rows, the baseline rows and the
        # observation-3 percentage points are generated now too
        if (line.startswith("| `claude-") and "%" in line) or \
                line.startswith("| greedy-") or \
                line.startswith("| 100-sample"):
            check(f"main.md headline/baseline row matches the artifacts "
                  f"({line[2:26]}…)", line in paper_md, True)
            check(f"main.tex headline/baseline row matches the artifacts "
                  f"({line[2:26]}…)",
                  re.search(tex_row_pattern(line), paper_tex) is not None,
                  True)
        if line.startswith("geometry-removal cost: "):
            phrase = "cost " + line.split(": ", 1)[1]
            check("main.md quotes the geometry-removal percentage points",
                  phrase in paper_md, True)
            check("main.tex quotes the geometry-removal percentage points",
                  phrase in paper_tex, True)
        if line.startswith("natural-family haiku sequence: "):
            seq = line.split(": ", 1)[1]
            check("both papers quote the natural-family haiku sequence",
                  seq in paper_md and seq in paper_tex, True)

    # round 10 (M2): §5.1's ability-projection numbers are pinned to the
    # committed audit artifact (the audit itself needs a VCMI checkout, so
    # the battery pins the papers to the shipped JSON, not the JSON to VCMI)
    ab = json.loads(
        (root / "empirics" / "results" / "ability_projection.json")
        .read_text())
    for name, n in {**ab["tally_melee"], **ab["tally_extended"]}.items():
        m = re.search(rf"`{name}` on\s+(\d+)", paper_md)
        check(f"main.md quotes the {name} slot count",
              int(m.group(1)) if m else None, n)
        m = re.search(re.escape("\\src{" + name.replace("_", r"\_") + "}")
                      + r" on\s+(\d+)", paper_tex)
        check(f"main.tex quotes the {name} slot count",
              int(m.group(1)) if m else None, n)
    for label, text in (("main.md", paper_md), ("main.tex", paper_tex)):
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
        # comments and the §1.2 instance count previously had no guard at all
        ("paper/main.md", r"# (\d+) checks: damage formula",
         (cnt["mechanics_checks"],)),
        ("paper/main.md", r"# (\d+) checks on geometry and blocking",
         (cnt["obstacle_checks"],)),
        ("paper/main.md", r"language models on (\d+) instances",
         (cnt["empirical_instances"],)),
        ("paper/main.tex", r"# (\d+) checks: damage formula",
         (cnt["mechanics_checks"],)),
        ("paper/main.tex", r"# (\d+) checks on geometry and blocking",
         (cnt["obstacle_checks"],)),
        ("paper/main.tex", r"language models on (\d+) instances",
         (cnt["empirical_instances"],)),
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
        # both rendered tables — the count is a placeholder now, swept here
        ("paper/main.md", r"reproduces the (\d+) round-5 violations",
         (cnt["legacy_round5_violations"],)),
        ("paper/main.tex", r"reproduces the (\d+) round-5 violations",
         (cnt["legacy_round5_violations"],)),
        ("paper/main.md", r"(\d+) router skip events",
         (cnt["x3c_full_vacate_skipped"] + cnt["crosscheck_full_skipped"],)),
        ("paper/main.md",
         r"(\d+) in the `--full --vacate` tier, (\d+) in the crosscheck",
         (cnt["x3c_full_vacate_skipped"], cnt["crosscheck_full_skipped"])),
        ("paper/main.tex", r"(\d+) router skip events",
         (cnt["x3c_full_vacate_skipped"] + cnt["crosscheck_full_skipped"],)),
        ("paper/main.tex",
         r"(\d+) in the \\src\{--full --vacate\} tier, (\d+) in the "
         r"crosscheck",
         (cnt["x3c_full_vacate_skipped"], cnt["crosscheck_full_skipped"])),
        ("paper/main.md", r"exactly (\d+) non-planar famil",
         (cnt["lemma_degenerate_nonplanar"],)),
        ("paper/main.tex", r"exactly (\d+) non-planar famil",
         (cnt["lemma_degenerate_nonplanar"],)),
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
    ]
    check("manifest banned_claims == the length of the ban list itself",
          len(banned), cnt["banned_claims"])
    for path, pattern in banned:
        check(f"{path.name}: retired claim absent ({pattern[:40]})",
              re.search(pattern, path.read_text(), re.DOTALL) is None, True)


def main() -> int:
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
    # comparison cannot change the number it verifies. The paper rows are the
    # manifest's render (checked above), so this covers main.md and main.tex.
    import json
    import sys
    from pathlib import Path
    man = json.loads((Path(__file__).resolve().parent.parent
                      / "verification_manifest.json").read_text())
    claimed = man["counters"]["regressions"]
    if "--fast" in sys.argv:
        # --fast skips the five slow subprocess pins, so PASSED here is not
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
