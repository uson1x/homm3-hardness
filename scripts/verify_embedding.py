#!/usr/bin/env python3
"""Machine checks for the Lemma D.4 embedding algorithm (embed_lemma.py).

What runs on what — stated precisely, because the boards this algorithm
produces are λ = 20 times larger per drawing unit than the compact router's:

  1. EVERY family of the published verify_x3c and crosscheck_sol corpora
     (default and --full tiers, both seed sets) is fed to the algorithm.
     For each: either a board comes back — then invariants I1-I4
     (verify_x3c.check_geometry) must hold, the REAL (SEP') separation must
     hold (all three non-incident feature classes — box↔box, box↔corridor,
     corridor↔corridor — at L∞ ≥ λ − 2ρ = 12, computed exactly over the
     exported feature geometry; round 10 retired the image-only predecessor
     of this check as an identity), and building twice must give identical
     boards, field by field — or ("G_no", {reason, instance}) comes back,
     and then the reason must be the DMP planarity verdict or a true
     degeneracy certificate, re-verified against the family. Degenerate
     families are ALSO planarity-tested directly here, because step 0
     certifies degeneracy before ever running the planarity test: the
     corpus contains families that are both (counted separately below),
     and the lemma's non-planar counter alone says nothing about the
     corpus — a round-10 catch.

  2. The total-reduction branch is fuzzed: |X| not divisible by 3, |C| < q,
     an uncovered element, malformed members of C in many shapes (wrong
     length, repeats, out of range, mixed types, non-sequences, booleans),
     malformed |X| (negative, non-integer), a duplicate member of C (must
     be DELETED, not rejected — the built board must be identical to the
     deduplicated family's), the empty instance |X| = 0 (a YES-instance:
     the empty cover — must map to G_yes, the image of X={0,1,2},
     C={{0,1,2}}), and a planted K3,3-subdivision incidence graph, which
     must map to G_no as non-planar. The G_no payload's fixed instance is
     PLAYED here, under both constant sets, and must be a genuine no.

  3. On the smallest instances (the fixed 3-entry list below; --slow adds
     one more planted q = 2 board) the full game search of verify_x3c runs
     ON the lemma-built board and must agree with X3C, with the canonical
     all-ones allocation the unique winner on yes-instances — under BOTH
     the historical constants (def 41, the verify_x3c defaults) and the
     published Theorem 3 constants (def 27, hp 4, via crosscheck_sol's
     swap), and the built enemy defence is asserted each time, so a
     silently ineffective swap fails rather than passes. On the larger
     boards the exhaustive search is out of reach by design (the compact
     router exists exactly for that), and this file says so rather than
     pretending otherwise.

Run:  python3 verify_embedding.py [--slow]
"""

from __future__ import annotations

import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import crosscheck_sol as C  # noqa: E402
import planar_embed  # noqa: E402
import verify_x3c as V  # noqa: E402
from brute_force import max_destroyed_value  # noqa: E402
from embed_lemma import LAMBDA, RHO, build_board_lemma  # noqa: E402
from homm3_model import Battle, Battlefield, Stack  # noqa: E402

FAILS: list[str] = []

# a K3,3 subdivision as an X3C incidence graph: 6 sets = branch vertices,
# 9 elements = the subdivided edges, each element in exactly two sets.
# Well-formed (|X| = 9, all covered), but the incidence graph is non-planar.
_K33_EDGES = [(a, b) for a in range(3) for b in range(3, 6)]
K33_FAMILY = (9, [tuple(sorted(ei for ei, (a, b) in enumerate(_K33_EDGES)
                          if v in (a, b))) for v in range(6)])


def fail(msg: str) -> None:
    FAILS.append(msg)
    print("   FAIL", msg)


def corpus() -> list[tuple[int, list[tuple]]]:
    """Every family of the published suites, deduplicated, order-stable."""
    fams = (
        [(3, [(0, 1, 2)])]
        + V.planted_instances(2, 2, 10, seed=3)
        + V.random_instances(2, 3, 10, seed=5)
        + V.random_instances(2, 4, 10, seed=41)
        + V.planted_instances(3, 2, 10, seed=13)
        + V.random_instances(3, 6, 10, seed=17)
        + V.planted_instances(4, 2, 5, seed=23)
        + V.random_instances(4, 7, 5, seed=29)
        # the crosscheck_sol corpus (crosscheck_sol.cross_instances)
        + V.planted_instances(2, 2, 8, seed=3)
        + V.random_instances(2, 3, 8, seed=5)
        + V.random_instances(2, 4, 8, seed=41)
        + V.planted_instances(3, 2, 6, seed=13)
        + V.random_instances(3, 6, 6, seed=17)
        + V.planted_instances(4, 2, 3, seed=23)
    )
    seen = set()
    out = []
    for n, sets in fams:
        key = (n, tuple(sorted(tuple(s) for s in sets)))
        if key not in seen:
            seen.add(key)
            out.append((n, sets))
    return out


def incidence_planar(n: int, sets: list[tuple]) -> bool:
    """DMP verdict on the deduplicated incidence graph, exactly as
    embed_lemma builds it — used to planarity-test the families step 0
    never reaches (it certifies degeneracy first)."""
    seen: set = set()
    ded = []
    for s in sets:
        k = tuple(sorted(s))
        if k not in seen:
            seen.add(k)
            ded.append(tuple(s))
    edges = [(e, n + i) for i, s in enumerate(ded) for e in s]
    return planar_embed.planarity(n + len(ded), edges) is not None


def _rect_dist(a, b) -> int:
    """Exact min L∞ distance between two axis-aligned rectangles: the max
    of the per-coordinate interval gaps (coordinates are independent)."""
    (ax0, ax1, ay0, ay1), (bx0, bx1, by0, by1) = a, b
    gx = max(0, bx0 - ax1, ax0 - bx1)
    gy = max(0, by0 - ay1, ay0 - by1)
    return max(gx, gy)


def _segments(chain):
    """Axis-parallel corridor chain -> degenerate rectangles."""
    out = []
    for (px, py), (qx, qy) in zip(chain, chain[1:]):
        out.append((min(px, qx), max(px, qx), min(py, qy), max(py, qy)))
    return out


def check_separation(inst) -> tuple[list[str], dict]:
    """The REAL (SEP'): every pair of non-incident features — two gadget
    boxes, a box and a corridor of an edge not incident to its vertex, two
    corridors of edges sharing no endpoint — at L∞ ≥ λ − 2ρ. Distances are
    exact (rectangle arithmetic), features are the exported geometry itself.
    Corridor chains keep their tails inside their OWN endpoints' boxes;
    that cannot mask a violation against a non-incident feature, because a
    tail lies within ρ of its own vertex centre and centres are λ apart.

    Round 10 retired the predecessor of this check — pairwise L∞ ≥ λ over
    vertex images — as an identity: images are λ times distinct grid
    points, so it could not fail for ANY λ.

    Round 11 (P11-4) found the successor starvable: an empty `corridors`
    (or `boxes`) export made every loop below vacuous — ALL PASS with
    nothing checked. The check now also returns per-class statistics
    (pair count and min L∞), and the caller demands every class was
    actually exercised across the corpus."""
    feats = inst["features"]
    lam, rho = feats["lam"], feats["rho"]
    need = lam - 2 * rho
    bad = []
    stats = {cls: [0, None] for cls in
             ("box_box", "box_corridor", "corridor_corridor")}

    def seen(cls: str, d: int) -> None:
        stats[cls][0] += 1
        if stats[cls][1] is None or d < stats[cls][1]:
            stats[cls][1] = d

    boxes = {v: (cx - rho, cx + rho, cy - rho, cy + rho)
             for v, (cx, cy) in feats["boxes"].items()}
    corrs = {e: _segments(chain) for e, chain in feats["corridors"].items()}
    keys = sorted(boxes)
    for i, v in enumerate(keys):
        for w in keys[i + 1:]:
            d = _rect_dist(boxes[v], boxes[w])
            seen("box_box", d)
            if d < need:
                bad.append(f"boxes {v},{w}: L∞ = {d} < λ-2ρ = {need}")
    for e, segs in sorted(corrs.items()):
        for w in keys:
            if w in e:
                continue
            d = min(_rect_dist(s, boxes[w]) for s in segs)
            seen("box_corridor", d)
            if d < need:
                bad.append(f"corridor {e} vs box {w}: L∞ = {d} < {need}")
    ckeys = sorted(corrs)
    for i, e1 in enumerate(ckeys):
        for e2 in ckeys[i + 1:]:
            if set(e1) & set(e2):
                continue
            d = min(_rect_dist(s1, s2)
                    for s1 in corrs[e1] for s2 in corrs[e2])
            seen("corridor_corridor", d)
            if d < need:
                bad.append(f"corridors {e1} vs {e2}: L∞ = {d} < {need}")
    return bad, stats


def boards_equal(a, b) -> bool:
    if set(a) != set(b):
        return False
    return all(a[k] == b[k] for k in a)


def g_no_is_a_no(payload) -> list[str]:
    """Play the G_no payload's fixed instance: one slot, stock 1, no
    enemies, W = 1 — destroyed value must be 0 < 1 for every allocation
    (there is exactly one) under the CURRENT constants."""
    bad = []
    inst = payload["instance"]
    if inst["target"] < 1 or inst["stock"] != 1 or inst["enemy_hex"]:
        bad.append(f"G_no instance malformed: {inst['stock']=} "
                   f"{inst['target']=} {len(inst['enemy_hex'])=}")
        return bad
    battle = Battle(Battlefield(inst["width"], inst["height"]),
                    [Stack(inst["player_type"], 1, side=0, slot=0, hex_=0)])
    got = max_destroyed_value(battle, inst["rounds"])
    if got >= inst["target"]:
        bad.append(f"G_no instance is not a no: destroyed {got} >= "
                   f"W = {inst['target']}")
    return bad


def main() -> int:
    slow = "--slow" in sys.argv[1:]
    print("=" * 72)
    print("Lemma D.4, executed: DMP planarity -> orthogonal drawing -> "
          "λ=20 scaling,")
    print("adapters, corridors, deployment stubs -> invariants I1-I4 + "
          "real (SEP')")
    print("=" * 72)

    # the constants are the paper's literals, and (SEP') is non-vacuous
    if (LAMBDA, RHO) != (20, 4):
        fail(f"constants drifted from the paper: λ = {LAMBDA}, ρ = {RHO} "
             f"(Lemma D.4 states λ = 20, ρ = 4)")
    if LAMBDA - 2 * RHO < 2:
        fail(f"λ - 2ρ = {LAMBDA - 2 * RHO} < 2: (SEP') no longer implies "
             f"non-adjacency — this is the λ = 9 draft error")

    fams = corpus()
    built = 0
    nonplanar = 0
    degenerate_no = 0
    deg_nonplanar = 0
    max_side = 0
    sep_totals = {cls: [0, None] for cls in
                  ("box_box", "box_corridor", "corridor_corridor")}
    t0 = time.time()
    print(f"\n[1] the published corpora through the algorithm "
          f"({len(fams)} distinct families)")
    for n, sets in fams:
        kind, payload = build_board_lemma(n, sets)
        kind2, payload2 = build_board_lemma(n, sets)
        if kind != kind2:
            fail(f"{sets}: two builds disagree in kind ({kind} vs {kind2})")
        if kind == "G_no":
            reason = payload["reason"]
            if payload != payload2:
                fail(f"{sets}: G_no payload not deterministic")
            if "planar" in reason:
                nonplanar += 1
            elif "no set" in reason:
                # a random family really can leave an element uncovered;
                # then G_no is the lemma's CORRECT output — but only if the
                # certificate is true and the instance really is a no
                if all(any(e in s for s in sets) for e in range(n)):
                    fail(f"{sets}: 'no set' certificate is false")
                if V.x3c_is_yes(n, sets):
                    fail(f"{sets}: G_no for a yes-instance — the "
                         f"certificate lied")
                degenerate_no += 1
                # step 0 certifies degeneracy BEFORE the planarity test, so
                # the non-planar counter above says nothing about these
                # families — test them directly (round 10)
                if not incidence_planar(n, sets):
                    deg_nonplanar += 1
            else:
                fail(f"{sets}: G_no for a well-formed family with reason "
                     f"{reason!r} — only non-planarity or a true "
                     f"degeneracy certificate is acceptable here")
            continue
        inst = payload
        if not boards_equal(inst, payload2):
            fail(f"{sets}: two builds differ — the algorithm is not "
                 f"deterministic")
        geo = V.check_geometry(inst)
        for g in geo:
            fail(f"{sets}: {g}")
        seps, sep_stats = check_separation(inst)
        for s in seps:
            fail(f"{sets}: (SEP') violated: {s}")
        for cls, (pairs, mind) in sep_stats.items():
            sep_totals[cls][0] += pairs
            if mind is not None and (sep_totals[cls][1] is None
                                     or mind < sep_totals[cls][1]):
                sep_totals[cls][1] = mind
        built += 1
        max_side = max(max_side, inst["width"], inst["height"])
    dt = time.time() - t0
    print(f"   built {built}, certified non-planar {nonplanar}, "
          f"certified degenerate-no {degenerate_no} "
          f"(of which {deg_nonplanar} also non-planar, reached first by "
          f"the degeneracy certificate), largest board side {max_side} "
          f"hexes ({dt:.0f}s)")
    # round 11 (P11-4): the class loops are only evidence if they ran —
    # a starved feature export used to make every one of them vacuous
    for cls, (pairs, mind) in sep_totals.items():
        if pairs == 0:
            fail(f"(SEP') class {cls} was never exercised across the whole "
                 f"corpus — the feature export is starved")
    sep_pairs = sum(p for p, _ in sep_totals.values())
    sep_mins = tuple(sep_totals[cls][1] for cls in
                     ("box_box", "box_corridor", "corridor_corridor"))
    print(f"   every built board passes I1-I4 and the real (SEP') check "
          f"(boxes and corridors, all three non-incident classes); every "
          f"degeneracy certificate is re-verified; a non-planar skip is "
          f"the DMP test's own verdict (planted control in [2])")
    print(f"   (SEP') exercised on {sep_pairs} non-incident feature pairs: "
          f"class minima L∞ = {sep_mins[0]}/{sep_mins[1]}/{sep_mins[2]} "
          f"(box-box/box-corridor/corridor-corridor) against the required "
          f"{LAMBDA - 2 * RHO}")

    print("\n[2] the total-reduction branch (step 0, fuzzed)")
    malformed = 0
    for args, want in [
        ((4, [(0, 1, 2)]), "divisible"),
        ((3, []), "|C| < q"),
        ((6, [(0, 1, 2), (0, 1, 3)]), "no set"),
        ((3, [(0, 0, 1)]), "not a 3-set"),
        ((3, [(0, 1)]), "not a 3-set"),
        ((6, [(0, 1, 2, 3), (3, 4, 5)]), "not a 3-set"),
        ((3, [(0, 1, 5)]), "not a 3-set"),
        # round-10 shapes: these used to raise instead of certifying
        ((3, [(0, "1", 2)]), "not a 3-set"),
        ((3, [(0, 1.0, 2)]), "not a 3-set"),
        ((3, [(0, True, 2)]), "not a 3-set"),
        ((3, [7]), "not a 3-set"),
        ((3, [None]), "not a 3-set"),
        ((3, 7), "not a sequence"),
        ((-3, []), "non-negative"),
        ((1.5, []), "non-negative"),
        ((True, []), "non-negative"),
        ((None, []), "non-negative"),
    ]:
        kind, payload = build_board_lemma(*args)
        if kind != "G_no" or want not in payload["reason"]:
            fail(f"malformed {args!r}: expected G_no ({want!r}), "
                 f"got {kind} {payload!r}")
        else:
            malformed += 1
    # the G_no payload is the lemma's CONCRETE no-instance — play it,
    # under the historical and the published constants
    for label, swap in (("def 41", False), ("def 27", True)):
        saved = C.with_sol_stats() if swap else None
        try:
            _, payload = build_board_lemma(3, [(0, 1)])
            for b in g_no_is_a_no(payload):
                fail(f"[{label}] {b}")
        finally:
            if saved is not None:
                C.restore(saved)
    # duplicates are DELETED, not rejected: identical board either way
    kd, bd = build_board_lemma(3, [(0, 1, 2), (2, 1, 0)])
    ks, bs = build_board_lemma(3, [(0, 1, 2)])
    if kd != "board" or ks != "board" or not boards_equal(bd, bs):
        fail("duplicate member of C: expected the deduplicated family's "
             "board, field by field")
    # the empty instance is a well-formed YES (the empty cover) and must
    # map to G_yes — the image of the fixed yes-family (round 10: the old
    # target-0 board was not a legal instance, W ∈ Z>0)
    ke, be = build_board_lemma(0, [])
    ky, by = build_board_lemma(3, [(0, 1, 2)])
    if ke != "board" or ky != "board" or not boards_equal(be, by):
        fail(f"|X| = 0: expected G_yes = the board of (3, [(0,1,2)]), "
             f"got {ke}")
    # planted non-planar control: a K3,3-subdivision incidence graph
    kk, kp = build_board_lemma(*K33_FAMILY)
    if kk != "G_no" or "planar" not in kp["reason"]:
        fail(f"planted K3,3 subdivision: expected the non-planar G_no, "
             f"got {kk} {kp!r}")
    if not FAILS:
        print(f"   {malformed} malformed/degenerate certificates fire, none "
              f"silently and none by raising; the G_no instance plays as a "
              f"genuine no under both constant sets; duplicates deleted "
              f"(board identical to the deduplicated family's); |X| = 0 "
              f"maps to G_yes; the planted K3,3 subdivision is refused as "
              f"non-planar")

    print("\n[3] full game search on lemma-built boards (small instances),")
    print("    historical constants (def 41) AND published constants (def 27)")
    small = [
        (3, [(0, 1, 2)]),                            # q = 1, yes
        (6, [(0, 1, 2), (0, 3, 4), (2, 4, 5)]),      # q = 2, covering, NO
    ] + V.planted_instances(2, 2, 1, seed=3)         # q = 2, planted yes
    if slow:
        small += V.planted_instances(2, 2, 2, seed=3)[1:]
    for n, sets in small:
        want = V.x3c_is_yes(n, sets)
        for label, swap in (("def 41", False), ("def 27", True)):
            saved = C.with_sol_stats() if swap else None
            try:
                kind, inst = build_board_lemma(n, sets)
                if kind != "board":
                    fail(f"{sets}: expected a board for the end-to-end check")
                    continue
                # the swap must actually reach the build (round 10, after a
                # reviewer conjectured a silent no-op here): assert the
                # built defence, not the label
                want_def = 27 if swap else 41
                if inst["enemy_type"].defense != want_def:
                    fail(f"{sets} [{label}]: built enemy defence "
                         f"{inst['enemy_type'].defense}, expected "
                         f"{want_def} — the constant swap did not reach "
                         f"the build")
                t1 = time.time()
                wins = V.winning_allocations(inst)
            finally:
                if saved is not None:
                    C.restore(saved)
            got = bool(wins)
            mark = "ok " if want == got else "FAIL"
            print(f"  {mark} [{label}] q={n // 3} sets={len(sets)} "
                  f"board {inst['width']}x{inst['height']} "
                  f"X3C={'Y' if want else 'N'} game={'Y' if got else 'N'} "
                  f"winners={len(wins)} ({time.time() - t1:.0f}s)")
            if want != got:
                fail(f"{sets} [{label}]: on the lemma board X3C={want} "
                     f"but game={got}")
            elif got and wins != [(1,) * n]:
                fail(f"{sets} [{label}]: winners {wins[:5]}, expected only "
                     f"all-ones")
    if not slow:
        print("   (--slow adds one more planted q=2 board; larger lemma "
              "boards are validated by [1] only — the exhaustive search "
              "is out of reach there by design)")

    print("\n" + "-" * 72)
    if FAILS:
        print(f"FAILURES ({len(FAILS)}):")
        for f in FAILS[:40]:
            print("  ", f)
        return 1
    print(f"ALL PASS — the embedding algorithm of Lemma D.4 is executable, "
          f"deterministic, total ({built} boards, {nonplanar} certified "
          f"non-planar, {degenerate_no} certified degenerate-no of which "
          f"{deg_nonplanar} also non-planar, {malformed} malformed "
          f"certificates, 1 planted non-planar control, G_no played as a "
          f"genuine no, real (SEP') on {sep_pairs} pairs, end-to-end game "
          f"on {len(small)} board(s) under historical and published "
          f"constants)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
