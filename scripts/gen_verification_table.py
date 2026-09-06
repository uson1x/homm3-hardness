#!/usr/bin/env python3
"""Render the paper's verification table from verification_manifest.json.

Round-8 review (codex leg) recommendation: the table's rows drifted from the
artifacts twice, because every number was retyped by hand in two files. Now
the numbers live once, in ../verification_manifest.json, and this script
renders the Markdown and LaTeX tables from it, between marker comments:

    <!-- verification-table:begin -->  /  <!-- verification-table:end -->
    % verification-table:begin        /  % verification-table:end

Modes:
    python3 gen_verification_table.py            # CHECK: exit 1 + diff if the
                                                 # files differ from the render
    python3 gen_verification_table.py --write    # rewrite the marked regions

test_regressions.py runs the check mode as part of the doc-consistency
battery, so an edit to the table that bypasses the manifest fails the suite.
Placeholders: `{name}` where `name` is a key of the manifest's `counters`
map is substituted; every other brace (LaTeX, set notation) is left alone —
which is why str.format is deliberately NOT used here.
"""

from __future__ import annotations

import difflib
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
MANIFEST = ROOT / "verification_manifest.json"
MD = ROOT / "paper" / "main.md"
TEX = ROOT / "paper" / "main.tex"

MD_BEGIN = "<!-- verification-table:begin -->"
MD_END = "<!-- verification-table:end -->"
TEX_BEGIN = "% verification-table:begin"
TEX_END = "% verification-table:end"


def load_manifest() -> dict:
    return json.loads(MANIFEST.read_text())


def substitute(cell: str, counters: dict) -> str:
    def repl(m: re.Match) -> str:
        name = m.group(1)
        if name in counters:
            return str(counters[name])
        return m.group(0)          # a LaTeX brace group, not a placeholder

    out = re.sub(r"\{([a-z_][a-z0-9_]*)\}", repl, cell)
    # round 9 (harness): a TYPO'D placeholder used to pass through silently
    # and render literal braces into both papers. Round 10 (fable) broadened
    # the net: the old pattern required an underscore, so {mechanicschecks}
    # (a typo WITHOUT one) still slipped through. Now every bare lowercase
    # brace-word is an error unless it is on the explicit allowlist of
    # legitimate LaTeX brace groups used by the templates.
    # \src{hold} and \textbf{published} in the tex templates
    allowed = {"hold", "published"}
    for leftover in re.finditer(r"\{([a-z][a-z0-9_]*)\}", out):
        if leftover.group(1) not in allowed:
            raise SystemExit(
                f"unresolved counter placeholder {{{leftover.group(1)}}} in "
                f"manifest cell {cell!r} — not a key of the manifest's "
                f"counters (add to the allowlist only for a genuine LaTeX "
                f"brace group)")
    return out


def placeholder_cells(cells: list[str], counters: dict) -> list[list[str]]:
    """Counter names per cell, in template order (non-counter brace groups —
    LaTeX macros — are not placeholders and are skipped). Kept per cell:
    round 12 (P12-7) showed that a flat, concatenated sequence lets a counter
    move across a cell boundary, putting the same number in different table
    columns of the md and tex renders."""
    return [[n for n in re.findall(r"\{([a-z_][a-z0-9_]*)\}", cell)
             if n in counters]
            for cell in cells]


def placeholder_sequence(cells: list[str], counters: dict) -> list[str]:
    """The flattened per-cell sequence (what the manifest declares)."""
    return [n for cell in placeholder_cells(cells, counters) for n in cell]


def validate_placeholders(manifest: dict) -> None:
    """Round-11 P11-1/2: the digit audit below let two mutations through —
    a counter retyped as a digit that row already declared in `literals`,
    and two placeholders swapped inside one row (sets don't see order).
    Every row now declares `placeholders`: the exact ordered sequence of
    counter names its templates carry. The md cells, the tex cells and the
    declaration must all agree; a retyped counter drops out of the
    sequence, a swap changes its order — both fail here."""
    counters = manifest["counters"]
    problems = []
    for row in manifest["rows"]:
        declared = row.get("placeholders")
        if declared is None:
            problems.append(f"row {row['id']}: no `placeholders` declaration")
            continue
        unknown = [n for n in declared if n not in counters]
        if unknown:
            problems.append(f"row {row['id']}: declared placeholders "
                            f"{unknown} are not manifest counters")
        for kind in ("md", "tex"):
            got = placeholder_sequence(row.get(kind, []), counters)
            if got != declared:
                problems.append(
                    f"row {row['id']}: {kind} placeholder sequence {got} != "
                    f"declared {declared}")
        # round 12 (P12-7): the md and tex CELLS must agree placeholder-for-
        # placeholder, not just their concatenations — a counter moved
        # across a cell boundary in one render only is a different table.
        md_cells = placeholder_cells(row.get("md", []), counters)
        tex_cells = placeholder_cells(row.get("tex", []), counters)
        if md_cells != tex_cells:
            problems.append(
                f"row {row['id']}: md cells carry placeholders {md_cells} "
                f"but tex cells carry {tex_cells} — the two renders would "
                f"put a number in different columns")
    if problems:
        raise SystemExit("placeholder-sequence audit failed:\n  " +
                         "\n  ".join(problems))


# LaTeX macros the tex templates use that HIDE or carry digits. Expanded
# before the literal audit so the tex mirror can be held to the SAME
# multiset as the md master (round 13, fable F-05 D3/D4: "tex may carry
# fewer" let a tex-only deletion of `41` and a tex-only 27<->41 swap render
# a false PDF table under a green battery).
TEX_DIGIT_MACROS = {
    r"\\THREEPART(?:\{\})?": "3-PARTITION",
    r"\\PARTITION(?:\{\})?": "PARTITION",
}
# Section labels the tex cells reference where the md master carries the
# section NUMBER. The audit resolves them here, explicitly, so that md and
# tex are held to one multiset; an unlisted label fails the audit rather
# than silently vanishing (that is what "tex may carry fewer" amounted to).
TEX_REF_NUMBERS = {"sec:design": "5.1", "sec:floats": "4.2"}

# A digit-run, with its sign when the sign is a free-standing minus (start
# of cell, whitespace or an opening bracket before it) -- round 13, codex
# Check 05: `12` -> `-12` passed an unsigned audit. A hyphen inside a word
# (`round-8`, `I1-I4`, `12/16/20`) is not a sign.
LITERAL_RE = re.compile(r"(?:(?<=^)|(?<=[\s(\[]))-\d+(?:\.\d+)?|\d+(?:\.\d+)?")


def literal_runs(cell: str, kind: str) -> list[str]:
    """The signed digit-runs of one template cell outside its placeholders."""
    stripped = re.sub(r"\{[a-z_][a-z0-9_]*\}", "", cell)
    if kind == "tex":
        for macro, expansion in TEX_DIGIT_MACROS.items():
            stripped = re.sub(macro, expansion, stripped)

        def ref(m):
            label = m.group(1)
            if label not in TEX_REF_NUMBERS:
                raise SystemExit(f"tex cell references label {label!r}, not "
                                 f"in TEX_REF_NUMBERS -- add it with the "
                                 f"section number the md master prints")
            return TEX_REF_NUMBERS[label]
        stripped = re.sub(r"\\ref\{([^}]*)\}", ref, stripped)
    return LITERAL_RE.findall(stripped)


def validate_literals(manifest: dict) -> None:
    """Round-10 B6: a counter retyped as a literal digit in a row template
    used to render fine and drift silently. Every digit-run a template
    carries outside {placeholders} must be declared in that row's
    `literals` allowlist (constants like `def 41`, file names like `x3c`,
    section numbers). Round 12 (P12-7): the audit is MULTISET equality
    for the md master -- set equality was blind to deleting one occurrence
    of a digit that appears twice -- with one `literals` entry per md
    occurrence. Round 13 (F-05, Check 05): the tex mirror is held to the
    SAME per-cell literal SEQUENCE after expanding the digit-carrying
    macros it uses (TEX_DIGIT_MACROS, TEX_REF_NUMBERS) -- "fewer is fine"
    let tex-only deletions and swaps through -- and digit-runs are read
    with a free-standing sign."""
    from collections import Counter

    problems = []
    for row in manifest["rows"]:
        counts = {kind: Counter(run for cell in row.get(kind, [])
                                for run in literal_runs(cell, kind))
                  for kind in ("md", "tex")}
        declared = Counter(row.get("literals", []))
        if counts["md"] != declared:
            problems.append(
                f"row {row['id']}: md digit-runs {dict(counts['md'])} "
                f"!= declared literals {dict(declared)}")
        # the tex mirror is held cell by cell, IN ORDER, to the md master
        # (a multiset would still pass a tex-only 27<->41 swap, F-05 D4)
        md_seq = [literal_runs(c, "md") for c in row.get("md", [])]
        tex_seq = [literal_runs(c, "tex") for c in row.get("tex", [])]
        if md_seq != tex_seq:
            problems.append(
                f"row {row['id']}: per-cell literal sequences differ -- md "
                f"{md_seq} vs tex {tex_seq} (after macro expansion)")
    if problems:
        raise SystemExit("literal-digit audit failed:\n  " +
                         "\n  ".join(problems))


def render_md(manifest: dict) -> str:
    counters = manifest["counters"]
    lines = ["| suite | scale | outcome |", "|---|---|---|"]
    for row in manifest["rows"]:
        cells = [substitute(c, counters) for c in row["md"]]
        lines.append("| " + " | ".join(cells) + " |")
    return "\n".join(lines)


def render_tex(manifest: dict) -> str:
    counters = manifest["counters"]
    lines = []
    for row in manifest["rows"]:
        cells = [substitute(c, counters) for c in row["tex"]]
        lines.append(" & ".join(cells) + " \\\\")
    return "\n".join(lines)


def region(text: str, begin: str, end: str, path: Path) -> tuple[int, int]:
    """Character offsets of the region BETWEEN the marker lines."""
    i = text.find(begin)
    j = text.find(end)
    if i < 0 or j < 0 or j < i:
        raise SystemExit(f"{path}: markers '{begin}' / '{end}' not found or "
                         f"out of order — the table region is gone")
    start = text.index("\n", i) + 1
    stop = text.rindex("\n", start, j) + 1
    return start, stop


def process(path: Path, begin: str, end: str, rendered: str,
            write: bool) -> bool:
    text = path.read_text()
    start, stop = region(text, begin, end, path)
    current = text[start:stop]
    wanted = rendered + "\n"
    if current == wanted:
        return True
    if write:
        path.write_text(text[:start] + wanted + text[stop:])
        print(f"rewrote the verification table in {path.name}")
        return True
    sys.stderr.write(f"{path.name}: verification table differs from the "
                     f"manifest render:\n")
    for line in difflib.unified_diff(current.splitlines(), wanted.splitlines(),
                                     "current", "manifest", lineterm=""):
        sys.stderr.write(line + "\n")
    return False


def main() -> int:
    write = "--write" in sys.argv[1:]
    manifest = load_manifest()
    validate_placeholders(manifest)
    validate_literals(manifest)
    ok_md = process(MD, MD_BEGIN, MD_END, render_md(manifest), write)
    ok_tex = process(TEX, TEX_BEGIN, TEX_END, render_tex(manifest), write)
    if ok_md and ok_tex:
        if not write:
            print("OK: both verification tables match the manifest render")
        return 0
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
