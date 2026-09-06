"""Pin the PUBLISHED artifact repository to the paper, the way every suite
is pinned to its final line.

Round 12 (P12-1): the artifact repo was the one artifact the battery did not
pin, and it was exactly the one that drifted — the paper printed a suite,
its table row and its counters one commit before they were pushed, so the
Data-availability paragraph was false in print for three days.

This check needs the network (GitHub API via `gh`), so it is NOT part of
`test_regressions.py` — same policy as `audit_ability_projection.py`, which
needs a VCMI checkout. Run it before tagging a release and after every
artifact push:

    python3 scripts/check_artifact_repo.py            # checks the default tag
    python3 scripts/check_artifact_repo.py --ref main

It asserts, against the given ref of github.com/uson1x/homm3-hardness:
  1. every artifact-relative path the paper cites exists in the public tree;
  2. the public `verification_manifest.json` counters equal the local ones;
  3. the public paper (main.md) is byte-identical to the local one;
  4. (round 13) every file git tracks under the artifact root is in the
     public tree with the same blob SHA, and the public tree holds nothing
     else -- the release-file hash manifest; 1. is now the readable
     diagnostic on top of it.

A failure means the paper and the published artifact disagree — push and
re-tag before submitting anything that cites the ref.

The battery's network-free little sibling lives in `test_regressions.py`:
it sweeps the same cited paths against the LOCAL tree, which catches a
renamed or deleted file at edit time; only this script catches a stale
public tree.
"""

from __future__ import annotations

import base64
import json
import os
import re
import subprocess
import sys

REPO = "uson1x/homm3-hardness"
DEFAULT_REF = "v1.2"

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


KNOWN_DIRS = ("scripts/", "empirics/scripts/")


def cited_paths(text: str | None = None, root: str = ROOT) -> set[str]:
    """Artifact-relative paths cited by the md master of the paper.

    Three citation forms, all swept (round 13, fable F-02 / codex Check 06:
    the round-12 sweep saw only backticked paths WITH a directory prefix --
    13 of the ~30 files the paper names -- and missed the fenced
    `python3 scripts/...` commands of the Reproducing block, among them
    `scripts/search_free_order.py`, the very file whose absence was the
    round-12 blocker):

      1. a backticked path with a directory prefix, `scripts/x.py`;
      2. a `python3 <path>` command anywhere in the text (the fenced block);
      3. a bare backticked basename, `x.py`, resolved against KNOWN_DIRS --
         it must resolve to exactly one existing file, or the sweep fails
         loudly rather than silently dropping the citation.

    The manifest is always included: the paper's table is rendered from it.
    """
    if text is None:
        text = open(os.path.join(root, "paper", "main.md")).read()
    out = set()
    for m in re.finditer(
            r"`((?:scripts|empirics|engine-check|proofs)/[A-Za-z0-9_./-]+"
            r"|MODEL\.md|VERIFICATION\.md|RELATED-WORK\.md)"
            r"(?:::[A-Za-z0-9_.]+)?(?: [-A-Za-z0-9 ._]*)?`", text):
        path = m.group(1)
        if path.endswith((".py", ".md", ".cpp", ".json", ".sh")):
            out.add(path)
    for m in re.finditer(r"python3 ((?:scripts|empirics/scripts)/"
                         r"[A-Za-z0-9_./-]+\.py)", text):
        out.add(m.group(1))
    for m in re.finditer(r"cd (engine-check) && (.*)", text):
        for f in re.findall(r"(?:\./|python3 )([A-Za-z0-9_.-]+\.(?:sh|py))",
                            m.group(2)):
            out.add(m.group(1) + "/" + f)
    for base in set(re.findall(r"`([a-z][a-z0-9_]*\.py)`", text)):
        hits = [d + base for d in KNOWN_DIRS
                if os.path.isfile(os.path.join(root, d, base))]
        if len(hits) != 1:
            raise SystemExit(f"cited basename `{base}` resolves to {hits} "
                             f"under {KNOWN_DIRS} -- not exactly one file")
        out.add(hits[0])
    out.add("verification_manifest.json")
    return out


def gh_json(url: str):
    res = subprocess.run(["gh", "api", url], capture_output=True, text=True)
    if res.returncode != 0:
        raise RuntimeError(f"gh api {url}: {res.stderr.strip()[:200]}")
    return json.loads(res.stdout)


def main() -> int:
    ref = DEFAULT_REF
    if "--ref" in sys.argv:
        ref = sys.argv[sys.argv.index("--ref") + 1]

    fails = []

    tree = gh_json(f"repos/{REPO}/git/trees/{ref}?recursive=1")
    if tree.get("truncated"):
        fails.append("GitHub returned a truncated tree — cannot certify")
    public = {e["path"] for e in tree.get("tree", []) if e["type"] == "blob"}

    paths = cited_paths()
    missing = sorted(p for p in paths if p not in public)
    for p in missing:
        fails.append(f"paper cites {p} but ref {ref} does not contain it")

    pub_man = gh_json(f"repos/{REPO}/contents/verification_manifest.json?ref={ref}")
    pub_counters = json.loads(base64.b64decode(pub_man["content"]))["counters"]
    loc_counters = json.loads(
        open(os.path.join(ROOT, "verification_manifest.json")).read())["counters"]
    if pub_counters != loc_counters:
        diff = {k: (loc_counters.get(k), pub_counters.get(k))
                for k in set(loc_counters) | set(pub_counters)
                if loc_counters.get(k) != pub_counters.get(k)}
        fails.append(f"manifest counters differ (local, {ref}): {diff}")

    pub_paper = gh_json(f"repos/{REPO}/contents/paper/main.md?ref={ref}")
    pub_text = base64.b64decode(pub_paper["content"])
    loc_text = open(os.path.join(ROOT, "paper", "main.md"), "rb").read()
    if pub_text != loc_text:
        fails.append(f"paper/main.md differs from ref {ref} "
                     f"({len(loc_text)} vs {len(pub_text)} bytes)")

    # 4. (round 13, codex Check 12 / finding 3) the whole tree, by content:
    #    every file git tracks under the artifact root must be in the public
    #    tree with the same blob SHA, and the public tree must hold nothing
    #    else. This is the release-file hash manifest the panel asked for;
    #    the path sweep above is now the readable diagnostic, not the pin.
    blobs = {e["path"]: e["sha"] for e in tree.get("tree", [])
             if e["type"] == "blob"}
    tracked = subprocess.run(["git", "-C", ROOT, "ls-files"],
                             capture_output=True, text=True, check=True)
    local = {}
    for rel in tracked.stdout.split():
        sha = subprocess.run(["git", "-C", ROOT, "hash-object", rel],
                             capture_output=True, text=True, check=True)
        local[rel] = sha.stdout.strip()
    for rel in sorted(set(local) - set(blobs)):
        fails.append(f"tracked file {rel} is absent from ref {ref}")
    for rel in sorted(set(blobs) - set(local)):
        fails.append(f"ref {ref} carries {rel}, which is not a tracked "
                     f"artifact file")
    differing = sorted(rel for rel in set(local) & set(blobs)
                       if local[rel] != blobs[rel])
    for rel in differing:
        fails.append(f"{rel} differs from ref {ref} (blob sha)")
    n_equal = len(set(local) & set(blobs)) - len(differing)

    if fails:
        print(f"FAILED ({len(fails)}):")
        for f in fails:
            print(f"  - {f}")
        return 1
    print(f"ALL PASS  (artifact ref {ref}: {len(paths)} cited paths present, "
          f"manifest counters equal, paper byte-identical, {n_equal} tracked "
          f"files blob-identical and nothing extra)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
