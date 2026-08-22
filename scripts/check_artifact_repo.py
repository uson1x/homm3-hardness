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
  3. the public paper (main.md) is byte-identical to the local one.

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
DEFAULT_REF = "v1.1"

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def cited_paths() -> set[str]:
    """Artifact-relative paths cited by the md master of the paper."""
    text = open(os.path.join(ROOT, "paper", "main.md")).read()
    out = set()
    for m in re.finditer(
            r"`((?:scripts|empirics|engine-check|proofs)/[A-Za-z0-9_./-]+"
            r"|MODEL\.md|VERIFICATION\.md|RELATED-WORK\.md)"
            r"(?:::[A-Za-z0-9_.]+)?(?: [-A-Za-z0-9 ._]*)?`", text):
        path = m.group(1)
        if path.endswith((".py", ".md", ".cpp", ".json", ".sh")):
            out.add(path)
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

    if fails:
        print(f"FAILED ({len(fails)}):")
        for f in fails:
            print(f"  - {f}")
        return 1
    print(f"ALL PASS  (artifact ref {ref}: {len(paths)} cited paths present, "
          f"manifest counters equal, paper byte-identical)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
