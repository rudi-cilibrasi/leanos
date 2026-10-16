#!/usr/bin/env python3
"""Delete restored Lake outputs whose Lean source no longer exists.

CI lanes other than the proof-timing lane restore the newest Lake cache of the
same platform and CI image when no cache matches their exact Lean inputs
(issue #574). Lake rebuilds every module whose source, imports, or toolchain
trace changed, so a stale output never stands in for changed source. One case
remains: a module whose source a change deleted keeps its old `.olean` in the
restored tree, and `lake env lean` could still import it. This removes every
module output under `.lake/build/{lib/lean,ir}` without a matching `.lean`
source, so a restored cache holds no module a clean build would lack.
"""

from __future__ import annotations

import argparse
from pathlib import Path


def module_source(output: Path, root: Path) -> Path:
    """Map `.lake/build/lib/lean/A/B.olean.hash` to `A/B.lean`."""

    relative = output.relative_to(root)
    return relative.with_name(relative.name.split(".", 1)[0] + ".lean")


def prune(repo: Path) -> list[Path]:
    removed: list[Path] = []
    for tree in ("lib/lean", "ir"):
        root = repo / ".lake" / "build" / tree
        if not root.is_dir():
            continue
        for output in sorted(path for path in root.rglob("*") if path.is_file()):
            if not (repo / module_source(output, root)).is_file():
                output.unlink()
                removed.append(output)
        for directory in sorted(
            (path for path in root.rglob("*") if path.is_dir()), reverse=True
        ):
            if not any(directory.iterdir()):
                directory.rmdir()
    return removed


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repo", type=Path, nargs="?", default=Path("."))
    args = parser.parse_args()
    removed = prune(args.repo)
    for path in removed:
        print(f"pruned {path}")
    print(f"Lake output pruning removed {len(removed)} file(s) without a Lean source")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
