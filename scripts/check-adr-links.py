#!/usr/bin/env python3
"""Reject duplicate ADR numbers and broken repository-local ADR links."""

from __future__ import annotations

from collections import defaultdict
from pathlib import Path
import re
import sys
from urllib.parse import unquote


ROOT = Path(__file__).resolve().parent.parent
ADR_DIR = ROOT / "docs" / "adr"
ADR_NAME = re.compile(r"^(\d{4})-[a-z0-9][a-z0-9-]*\.md$")
MARKDOWN_LINK = re.compile(r"\[[^\]]+\]\(([^)]+)\)")


def fail(message: str) -> None:
    print(f"error: {message}", file=sys.stderr)


def check(root: Path) -> int:
    errors = 0
    adr_dir = root / "docs" / "adr"
    numbers: dict[str, list[Path]] = defaultdict(list)

    for path in sorted(adr_dir.glob("*.md")):
        match = ADR_NAME.fullmatch(path.name)
        if match is None:
            fail(f"malformed ADR filename: {path.relative_to(root)}")
            errors += 1
            continue
        numbers[match.group(1)].append(path)

    for number, paths in sorted(numbers.items()):
        if len(paths) > 1:
            rendered = ", ".join(str(path.relative_to(root)) for path in paths)
            fail(f"duplicate ADR number {number}: {rendered}")
            errors += 1

    for source in sorted(root.rglob("*.md")):
        if any(part in {".git", "build"} for part in source.parts):
            continue
        text = source.read_text(encoding="utf-8")
        for raw_target in MARKDOWN_LINK.findall(text):
            target = raw_target.strip().strip("<>").split("#", 1)[0]
            if not target or "://" in target or target.startswith("mailto:"):
                continue
            decoded = unquote(target)
            resolved = (source.parent / decoded).resolve()
            try:
                resolved.relative_to(adr_dir.resolve())
            except ValueError:
                continue
            if not resolved.exists():
                fail(
                    f"broken ADR link in {source.relative_to(root)}: {raw_target}"
                )
                errors += 1

    if errors:
        return 1
    print(f"ADR numbering and links OK ({len(numbers)} decisions)")
    return 0


def main() -> int:
    if len(sys.argv) > 2:
        fail("usage: check-adr-links.py [repository-root]")
        return 2
    root = Path(sys.argv[1]).resolve() if len(sys.argv) == 2 else ROOT
    return check(root)


if __name__ == "__main__":
    raise SystemExit(main())
