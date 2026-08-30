#!/usr/bin/env python3
"""Inventory and enforce LeanOS's source-level native_decide policy."""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from pathlib import Path
import re
import sys


POLICY_DOCUMENT = Path("docs/adr/0001-phase-1-scope-threat-model-and-tcb.md")
MANIFEST = Path("scripts/native-decide-modules.tsv")
POLICY_START = "<!-- native-decide-policy:start -->"
POLICY_END = "<!-- native-decide-policy:end -->"
TCB_ROW = "| `native_decide` / `Lean.ofReduceBool` native proof path |"
REQUIRED_POLICY_TERMS = (
    "`native_decide`",
    "`Lean.ofReduceBool`",
    "native evaluator",
    "kernel reduction",
    "`scripts/native-decide-modules.tsv`",
)
VALID_CATEGORIES = {
    "bounded-model": "bounded model/corpus proofs",
    "negative-fixture": "golden negative fixtures",
}
NATIVE_DECIDE = re.compile(r"\bnative_decide\b")
OF_REDUCE_BOOL = re.compile(r"\b(?:Lean\.)?ofReduceBool\b")


def strip_comments_and_strings(source: str) -> str:
    """Replace comments and strings with spaces while preserving line breaks."""
    result = list(source)
    index = 0
    block_depth = 0
    in_string = False
    in_line_comment = False

    def blank(position: int) -> None:
        if result[position] != "\n":
            result[position] = " "

    while index < len(source):
        pair = source[index : index + 2]
        if in_line_comment:
            if source[index] == "\n":
                in_line_comment = False
            else:
                blank(index)
            index += 1
            continue
        if block_depth:
            if pair == "/-":
                blank(index)
                blank(index + 1)
                block_depth += 1
                index += 2
            elif pair == "-/":
                blank(index)
                blank(index + 1)
                block_depth -= 1
                index += 2
            else:
                blank(index)
                index += 1
            continue
        if in_string:
            blank(index)
            if source[index] == "\\" and index + 1 < len(source):
                blank(index + 1)
                index += 2
            elif source[index] == '"':
                in_string = False
                index += 1
            else:
                index += 1
            continue
        if pair == "--":
            blank(index)
            blank(index + 1)
            in_line_comment = True
            index += 2
        elif pair == "/-":
            blank(index)
            blank(index + 1)
            block_depth = 1
            index += 2
        elif source[index] == '"':
            blank(index)
            in_string = True
            index += 1
        else:
            index += 1
    return "".join(result)


def lean_sources(root: Path) -> list[Path]:
    sources: list[Path] = []
    top_level = root / "LeanOS.lean"
    if top_level.is_file():
        sources.append(top_level)
    for directory in ("LeanOS", "experiments", "tests"):
        source_root = root / directory
        if source_root.is_dir():
            sources.extend(source_root.rglob("*.lean"))
    return sorted(set(sources))


def expected_category(relative: Path) -> str | None:
    parts = relative.parts
    if len(parts) >= 3 and parts[:2] == ("LeanOS", "NegativeFixtures"):
        return "negative-fixture"
    if parts and parts[0] == "LeanOS":
        return "bounded-model"
    return None


def read_manifest(root: Path, errors: list[str]) -> dict[Path, str]:
    path = root / MANIFEST
    if not path.is_file():
        errors.append(f"missing classification manifest: {MANIFEST}")
        return {}
    entries: dict[Path, str] = {}
    for line_number, raw_line in enumerate(path.read_text().splitlines(), 1):
        if not raw_line or raw_line.startswith("#"):
            continue
        fields = raw_line.split("\t")
        if len(fields) != 2:
            errors.append(f"{MANIFEST}:{line_number}: expected path<TAB>category")
            continue
        relative, category = Path(fields[0]), fields[1]
        if relative in entries:
            errors.append(f"{MANIFEST}:{line_number}: duplicate module {relative}")
        elif category not in VALID_CATEGORIES:
            errors.append(f"{MANIFEST}:{line_number}: unknown category {category}")
        else:
            expected = expected_category(relative)
            if expected != category:
                errors.append(
                    f"{MANIFEST}:{line_number}: {relative} must use category "
                    f"{expected or 'unclassified'}, not {category}"
                )
            entries[relative] = category
    return entries


def line_number(source: str, offset: int) -> int:
    return source.count("\n", 0, offset) + 1


def check_policy_document(root: Path, errors: list[str]) -> None:
    path = root / POLICY_DOCUMENT
    if not path.is_file():
        errors.append(f"missing policy document: {POLICY_DOCUMENT}")
        return
    document = path.read_text()
    if document.count(POLICY_START) != 1 or document.count(POLICY_END) != 1:
        errors.append(f"{POLICY_DOCUMENT}: native_decide policy markers are missing or duplicated")
        return
    start = document.index(POLICY_START)
    end = document.index(POLICY_END)
    if start >= end:
        errors.append(f"{POLICY_DOCUMENT}: native_decide policy markers are out of order")
        return
    policy = document[start:end]
    for term in REQUIRED_POLICY_TERMS:
        if term not in policy:
            errors.append(f"{POLICY_DOCUMENT}: native_decide policy is missing {term}")
    if document.count(TCB_ROW) != 1:
        errors.append(f"{POLICY_DOCUMENT}: dedicated native_decide TCB row is missing or duplicated")


def run(root: Path) -> int:
    errors: list[str] = []
    manifest = read_manifest(root, errors)
    check_policy_document(root, errors)
    uses: dict[Path, list[int]] = defaultdict(list)
    direct_uses: list[tuple[Path, int]] = []

    for source_path in lean_sources(root):
        relative = source_path.relative_to(root)
        source = strip_comments_and_strings(source_path.read_text())
        for match in NATIVE_DECIDE.finditer(source):
            uses[relative].append(line_number(source, match.start()))
        for match in OF_REDUCE_BOOL.finditer(source):
            direct_uses.append((relative, line_number(source, match.start())))
            errors.append(
                f"{relative}:{line_number(source, match.start())}: direct ofReduceBool use is "
                "unclassified; use an approved tactic or amend the TCB policy"
            )

    for relative in sorted(uses):
        if relative not in manifest:
            locations = ",".join(str(number) for number in uses[relative])
            errors.append(
                f"{relative}:{locations}: native_decide module is not classified in {MANIFEST}"
            )
    for relative in sorted(manifest):
        if relative not in uses:
            errors.append(f"{MANIFEST}: stale classification for {relative}")

    category_uses: Counter[str] = Counter()
    category_modules: Counter[str] = Counter()
    for relative, locations in uses.items():
        category = manifest.get(relative)
        if category in VALID_CATEGORIES:
            category_uses[category] += len(locations)
            category_modules[category] += 1

    print("native_decide trust inventory (comments and strings excluded)")
    for category, description in VALID_CATEGORIES.items():
        print(
            f"  {category}: {category_uses[category]} uses in "
            f"{category_modules[category]} modules ({description})"
        )
    print(f"  total: {sum(len(locations) for locations in uses.values())} uses in {len(uses)} modules")
    print("  modules:")
    for relative in sorted(uses):
        print(f"    {relative}: {len(uses[relative])}")
    print(f"  direct Lean.ofReduceBool source uses: {len(direct_uses)} (0 required)")

    if errors:
        for error in errors:
            print(f"native_decide policy error: {error}", file=sys.stderr)
        return 1
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root",
        type=Path,
        default=Path(__file__).resolve().parents[1],
        help=argparse.SUPPRESS,
    )
    arguments = parser.parse_args()
    return run(arguments.root.resolve())


if __name__ == "__main__":
    raise SystemExit(main())
