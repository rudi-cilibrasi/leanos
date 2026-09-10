#!/usr/bin/env python3
"""Render the versioned evidence inventory from the scenario manifest.

The existing matrix parser validates the complete result before any output is
published. This keeps runner, artifact, and PR-tier admission rules shared with
the evidence consumer.
"""

import argparse
import importlib.util
import os
from pathlib import Path
import sys
import tempfile

SCRIPT_DIR = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "emulator_evidence", SCRIPT_DIR / "run-emulator-evidence.py"
)
EVIDENCE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(EVIDENCE)
COLUMNS = (
    "id", "runner", "result_class", "timeout", "image", "elf",
    "serial_log", "scenario", "mode", "reason", "tier",
)
HEADER = "# id\trunner\tresult-class\ttimeout-seconds\timage\telf\tserial-log\tscenario\tmode\treason\ttier"


def render(manifest_path: Path) -> str:
    manifest = EVIDENCE.load_manifest(manifest_path)
    rows = []
    for scenario_id, entry in manifest["scenarios"].items():
        row = EVIDENCE.derive_row(manifest, scenario_id)
        if row is None:
            declaration = entry.get("row")
            if not isinstance(declaration, dict) or set(declaration) != set(EVIDENCE.ROW_TEMPLATE_KEYS):
                raise EVIDENCE.EvidenceError(f"scenario {scenario_id} lacks a complete matrix row")
            row = dict(declaration, id=scenario_id)
            runner = row["runner"]
            if not isinstance(runner, str) or runner not in EVIDENCE.RUNNER_RESULT_CLASSES:
                raise EVIDENCE.EvidenceError(f"scenario {scenario_id} has an unknown runner")
            row["result_class"] = EVIDENCE.RUNNER_RESULT_CLASSES[runner]
        elif "row" in entry:
            raise EVIDENCE.EvidenceError(f"scenario {scenario_id} duplicates its family matrix row")
        row["tier"] = entry.get("tier")
        for column in COLUMNS:
            value = row[column]
            if not isinstance(value, str) or not value or any(c in value for c in "\t\r\n"):
                raise EVIDENCE.EvidenceError(f"scenario {scenario_id} has invalid matrix field {column}")
        rows.append("\t".join(row[column] for column in COLUMNS))
    result = "\n".join([
        "# leanos-emulator-evidence-v2", f"# mandatory-count\t{len(rows)}",
        HEADER, *rows,
    ]) + "\n"
    with tempfile.TemporaryDirectory() as directory:
        matrix = Path(directory) / "matrix.tsv"
        matrix.write_text(result, encoding="utf-8")
        EVIDENCE.parse_matrix(matrix, manifest_path)
    return result


def publish(output: Path, result: str) -> None:
    # Concurrent build and evidence consumers may request the same
    # inventory. Publish only a complete, validated file.
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="w", encoding="utf-8", dir=output.parent,
            prefix=f".{output.name}.", delete=False,
        ) as handle:
            temporary = Path(handle.name)
            handle.write(result)
        os.replace(temporary, output)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=EVIDENCE.DEFAULT_MANIFEST)
    output = parser.add_mutually_exclusive_group()
    output.add_argument("--check", type=Path, help="reject a stale derived matrix")
    output.add_argument("--output", type=Path, help="atomically publish the derived matrix")
    args = parser.parse_args()
    try:
        result = render(args.manifest)
        if args.check is not None:
            if args.check.read_text(encoding="utf-8") != result:
                raise EVIDENCE.EvidenceError("derived evidence matrix is stale; regenerate from scenario-manifest.json")
        elif args.output is not None:
            publish(args.output, result)
        else:
            sys.stdout.write(result)
    except (EVIDENCE.EvidenceError, OSError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
