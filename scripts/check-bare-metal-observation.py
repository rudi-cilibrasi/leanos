#!/usr/bin/env python3
"""Validate bounded bare-metal observation metadata without network tooling."""

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import re
import sys


RFC3339_UTC = re.compile(
    r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(?:\.\d+)?Z"
)


def fail(reason: str) -> None:
    raise ValueError(reason)


def parse_utc(value: str, field: str) -> datetime:
    if RFC3339_UTC.fullmatch(value) is None:
        fail(f"{field}: expected UTC RFC3339 timestamp")
    try:
        parsed = datetime.fromisoformat(value[:-1] + "+00:00")
    except ValueError:
        fail(f"{field}: invalid timestamp")
    if parsed.tzinfo != timezone.utc:
        fail(f"{field}: expected UTC RFC3339 timestamp")
    return parsed


def validate(observation_path: Path, schema_path: Path) -> None:
    observation = json.loads(observation_path.read_text(encoding="utf-8"))
    schema = json.loads(schema_path.read_text(encoding="utf-8"))
    if not isinstance(observation, dict) or schema.get("type") != "object":
        fail("observation: expected object")

    properties = schema["properties"]
    required = set(schema["required"])
    keys = set(observation)
    if missing := sorted(required - keys):
        fail(f"observation: missing fields: {','.join(missing)}")
    if extra := sorted(keys - set(properties)):
        fail(f"observation: unexpected fields: {','.join(extra)}")

    for name, value in observation.items():
        rule = properties[name]
        if "const" in rule and value != rule["const"]:
            fail(f"{name}: invalid constant")
        expected_type = rule.get("type")
        if expected_type == "string":
            if not isinstance(value, str):
                fail(f"{name}: expected string")
            if len(value) < rule.get("minLength", 0):
                fail(f"{name}: too short")
            if len(value) > rule.get("maxLength", sys.maxsize):
                fail(f"{name}: too long")
            if rule.get("format") == "date-time":
                parse_utc(value, name)
        elif expected_type == "integer":
            if not isinstance(value, int) or isinstance(value, bool):
                fail(f"{name}: expected integer")
            if value < rule.get("minimum", value):
                fail(f"{name}: below minimum")
            if value > rule.get("maximum", value):
                fail(f"{name}: above maximum")

    started = parse_utc(observation["startedAtUtc"], "startedAtUtc")
    ended = parse_utc(observation["endedAtUtc"], "endedAtUtc")
    if ended < started:
        fail("endedAtUtc: precedes startedAtUtc")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("observation", type=Path)
    parser.add_argument(
        "--schema",
        type=Path,
        default=Path(__file__).resolve().parents[1]
        / "docs"
        / "bare-metal-observation.schema.json",
    )
    args = parser.parse_args()
    try:
        validate(args.observation, args.schema)
    except (OSError, json.JSONDecodeError, KeyError, TypeError, ValueError) as error:
        print(f"bare-metal-observation: invalid: {error}", file=sys.stderr)
        return 1
    print("bare-metal-observation: valid")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
