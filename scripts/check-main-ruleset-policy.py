#!/usr/bin/env python3
"""Compare the live GitHub main ruleset with the versioned admission policy."""

from __future__ import annotations

import argparse
import copy
import difflib
import json
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_POLICY = ROOT / ".github" / "main-ruleset-policy.json"


class PolicyError(RuntimeError):
    pass


def load_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise PolicyError(f"cannot read {path}: {error}") from error


def canonicalize_ruleset(ruleset: dict[str, Any]) -> dict[str, Any]:
    normalized = copy.deepcopy(ruleset)
    conditions = normalized.get("conditions", {}).get("ref_name", {})
    for key in ("include", "exclude"):
        if isinstance(conditions.get(key), list):
            conditions[key].sort()

    bypass_actors = normalized.get("bypass_actors")
    if isinstance(bypass_actors, list):
        bypass_actors.sort(key=lambda actor: json.dumps(actor, sort_keys=True))

    rules = normalized.get("rules")
    if isinstance(rules, list):
        for rule in rules:
            parameters = rule.get("parameters", {})
            methods = parameters.get("allowed_merge_methods")
            if isinstance(methods, list):
                methods.sort()
            checks = parameters.get("required_status_checks")
            if isinstance(checks, list):
                checks.sort(
                    key=lambda check: (
                        check.get("context", ""),
                        check.get("integration_id", -1),
                    )
                )
        rules.sort(key=lambda rule: rule.get("type", ""))
    return normalized


def check_policy(policy: dict[str, Any], actual: dict[str, Any]) -> list[str]:
    expected_id = policy.get("ruleset_id")
    if actual.get("id") != expected_id:
        raise PolicyError(
            f"main ruleset id drifted: expected {expected_id}, got {actual.get('id')}"
        )

    expected = policy.get("ruleset")
    if not isinstance(expected, dict):
        raise PolicyError("policy must contain a ruleset object")

    warnings: list[str] = []
    projected: dict[str, Any] = {}
    for key in expected:
        if key == "bypass_actors" and key not in actual:
            warnings.append(
                "live response omitted bypass_actors; GitHub exposes them only to "
                "tokens with ruleset write access"
            )
            continue
        projected[key] = actual.get(key)

    expected_projected = {
        key: value for key, value in expected.items() if key in projected
    }
    expected_normalized = canonicalize_ruleset(expected_projected)
    actual_normalized = canonicalize_ruleset(projected)
    if expected_normalized != actual_normalized:
        expected_text = json.dumps(expected_normalized, indent=2, sort_keys=True).splitlines()
        actual_text = json.dumps(actual_normalized, indent=2, sort_keys=True).splitlines()
        diff = "\n".join(
            difflib.unified_diff(
                expected_text,
                actual_text,
                fromfile="versioned policy",
                tofile="live ruleset",
                lineterm="",
            )
        )
        raise PolicyError(f"main admission policy drifted:\n{diff}")
    return warnings


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("actual", type=Path, help="JSON returned by GitHub's ruleset API")
    parser.add_argument("--policy", type=Path, default=DEFAULT_POLICY)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        policy = load_json(args.policy)
        actual = load_json(args.actual)
        for warning in check_policy(policy, actual):
            print(f"warning: {warning}", file=sys.stderr)
    except PolicyError as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    print("Live main admission policy matches the versioned ruleset")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
