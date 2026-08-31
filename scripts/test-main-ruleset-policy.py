#!/usr/bin/env python3
"""Regression fixtures for the versioned main-branch admission policy."""

from __future__ import annotations

import copy
import importlib.util
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
CHECKER = ROOT / "scripts" / "check-main-ruleset-policy.py"
SPEC = importlib.util.spec_from_file_location("check_main_ruleset_policy", CHECKER)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot import {CHECKER}")
policy_checker = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(policy_checker)


def expect_failure(policy: dict[str, Any], actual: dict[str, Any], needle: str) -> None:
    try:
        policy_checker.check_policy(policy, actual)
    except policy_checker.PolicyError as error:
        if needle not in str(error):
            raise AssertionError(f"missing expected diagnostic {needle!r}: {error}") from error
    else:
        raise AssertionError(f"policy mutation unexpectedly passed: {needle}")


def main() -> None:
    policy = policy_checker.load_json(policy_checker.DEFAULT_POLICY)
    actual = copy.deepcopy(policy["ruleset"])
    actual["id"] = policy["ruleset_id"]
    actual["source_type"] = "Repository"
    policy_checker.check_policy(policy, actual)

    without_queue = copy.deepcopy(actual)
    without_queue["rules"] = [
        rule for rule in without_queue["rules"] if rule["type"] != "merge_queue"
    ]
    expect_failure(policy, without_queue, '"type": "merge_queue"')

    stale_check = copy.deepcopy(actual)
    required = next(
        rule for rule in stale_check["rules"] if rule["type"] == "required_status_checks"
    )
    required["parameters"]["required_status_checks"].pop()
    expect_failure(policy, stale_check, "Hosted generated-boundary evidence")

    disabled = copy.deepcopy(actual)
    disabled["enforcement"] = "disabled"
    expect_failure(policy, disabled, '"enforcement": "active"')

    hidden_bypass = copy.deepcopy(actual)
    del hidden_bypass["bypass_actors"]
    warnings = policy_checker.check_policy(policy, hidden_bypass)
    if not warnings or "omitted bypass_actors" not in warnings[0]:
        raise AssertionError("missing limited-token bypass warning")

    audit = (ROOT / ".github" / "workflows" / "ruleset-audit.yml").read_text(
        encoding="utf-8"
    )
    for contract in (
        "schedule:",
        "workflow_dispatch:",
        "repos/${{ github.repository }}/rulesets/${RULESET_ID}",
        "python3 scripts/check-main-ruleset-policy.py",
    ):
        if contract not in audit:
            raise AssertionError(f"ruleset audit workflow lost contract: {contract}")

    print("Main ruleset policy regression fixtures passed")


if __name__ == "__main__":
    main()
