#!/usr/bin/env python3
"""Fixtures for the pull-request run supersession rule (issue #574)."""

from __future__ import annotations

import importlib.util
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "ci_supersede_runs", ROOT / "scripts" / "ci-supersede-runs.py"
)
assert SPEC is not None and SPEC.loader is not None
module = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = module
SPEC.loader.exec_module(module)


def run(run_id, sha, suite, status="in_progress", **overrides):
    record = {
        "id": run_id,
        "head_sha": sha,
        "check_suite_id": suite,
        "status": status,
        "workflow_id": 7,
        "event": "pull_request",
        "head_branch": "feature",
        "head_repository": {"full_name": "owner/repo"},
    }
    record.update(overrides)
    return record


own = run(20, "b" * 40, 500)


def ids(runs):
    return [run_id for run_id, _ in module.superseded(own, runs)]


# #547: the opened and labeled runs of one head; the run in the lower suite is
# cancelled by the run in the higher suite, never the other way around.
assert ids([own, run(21, "b" * 40, 400)]) == [21]
assert ids([own, run(19, "b" * 40, 600)]) == []
# A push supersedes every unfinished run of an older head, whatever its suite.
assert ids([run(10, "a" * 40, 900), run(11, "a" * 40, 100, status="queued")]) == [10, 11]
# A newer head is never cancelled by an older one.
assert ids([run(30, "c" * 40, 100)]) == []
# Finished runs, other workflows, events, branches, and fork heads are left alone.
assert ids([
    run(12, "a" * 40, 100, status="completed"),
    run(13, "a" * 40, 100, workflow_id=8),
    run(14, "a" * 40, 100, event="push"),
    run(15, "a" * 40, 100, head_branch="other"),
    run(16, "a" * 40, 100, head_repository={"full_name": "fork/repo"}),
    run(17, "b" * 40, 100, head_repository=None),
]) == []
for status in sorted(module.UNFINISHED):
    assert ids([run(18, "a" * 40, 100, status=status)]) == [18], status
# The run itself is never in its own cancel list.
assert ids([own]) == []

print("CI run supersession fixtures passed")
