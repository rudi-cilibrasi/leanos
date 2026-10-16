#!/usr/bin/env python3
"""Cancel CI runs that a newer pull-request run supersedes (issue #574).

Required checks are matched by name. When one head commit has several CI runs
(for example the `opened` and `labeled` events of a pull request created with
its label), GitHub admits the commit by the check runs of the most recent
check suite: a cancelled run in a lower suite does not block a merge (#563,
#502), but a cancelled run in the highest suite does (#547). GitHub's
`cancel-in-progress` concurrency cancels the run that queued first, which is
not always the lower suite, so pull-request runs no longer share a concurrency
group. Instead this job, run first by every pull-request CI run, cancels

  * every unfinished run of the same pull request for a different, older head
    commit (a new push supersedes it), and
  * every unfinished run for the same head commit in a lower check suite.

It never cancels its own run, a run for a newer head, or a same-head run in a
higher suite: that run is the one GitHub will admit, and its own job cancels
this one. A cancel that the token may not perform (pull requests from forks
get a read-only token) is reported and skipped; the superseded run then
finishes on its own and only costs runner time.
"""

from __future__ import annotations

import json
import os
import urllib.error
import urllib.parse
import urllib.request
from typing import Any, Iterable

UNFINISHED = {"queued", "in_progress", "waiting", "requested", "pending"}


def superseded(own: dict[str, Any], runs: Iterable[dict[str, Any]]) -> list[tuple[int, str]]:
    """Return (run id, reason) for each run `own` supersedes."""

    head_repo = (own.get("head_repository") or {}).get("full_name")
    cancel: list[tuple[int, str]] = []
    for run in runs:
        if run["id"] == own["id"] or run.get("status") not in UNFINISHED:
            continue
        if run.get("workflow_id") != own["workflow_id"] or run.get("event") != "pull_request":
            continue
        if (run.get("head_repository") or {}).get("full_name") != head_repo:
            continue
        if run.get("head_branch") != own["head_branch"]:
            continue
        if run["head_sha"] == own["head_sha"]:
            if run["check_suite_id"] < own["check_suite_id"]:
                cancel.append((run["id"], "same head in a lower check suite"))
        elif run["id"] < own["id"]:
            cancel.append((run["id"], f"older head {run['head_sha'][:12]}"))
    return cancel


def api(method: str, path: str) -> Any:
    request = urllib.request.Request(
        f"{os.environ.get('GITHUB_API_URL', 'https://api.github.com')}{path}",
        method=method,
        headers={
            "Accept": "application/vnd.github+json",
            "Authorization": f"Bearer {os.environ['GH_TOKEN']}",
            "X-GitHub-Api-Version": "2022-11-28",
        },
    )
    with urllib.request.urlopen(request, timeout=30) as response:
        body = response.read()
    return json.loads(body) if body else None


def main() -> int:
    repository = os.environ["GITHUB_REPOSITORY"]
    own = api("GET", f"/repos/{repository}/actions/runs/{os.environ['GITHUB_RUN_ID']}")
    runs: list[dict[str, Any]] = []
    for page in range(1, 4):
        listing = api(
            "GET",
            f"/repos/{repository}/actions/workflows/{own['workflow_id']}/runs"
            f"?event=pull_request&branch={urllib.parse.quote(own['head_branch'])}"
            f"&per_page=100&page={page}",
        )
        runs += listing["workflow_runs"]
        if len(listing["workflow_runs"]) < 100:
            break
    decisions = superseded(own, runs)
    print(
        f"run {own['id']} head {own['head_sha'][:12]} suite {own['check_suite_id']}: "
        f"{len(decisions)} superseded run(s)"
    )
    for run_id, reason in decisions:
        try:
            api("POST", f"/repos/{repository}/actions/runs/{run_id}/cancel")
            print(f"cancelled run {run_id}: {reason}")
        except urllib.error.HTTPError as error:
            print(f"::warning::could not cancel run {run_id} ({reason}): HTTP {error.code}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
