#!/usr/bin/env python3
"""Render unavoidable workflow CI-image literals from the toolchain manifest."""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

from workflow_yaml import WorkflowYamlError, load_workflow


IMAGE_RE = re.compile(
    r"(?m)^(\s*container:\s*)"
    r"ghcr\.io/rudi-cilibrasi/leanos-ci@sha256:[0-9a-f]{64}$"
)
DIGEST_ENV_RE = re.compile(r"(?m)^(\s*LEANOS_CI_IMAGE_DIGEST:\s*)sha256:[0-9a-f]{64}$")
WORKFLOWS = (Path(".github/workflows/ci.yml"), Path(".github/workflows/release.yml"))


def canonical_digest(root: Path) -> str:
    data = json.loads((root / "scripts/toolchain-profiles.json").read_text())
    canonical = [p for p in data["profiles"] if p["status"] == "canonical"]
    if len(canonical) != 1 or canonical[0]["id"] != data["default_profile"]:
        raise ValueError("manifest does not identify one canonical default profile")
    digest = canonical[0]["reference_environment"]["ci_image_digest"]
    if re.fullmatch(r"sha256:[0-9a-f]{64}", digest) is None:
        raise ValueError("canonical CI image digest is malformed")
    return digest


def workflow_container_count(path: Path, expected_image: str, expected_digest: str) -> int:
    document = load_workflow(path)
    env = document.get("env")
    if not isinstance(env, dict) or env.get("LEANOS_CI_IMAGE_DIGEST") != expected_digest:
        raise ValueError(f"{path}: canonical digest metadata is stale or missing")
    jobs = document.get("jobs")
    if not isinstance(jobs, dict):
        raise ValueError(f"{path}: jobs mapping is missing")
    count = 0
    for job_name, job in jobs.items():
        if not isinstance(job, dict) or "container" not in job:
            continue
        container = job["container"]
        image = container.get("image") if isinstance(container, dict) else container
        if not isinstance(image, str):
            raise ValueError(f"{path}: job {job_name!r} has a malformed container image")
        if image.startswith("ghcr.io/rudi-cilibrasi/leanos-ci@"):
            if image != expected_image:
                raise ValueError(f"{path}: job {job_name!r} has a stale canonical image")
            count += 1
    return count


def render(root: Path, check: bool) -> None:
    digest = canonical_digest(root)
    expected_image = f"ghcr.io/rudi-cilibrasi/leanos-ci@{digest}"
    sites = 0
    stale: list[str] = []
    for relative in WORKFLOWS:
        path = root / relative
        source = path.read_text(encoding="utf-8")
        rendered, image_count = IMAGE_RE.subn(rf"\g<1>{expected_image}", source)
        rendered, env_count = DIGEST_ENV_RE.subn(rf"\g<1>{digest}", rendered)
        if image_count == 0 or env_count != 1:
            raise ValueError(f"{relative}: expected container images and one digest metadata site")
        if check and rendered != source:
            stale.append(str(relative))
            continue
        elif not check:
            path.write_text(rendered, encoding="utf-8")
        # Count only parsed jobs.<id>.container values. Text in comments or step
        # bodies cannot satisfy the consumer contract.
        sites += workflow_container_count(path, expected_image, digest)
    if stale:
        raise ValueError(
            "stale generated toolchain consumers: " + ", ".join(stale)
            + "; run scripts/render-toolchain-consumers.py"
        )
    if sites != 10:
        raise ValueError(f"expected 10 canonical workflow container sites, found {sites}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    try:
        render(args.root.resolve(), args.check)
    except (KeyError, OSError, ValueError, json.JSONDecodeError, WorkflowYamlError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
