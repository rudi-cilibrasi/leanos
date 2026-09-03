#!/usr/bin/env python3
"""Render unavoidable workflow CI-image literals from the toolchain manifest."""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

from workflow_yaml import WorkflowYamlError, load_workflow


IMAGE_RE = re.compile(r"ghcr\.io/rudi-cilibrasi/leanos-ci@sha256:[0-9a-f]{64}")
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


def render(root: Path, check: bool) -> None:
    digest = canonical_digest(root)
    expected_image = f"ghcr.io/rudi-cilibrasi/leanos-ci@{digest}"
    sites = 0
    stale: list[str] = []
    for relative in WORKFLOWS:
        path = root / relative
        source = path.read_text(encoding="utf-8")
        rendered, image_count = IMAGE_RE.subn(expected_image, source)
        rendered, env_count = DIGEST_ENV_RE.subn(rf"\g<1>{digest}", rendered)
        if image_count == 0 or env_count != 1:
            raise ValueError(f"{relative}: expected container images and one digest metadata site")
        sites += image_count
        if check and rendered != source:
            stale.append(str(relative))
        elif not check:
            path.write_text(rendered, encoding="utf-8")
        # Parsing the rendered document makes malformed/duplicate workflow YAML
        # a hard failure instead of trusting formatting-sensitive replacement.
        load_workflow(path)
    if sites != 10:
        raise ValueError(f"expected 10 canonical workflow container sites, found {sites}")
    if stale:
        raise ValueError(
            "stale generated toolchain consumers: " + ", ".join(stale)
            + "; run scripts/render-toolchain-consumers.py"
        )


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
