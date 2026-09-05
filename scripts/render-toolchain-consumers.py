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
PAGES_WORKFLOW = Path(".github/workflows/pages.yml")
WORKFLOWS = (
    Path(".github/workflows/ci.yml"),
    Path(".github/workflows/release.yml"),
    PAGES_WORKFLOW,
)
CONTAINERFILE = Path("Containerfile.ci")
PACKAGE_DOC = Path("docs/boot-image.md")
PACKAGE_DOC_RE = re.compile(
    r"(?s)(<!-- BEGIN GENERATED CANONICAL APT PACKAGES -->\n).*?"
    r"(<!-- END GENERATED CANONICAL APT PACKAGES -->)"
)
APT_BLOCK_RE = re.compile(
    r"RUN apt-get update && apt-get install -y --no-install-recommends \\\n"
    r"(?P<body>(?:\s+[^\n]+\\\n)+)"
    r"\s+&& rm -rf /var/lib/apt/lists/\*"
)
APT_INSTALL_RE = re.compile(
    r"(?<![A-Za-z0-9_./-])apt(?:-get)?\b(?:(?!&&|\|\||;).)*?\binstall\b",
    re.DOTALL | re.MULTILINE,
)
APT_PACKAGE_RE = re.compile(
    r"^[a-z0-9][a-z0-9+.-]*=[0-9A-Za-z][0-9A-Za-z.+:~-]*$"
)
REQUIRED_CONTAINER_JOBS = {
    Path(".github/workflows/ci.yml"): {
        "repository-hygiene",
        "lean",
        "hosted-boundary",
        "clang-image",
        "gcc-image-family",
        "reproducibility-plan",
        "clang-reproducibility-build",
        "clang-reproducibility",
        "emulator",
        "serial-graph-parity",
    },
    Path(".github/workflows/release.yml"): {"gate"},
    PAGES_WORKFLOW: {"build-image"},
}


def canonical_digest(root: Path) -> str:
    data = json.loads((root / "scripts/toolchain-profiles.json").read_text())
    canonical = [p for p in data["profiles"] if p["status"] == "canonical"]
    if len(canonical) != 1 or canonical[0]["id"] != data["default_profile"]:
        raise ValueError("manifest does not identify one canonical default profile")
    digest = canonical[0]["reference_environment"]["ci_image_digest"]
    if re.fullmatch(r"sha256:[0-9a-f]{64}", digest) is None:
        raise ValueError("canonical CI image digest is malformed")
    return digest


def canonical_apt_packages(root: Path) -> list[str]:
    data = json.loads((root / "scripts/toolchain-profiles.json").read_text())
    packages = data.get("canonical_apt_packages")
    if not isinstance(packages, list) or len(packages) != len(set(packages)):
        raise ValueError("canonical apt package inventory is missing or duplicated")
    if any(
        not isinstance(package, str)
        or APT_PACKAGE_RE.fullmatch(package) is None
        for package in packages
    ):
        raise ValueError("canonical apt package inventory contains a floating package")
    return packages


def validate_container_packages(root: Path) -> None:
    source = (root / CONTAINERFILE).read_text(encoding="utf-8")
    install_sites = APT_INSTALL_RE.findall(source)
    if len(install_sites) != 1:
        raise ValueError(
            f"{CONTAINERFILE}: expected exactly one apt install site, "
            f"found {len(install_sites)}"
        )
    match = APT_BLOCK_RE.search(source)
    if match is None:
        raise ValueError(f"{CONTAINERFILE}: canonical apt install block is missing")
    observed = [
        line.strip().removesuffix(" \\")
        for line in match.group("body").splitlines()
    ]
    expected = canonical_apt_packages(root)
    if observed != expected:
        raise ValueError(
            f"{CONTAINERFILE}: apt package inventory differs from "
            "scripts/toolchain-profiles.json"
        )


def render_package_docs(root: Path, packages: list[str], check: bool) -> bool:
    path = root / PACKAGE_DOC
    source = path.read_text(encoding="utf-8")
    rows = ["| Package | Version |", "| --- | --- |"]
    rows.extend(
        f"| `{name}` | `{version}` |"
        for name, version in (package.split("=", 1) for package in packages)
    )
    generated = "\n".join(rows) + "\n"
    rendered, count = PACKAGE_DOC_RE.subn(rf"\g<1>{generated}\g<2>", source)
    if count != 1:
        raise ValueError(f"{PACKAGE_DOC}: expected one generated package table")
    if check:
        return rendered != source
    path.write_text(rendered, encoding="utf-8")
    return False


def validate_workflow_containers(
    path: Path,
    relative: Path,
    expected_image: str,
    expected_digest: str,
) -> None:
    document = load_workflow(path)
    env = document.get("env")
    if not isinstance(env, dict) or env.get("LEANOS_CI_IMAGE_DIGEST") != expected_digest:
        raise ValueError(f"{path}: canonical digest metadata is stale or missing")
    jobs = document.get("jobs")
    if not isinstance(jobs, dict):
        raise ValueError(f"{path}: jobs mapping is missing")
    container_jobs = {
        job_name
        for job_name, job in jobs.items()
        if isinstance(job, dict) and "container" in job
    }
    expected_jobs = REQUIRED_CONTAINER_JOBS[relative]
    if container_jobs != expected_jobs:
        missing = sorted(expected_jobs - container_jobs)
        unexpected = sorted(container_jobs - expected_jobs)
        raise ValueError(
            f"{path}: canonical container job set drifted; "
            f"missing={missing}, unexpected={unexpected}"
        )
    for job_name, job in jobs.items():
        if job_name not in expected_jobs:
            continue
        assert isinstance(job, dict)
        container = job["container"]
        if isinstance(container, dict):
            raise ValueError(
                f"{path}: job {job_name!r} must use scalar container syntax "
                "for deterministic rendering"
            )
        image = container
        if not isinstance(image, str):
            raise ValueError(f"{path}: job {job_name!r} has a malformed container image")
        if image != expected_image:
            raise ValueError(f"{path}: job {job_name!r} has a stale canonical image")


def named_steps(job: object, path: Path, job_name: str) -> dict[str, dict[str, object]]:
    if not isinstance(job, dict) or not isinstance(job.get("steps"), list):
        raise ValueError(f"{path}: job {job_name!r} has no steps")
    result: dict[str, dict[str, object]] = {}
    for step in job["steps"]:
        if not isinstance(step, dict):
            raise ValueError(f"{path}: job {job_name!r} has a malformed step")
        name = step.get("name")
        if isinstance(name, str):
            if name in result:
                raise ValueError(f"{path}: job {job_name!r} duplicates step {name!r}")
            result[name] = step
    return result


def validate_pages_pipeline(root: Path) -> None:
    path = root / PAGES_WORKFLOW
    document = load_workflow(path)
    jobs = document.get("jobs")
    if not isinstance(jobs, dict):
        raise ValueError(f"{path}: jobs mapping is missing")
    build_image = jobs.get("build-image")
    browser_build = jobs.get("build")
    if not isinstance(browser_build, dict) or browser_build.get("needs") != "build-image":
        raise ValueError(f"{path}: browser build must require the canonical image job")

    for job_name, job in jobs.items():
        if not isinstance(job, dict):
            continue
        for step in job.get("steps", []):
            if not isinstance(step, dict):
                continue
            command = step.get("run")
            if isinstance(command, str) and re.search(
                r"(?<![A-Za-z0-9_./-])apt(?:-get)?\b", command
            ):
                raise ValueError(f"{path}: mutable apt command in job {job_name!r}")

    image_steps = named_steps(build_image, path, "build-image")
    browser_steps = named_steps(browser_build, path, "build")
    create = image_steps.get("Build and bundle the canonical image", {}).get("run")
    upload = image_steps.get("Preserve revision-bound canonical image", {})
    download = browser_steps.get("Download revision-bound canonical image", {})
    verify = browser_steps.get("Verify revision-bound canonical image", {}).get("run")
    artifact_name = "leanos-pages-image-${{ github.sha }}"
    bundle_path = "build/ci/leanos-pages-image.tar.gz"
    download_path = "build/ci/pages-image"
    downloaded_bundle = f"{download_path}/leanos-pages-image.tar.gz"
    if (
        not isinstance(create, str)
        or "image-bundle.sh create" not in create
        or bundle_path not in create
    ):
        raise ValueError(f"{path}: canonical image bundle creation is missing")
    for artifact in (
        "corpus.tsv",
        "serial-protocol.sh",
        "serial-protocol.tsv",
        "SOURCE_REVISION",
        "TOOLCHAIN_PROFILE.json",
    ):
        if artifact not in create:
            raise ValueError(f"{path}: browser image bundle omits {artifact}")
    if not str(upload.get("uses", "")).startswith("actions/upload-artifact@"):
        raise ValueError(f"{path}: canonical image artifact upload is missing")
    if not isinstance(upload.get("with"), dict) or upload["with"].get("name") != artifact_name:
        raise ValueError(f"{path}: canonical image artifact upload name drifted")
    upload_paths = upload["with"].get("path")
    if not isinstance(upload_paths, str) or upload_paths.splitlines() != [
        bundle_path,
        f"{bundle_path}.sha256",
    ]:
        raise ValueError(f"{path}: canonical image artifact upload path drifted")
    if not str(download.get("uses", "")).startswith("actions/download-artifact@"):
        raise ValueError(f"{path}: canonical image artifact download is missing")
    if not isinstance(download.get("with"), dict) or download["with"].get("name") != artifact_name:
        raise ValueError(f"{path}: canonical image artifact download name drifted")
    if download["with"].get("path") != download_path:
        raise ValueError(f"{path}: canonical image artifact download path drifted")
    if (
        not isinstance(verify, str)
        or "image-bundle.sh verify" not in verify
        or downloaded_bundle not in verify
        or "${{ github.sha }}" not in verify
    ):
        raise ValueError(f"{path}: revision-bound image verification is missing")


def render(root: Path, check: bool) -> None:
    digest = canonical_digest(root)
    packages = canonical_apt_packages(root)
    expected_image = f"ghcr.io/rudi-cilibrasi/leanos-ci@{digest}"
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
        validate_workflow_containers(path, relative, expected_image, digest)
    if render_package_docs(root, packages, check):
        stale.append(str(PACKAGE_DOC))
    if stale:
        raise ValueError(
            "stale generated toolchain consumers: " + ", ".join(stale)
            + "; run scripts/render-toolchain-consumers.py"
        )
    validate_container_packages(root)
    validate_pages_pipeline(root)


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
