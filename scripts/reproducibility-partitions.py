#!/usr/bin/env python3
"""Plan and fail-closed aggregation for independent reproducibility shards."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys


SCHEMA = "leanos-reproducibility-partitions-v1"
DIGEST = re.compile(r"[0-9a-f]{64}")
REVISION = re.compile(r"[0-9a-f]{40}")


def fail(message: str) -> None:
    raise ValueError(message)


def canonical_digest(value: object) -> str:
    encoded = json.dumps(value, separators=(",", ":"), sort_keys=True).encode()
    return hashlib.sha256(encoded).hexdigest()


def read_artifacts(path: Path) -> list[str]:
    artifacts = [line.strip() for line in path.read_text().splitlines() if line.strip()]
    if not artifacts:
        fail("artifact list is empty")
    if len(artifacts) != len(set(artifacts)):
        fail("artifact list contains duplicates")
    if any(item.startswith("/") or ".." in Path(item).parts for item in artifacts):
        fail("artifact path escapes the build root")
    return sorted(artifacts)


def make_plan(args: argparse.Namespace) -> dict[str, object]:
    if not REVISION.fullmatch(args.source_revision):
        fail("invalid source revision")
    if not args.toolchain_id or any(character.isspace() for character in args.toolchain_id):
        fail("invalid toolchain identity")
    artifacts = read_artifacts(args.artifacts)
    if args.partitions < 1 or args.partitions > len(artifacts):
        fail("partition count must be between one and the artifact count")
    artifact_manifest_digest = hashlib.sha256(
        ("\n".join(artifacts) + "\n").encode()
    ).hexdigest()
    partitions = [
        {"id": index, "artifacts": artifacts[index :: args.partitions]}
        for index in range(args.partitions)
    ]
    plan: dict[str, object] = {
        "schemaVersion": SCHEMA,
        "sourceRevision": args.source_revision,
        "toolchainId": args.toolchain_id,
        "artifactManifestDigest": artifact_manifest_digest,
        "partitions": partitions,
    }
    plan["planDigest"] = canonical_digest(plan)
    return plan


def load_json(path: Path) -> dict[str, object]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        fail(f"{path}: expected a JSON object")
    return value


def verify_artifact_manifest(
    plan: dict[str, object], partitions: list[object]
) -> None:
    artifacts: list[str] = []
    for partition in partitions:
        if not isinstance(partition, dict):
            fail("invalid partition")
        partition_artifacts = partition.get("artifacts")
        if (
            not isinstance(partition_artifacts, list)
            or not partition_artifacts
            or not all(isinstance(artifact, str) for artifact in partition_artifacts)
        ):
            fail("partition has invalid artifacts")
        artifacts.extend(partition_artifacts)
    if len(artifacts) != len(set(artifacts)):
        fail("partition plan contains duplicate artifacts")
    expected = hashlib.sha256(
        ("\n".join(sorted(artifacts)) + "\n").encode()
    ).hexdigest()
    if plan.get("artifactManifestDigest") != expected:
        fail("artifact manifest digest mismatch")


def make_result(args: argparse.Namespace) -> dict[str, object]:
    plan = load_json(args.plan)
    plan_digest = plan.pop("planDigest", None)
    if not isinstance(plan_digest, str) or plan_digest != canonical_digest(plan):
        fail("plan digest mismatch")
    if plan.get("schemaVersion") != SCHEMA:
        fail("unsupported plan schema")
    partitions = plan.get("partitions")
    if not isinstance(partitions, list):
        fail("plan has no partitions")
    verify_artifact_manifest(plan, partitions)
    matches = [
        partition
        for partition in partitions
        if isinstance(partition, dict) and partition.get("id") == args.partition
    ]
    if len(matches) != 1:
        fail(f"unknown partition: {args.partition}")
    artifacts = matches[0].get("artifacts")
    if not isinstance(artifacts, list) or not artifacts or not all(
        isinstance(artifact, str) for artifact in artifacts
    ):
        fail("partition has invalid artifacts")
    digests: dict[str, str] = {}
    build_root = args.build_root.resolve(strict=True)
    for artifact in artifacts:
        path = build_root / artifact
        cursor = build_root
        for component in Path(artifact).parts:
            cursor /= component
            if cursor.is_symlink():
                fail(f"partition artifact is a symlink: {artifact}")
        try:
            resolved = path.resolve(strict=True)
        except OSError:
            fail(f"partition artifact is missing: {artifact}")
        if not resolved.is_relative_to(build_root):
            fail(f"partition artifact escapes the build root: {artifact}")
        if not resolved.is_file():
            fail(f"partition artifact is not a regular file: {artifact}")
        digests[artifact] = hashlib.sha256(resolved.read_bytes()).hexdigest()
    return {
        "partition": args.partition,
        "sourceRevision": plan.get("sourceRevision"),
        "toolchainId": plan.get("toolchainId"),
        "artifactManifestDigest": plan.get("artifactManifestDigest"),
        "planDigest": plan_digest,
        "artifacts": digests,
    }


def verify(args: argparse.Namespace) -> str:
    plan = load_json(args.plan)
    plan_digest = plan.pop("planDigest", None)
    if not isinstance(plan_digest, str) or plan_digest != canonical_digest(plan):
        fail("plan digest mismatch")
    if plan.get("schemaVersion") != SCHEMA:
        fail("unsupported plan schema")
    partitions = plan.get("partitions")
    if not isinstance(partitions, list) or not partitions:
        fail("plan has no partitions")
    verify_artifact_manifest(plan, partitions)
    expected = {}
    for partition in partitions:
        if not isinstance(partition, dict):
            fail("invalid partition")
        identifier = partition.get("id")
        artifacts = partition.get("artifacts")
        if not isinstance(identifier, int) or identifier in expected:
            fail("duplicate or invalid partition id")
        if not isinstance(artifacts, list) or not artifacts:
            fail("partition has no artifacts")
        expected[identifier] = artifacts

    observed: dict[str, str] = {}
    seen: set[int] = set()
    for result_path in args.results:
        result = load_json(result_path)
        identifier = result.get("partition")
        if not isinstance(identifier, int) or identifier not in expected:
            fail(f"{result_path}: unknown partition")
        if identifier in seen:
            fail(f"duplicate partition result: {identifier}")
        seen.add(identifier)
        for field in (
            "sourceRevision",
            "toolchainId",
            "artifactManifestDigest",
        ):
            if result.get(field) != plan.get(field):
                fail(f"partition {identifier}: {field} mismatch")
        if result.get("planDigest") != plan_digest:
            fail(f"partition {identifier}: planDigest mismatch")
        artifacts = result.get("artifacts")
        if not isinstance(artifacts, dict) or sorted(artifacts) != sorted(expected[identifier]):
            fail(f"partition {identifier}: artifact set mismatch")
        for artifact, digest in artifacts.items():
            if artifact in observed:
                fail(f"duplicate artifact result: {artifact}")
            if not isinstance(digest, str) or not DIGEST.fullmatch(digest):
                fail(f"partition {identifier}: invalid digest for {artifact}")
            observed[artifact] = digest
    missing = sorted(set(expected) - seen)
    if missing:
        fail(f"missing partition results: {','.join(map(str, missing))}")
    return "".join(f"{observed[path]}  {path}\n" for path in sorted(observed))


def main() -> int:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)
    plan_parser = subparsers.add_parser("plan")
    plan_parser.add_argument("artifacts", type=Path)
    plan_parser.add_argument("--partitions", type=int, required=True)
    plan_parser.add_argument("--source-revision", required=True)
    plan_parser.add_argument("--toolchain-id", required=True)
    result_parser = subparsers.add_parser("result")
    result_parser.add_argument("plan", type=Path)
    result_parser.add_argument("--partition", type=int, required=True)
    result_parser.add_argument("--build-root", type=Path, required=True)
    verify_parser = subparsers.add_parser("verify")
    verify_parser.add_argument("plan", type=Path)
    verify_parser.add_argument("results", type=Path, nargs="+")
    args = parser.parse_args()
    try:
        if args.command == "plan":
            print(json.dumps(make_plan(args), indent=2, sort_keys=True))
        elif args.command == "result":
            print(json.dumps(make_result(args), indent=2, sort_keys=True))
        else:
            sys.stdout.write(verify(args))
    except (OSError, ValueError, json.JSONDecodeError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
