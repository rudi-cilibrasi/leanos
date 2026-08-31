#!/usr/bin/env python3
"""Validate and resolve versioned LeanOS toolchain profiles."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MANIFEST = ROOT / "scripts" / "toolchain-profiles.json"
PROFILE_ID_RE = re.compile(r"^[a-z][a-z0-9-]*$")
DIGEST_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
VERSION_LIKE_RE = re.compile(r"(?:^|[^0-9])\d+(?:\.\d+)+(?:[^0-9]|$)")
STATUS_CLAIMS = {
    "canonical": "byte-reproducible-reference",
    "supported": "semantic-compatibility",
    "candidate": "semantic-compatibility",
}
ELF_LAYOUTS = {"gcc-reference-v1", "clang18-v1"}
SHARED_TOOLS = {
    "binutils", "grub", "mtools", "xorriso", "qemu", "seabios", "coreutils"
}


class ProfileError(RuntimeError):
    pass


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise ProfileError(f"cannot read {path}: {error}") from error


def require_string(value: Any, field: str) -> str:
    if not isinstance(value, str) or not value or "\t" in value or "\n" in value:
        raise ProfileError(f"{field} must be a nonempty single-line string")
    return value


def check_manifest(data: Any, lean_toolchain: str | None = None) -> dict[str, Any]:
    if not isinstance(data, dict) or data.get("schema") != "leanos-toolchain-profiles-v1":
        raise ProfileError("toolchain profile manifest has an unrecognized schema")
    default_profile = require_string(data.get("default_profile"), "default_profile")
    profiles = data.get("profiles")
    if not isinstance(profiles, list) or len(profiles) < 2:
        raise ProfileError("toolchain profile manifest must define at least two profiles")

    by_id: dict[str, Any] = {}
    canonical: list[str] = []
    for index, profile in enumerate(profiles):
        field = f"profiles[{index}]"
        if not isinstance(profile, dict):
            raise ProfileError(f"{field} must be an object")
        profile_id = require_string(profile.get("id"), f"{field}.id")
        if not PROFILE_ID_RE.fullmatch(profile_id) or profile_id in by_id:
            raise ProfileError(f"duplicate or malformed toolchain profile id: {profile_id}")
        status = require_string(profile.get("status"), f"{profile_id}.status")
        claim = require_string(profile.get("claim"), f"{profile_id}.claim")
        if STATUS_CLAIMS.get(status) != claim:
            raise ProfileError(
                f"profile {profile_id} has incompatible status/claim: {status}/{claim}"
            )
        if status == "canonical":
            canonical.append(profile_id)

        environment = profile.get("reference_environment")
        if not isinstance(environment, dict):
            raise ProfileError(f"profile {profile_id} lacks reference_environment")
        require_string(environment.get("os"), f"{profile_id}.reference_environment.os")
        if environment.get("architecture") != "x86_64":
            raise ProfileError(f"profile {profile_id} must target x86_64")
        digest = require_string(
            environment.get("ci_image_digest"),
            f"{profile_id}.reference_environment.ci_image_digest",
        )
        if not DIGEST_RE.fullmatch(digest):
            raise ProfileError(f"profile {profile_id} has a floating CI image reference")

        selected_lean = require_string(
            profile.get("lean_toolchain"), f"{profile_id}.lean_toolchain"
        )
        if lean_toolchain is not None and selected_lean != lean_toolchain:
            raise ProfileError(
                f"profile {profile_id} Lean toolchain differs from lean-toolchain"
            )

        compiler = profile.get("compiler")
        if not isinstance(compiler, dict):
            raise ProfileError(f"profile {profile_id} lacks compiler")
        require_string(compiler.get("command"), f"{profile_id}.compiler.command")
        family = compiler.get("family")
        major = compiler.get("major")
        version = require_string(
            compiler.get("version"), f"{profile_id}.compiler.version"
        )
        package = require_string(compiler.get("package"), f"{profile_id}.compiler.package")
        if family not in {"gcc", "clang"} or not isinstance(major, int) or major < 1:
            raise ProfileError(f"profile {profile_id} has an invalid compiler identity")
        if not re.fullmatch(rf"{major}(?:\.\d+)+", version):
            raise ProfileError(f"profile {profile_id} has an invalid compiler version")
        if not VERSION_LIKE_RE.search(package) or any(
            marker in package.lower() for marker in ("latest", "rolling", "*")
        ):
            raise ProfileError(f"profile {profile_id} compiler package is not pinned")

        shared = profile.get("shared_tools")
        if not isinstance(shared, dict) or set(shared) != SHARED_TOOLS:
            raise ProfileError(f"profile {profile_id} has an incomplete shared-tool inventory")
        for tool, version in shared.items():
            pinned = require_string(version, f"{profile_id}.shared_tools.{tool}")
            if not VERSION_LIKE_RE.search(pinned) or any(
                marker in pinned.lower() for marker in ("latest", "rolling", "*")
            ):
                raise ProfileError(f"profile {profile_id} leaves {tool} unpinned")

        interfaces = profile.get("interfaces")
        if not isinstance(interfaces, dict):
            raise ProfileError(f"profile {profile_id} lacks interface versions")
        if interfaces.get("lean_c") != "restricted-generated-c-v1":
            raise ProfileError(f"profile {profile_id} has an unsupported Lean/C interface")
        if interfaces.get("direct_port_elf") not in ELF_LAYOUTS:
            raise ProfileError(f"profile {profile_id} has an unknown ELF normalization")
        by_id[profile_id] = profile

    if canonical != [default_profile]:
        raise ProfileError(
            "default_profile must be the manifest's single canonical profile"
        )
    return by_id


def compiler_version(command: str) -> str:
    try:
        result = subprocess.run(
            [command, "--version"], check=True, text=True, capture_output=True
        )
    except (OSError, subprocess.CalledProcessError) as error:
        raise ProfileError(f"cannot identify selected compiler {command}: {error}") from error
    first_line = result.stdout.splitlines()[:1]
    if not first_line:
        raise ProfileError(f"selected compiler {command} returned no version identity")
    return first_line[0]


def check_compiler(profile: dict[str, Any], version: str) -> None:
    compiler = profile["compiler"]
    family = compiler["family"]
    lowered = version.lower()
    if family == "gcc":
        family_matches = "gcc" in lowered and "clang" not in lowered
    else:
        family_matches = "clang" in lowered
    version_matches = re.search(
        rf"(?<!\d){re.escape(compiler['version'])}(?!\d)", version
    )
    if not family_matches or version_matches is None:
        raise ProfileError(
            f"selected compiler identity does not match profile {profile['id']}: {version}"
        )


def resolve(
    manifest_path: Path, profile_id: str | None, compiler_command: str | None
) -> tuple[dict[str, Any], str, str]:
    data = load_json(manifest_path)
    lean_toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    profiles = check_manifest(data, lean_toolchain)
    selected_id = profile_id or os.environ.get("LEANOS_TOOLCHAIN_PROFILE") \
        or data["default_profile"]
    if selected_id not in profiles:
        raise ProfileError(f"unknown toolchain profile: {selected_id}")
    profile = profiles[selected_id]
    command = compiler_command or os.environ.get("LEANOS_CC") \
        or profile["compiler"]["command"]
    version = compiler_version(command)
    check_compiler(profile, version)
    return profile, command, version


def artifact(
    manifest_path: Path, profile: dict[str, Any], command: str, version: str
) -> dict[str, Any]:
    resolved_manifest = manifest_path.resolve()
    try:
        displayed_manifest = resolved_manifest.relative_to(ROOT).as_posix()
    except ValueError:
        displayed_manifest = resolved_manifest.as_posix()
    return {
        "schema": "leanos-toolchain-profile-selection-v1",
        "manifest": {
            "path": displayed_manifest,
            "sha256": sha256(manifest_path),
        },
        "profile": profile,
        "observed_compiler": {"command": command, "version": version},
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("check")
    resolve_parser = subparsers.add_parser("resolve")
    resolve_parser.add_argument("--profile")
    resolve_parser.add_argument("--compiler")
    resolve_parser.add_argument("--format", choices=("json", "tsv"), default="json")
    resolve_parser.add_argument("--output", type=Path)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        if args.command == "check":
            lean_toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
            profiles = check_manifest(load_json(args.manifest), lean_toolchain)
            print(f"Toolchain profile manifest passed ({len(profiles)} profiles)")
            return 0
        profile, command, version = resolve(args.manifest, args.profile, args.compiler)
        selection = artifact(args.manifest, profile, command, version)
        rendered = json.dumps(selection, indent=2, sort_keys=True) + "\n"
        if args.output is not None:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(rendered, encoding="utf-8")
        if args.format == "tsv":
            print(
                "\t".join(
                    (
                        profile["id"],
                        profile["status"],
                        profile["claim"],
                        profile["interfaces"]["lean_c"],
                        profile["interfaces"]["direct_port_elf"],
                        sha256(args.manifest),
                        command,
                        version,
                    )
                )
            )
        elif args.output is None:
            print(rendered, end="")
        return 0
    except ProfileError as error:
        print(f"error: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
