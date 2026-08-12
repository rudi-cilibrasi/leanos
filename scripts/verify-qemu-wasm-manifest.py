#!/usr/bin/env python3
"""Fail-closed validation for the issue #194 qemu-wasm build manifest."""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import re
import sys


ROOT = pathlib.Path(__file__).resolve().parent.parent
DEFAULT_MANIFEST = ROOT / "browser-runtime" / "manifest-v1.json"
DEFAULT_EVIDENCE = (
    ROOT / "browser-runtime" / "provisional-source-build-evidence-v1.json"
)
DOCKERFILE = ROOT / "browser-runtime" / "Dockerfile"
BUILD_SCRIPT = ROOT / "scripts" / "build-qemu-wasm-source.sh"
HEX40 = re.compile(r"^[0-9a-f]{40}$")
HEX64 = re.compile(r"^[0-9a-f]{64}$")
OUTPUTS = {
    "qemu-system-x86_64.js",
    "qemu-system-x86_64.wasm",
    "qemu-system-x86_64.worker.js",
    "TOOLCHAIN.txt",
    "BUILD_COMMANDS.txt",
    "PATCHES.json",
    "SHA256SUMS",
}
LICENSE_COMPONENTS = {
    "qemu-wasm",
    "qemu-wasm libraries",
    "zlib",
    "libffi",
    "glib",
    "pcre2",
    "pixman",
    "meson",
    "xterm-pty",
    "dtc",
    "keycodemapdb",
    "berkeley-softfloat-3",
    "berkeley-testfloat-3",
}
REQUIRED_RELEASE_ASSET_CLASSES = {
    "wasm",
    "javascript-glue",
    "worker",
    "firmware",
    "terminal",
    "service-worker",
    "preload",
    "browser-harness",
    "license-bundle",
    "build-log",
    "tool-versions",
    "patch-inventory",
    "browser-evidence",
}


def fail(message: str) -> None:
    raise ValueError(message)


def unique(items: list[dict], field: str, label: str) -> dict[str, dict]:
    result: dict[str, dict] = {}
    for item in items:
        key = item.get(field)
        if not isinstance(key, str) or not key:
            fail(f"{label} has missing {field}")
        if key in result:
            fail(f"duplicate {label} {key}")
        result[key] = item
    return result


def require_hash(value: object, label: str, pattern: re.Pattern[str] = HEX64) -> None:
    if not isinstance(value, str) or pattern.fullmatch(value) is None:
        fail(f"{label} is not a lowercase immutable hash")


def flat_regular_file_inventory(staging: pathlib.Path) -> set[str]:
    entries = list(staging.iterdir())
    invalid = sorted(
        entry.name for entry in entries if entry.is_symlink() or not entry.is_file()
    )
    if invalid:
        fail(f"staging contains non-regular entries: {invalid}")
    return {entry.name for entry in entries}


def validate_inputs(data: dict) -> None:
    if data.get("schema") != "leanos-qemu-wasm-runtime/v1":
        fail("unexpected manifest schema")
    if data.get("issue") != 194:
        fail("manifest is not scoped to issue 194")

    acceptance = data.get("acceptance", {})
    if acceptance.get("ready") is not False:
        fail("prototype input lock must remain acceptance.ready=false")
    pending_gate = acceptance.get("pending_gate", {})
    if (
        pending_gate.get("name") != "source-built-browser-acceptance"
        or not pending_gate.get("required_result")
    ):
        fail("prototype must preserve the source-built browser acceptance gate")
    resolved_by = acceptance.get("resolved_by", {})
    if resolved_by.get("issue") != 193 or resolved_by.get("pr") != 221:
        fail("prototype must preserve the resolved #193/#221 media decision")

    host = data.get("host", {})
    container = data.get("toolchain", {}).get("container", {})
    if host.get("architecture") != "x86_64":
        fail("only the recorded x86_64 host is supported")
    if host.get("container_platform") != "linux/amd64":
        fail("unexpected host container platform")
    if container.get("platform") != "linux/amd64":
        fail("container platform must be linux/amd64")
    if container.get("version") != "3.1.50":
        fail("Emscripten container version changed")
    digest = container.get("digest")
    if not isinstance(digest, str) or not digest.startswith("sha256:"):
        fail("container is not digest-pinned")
    require_hash(digest.removeprefix("sha256:"), "container digest")

    sources = unique(data.get("sources", []), "name", "source")
    if set(sources) != {
        "qemu-wasm",
        "LeanOS",
        "dtc",
        "keycodemapdb",
        "berkeley-softfloat-3",
        "berkeley-testfloat-3",
    }:
        fail("source inventory is incomplete or contains undeclared sources")
    require_hash(sources["qemu-wasm"].get("revision"), "qemu-wasm revision", HEX40)
    require_hash(sources["qemu-wasm"].get("tree"), "qemu-wasm tree", HEX40)
    require_hash(sources["LeanOS"].get("revision"), "LeanOS revision", HEX40)
    require_hash(sources["dtc"].get("revision"), "dtc revision", HEX40)
    require_hash(sources["dtc"].get("tree"), "dtc tree", HEX40)
    require_hash(
        sources["keycodemapdb"].get("revision"), "keycodemapdb revision", HEX40
    )
    require_hash(sources["keycodemapdb"].get("tree"), "keycodemapdb tree", HEX40)
    for name in ("berkeley-softfloat-3", "berkeley-testfloat-3"):
        require_hash(sources[name].get("revision"), f"{name} revision", HEX40)
        require_hash(sources[name].get("tree"), f"{name} tree", HEX40)
    if sources["LeanOS"].get("protocol_source") != "scripts/run-image.sh":
        fail("LeanOS acceptance must reuse scripts/run-image.sh")
    if sources["LeanOS"].get("expected_debug_exit_status") != 33:
        fail("LeanOS expected debug-exit status must be 33")

    dependencies = unique(data.get("dependencies", []), "name", "dependency")
    expected_dependencies = {
        "zlib",
        "libffi",
        "glib",
        "pcre2-meson-fallback",
        "pixman",
        "meson",
        "xterm-pty",
    }
    if set(dependencies) != expected_dependencies:
        fail("dependency inventory is incomplete or contains undeclared inputs")
    for name, dependency in dependencies.items():
        if not dependency.get("version") or not dependency.get("url"):
            fail(f"dependency {name} is not versioned with a source URL")
        require_hash(dependency.get("sha256"), f"{name} SHA-256")
        if not dependency.get("license"):
            fail(f"dependency {name} has no license identifier")
    pcre = dependencies["pcre2-meson-fallback"]
    if not pcre.get("patch_url"):
        fail("pcre2 Meson fallback patch URL is missing")
    require_hash(pcre.get("patch_sha256"), "pcre2 Meson patch SHA-256")

    apt = data.get("toolchain", {}).get("apt_top_level")
    if not isinstance(apt, list) or not apt:
        fail("apt top-level dependency inventory is empty")
    if any(not isinstance(item, str) or "=" not in item for item in apt):
        fail("every apt top-level package must have an exact version")
    apt_snapshot = data.get("toolchain", {}).get("apt_snapshot", {})
    expected_snapshot = {
        "url": "https://snapshot.ubuntu.com/ubuntu",
        "timestamp": "20260206T000000Z",
        "distribution": "jammy",
        "pockets": ["jammy", "jammy-updates", "jammy-security"],
        "components": ["main", "universe"],
    }
    if apt_snapshot != expected_snapshot:
        fail("APT snapshot identity differs from the reviewed immutable input")

    configuration = data.get("configuration", {})
    if configuration.get("target_list") != "x86_64-softmmu":
        fail("only the x86-64 system target is in scope")
    configure_args = configuration.get("configure_arguments", [])
    required_args = {
        "--static",
        "--target-list=x86_64-softmmu",
        "--cpu=wasm32",
        "--without-default-features",
        "--enable-system",
        "--with-coroutine=fiber",
        "--enable-virtfs",
    }
    if not required_args.issubset(set(configure_args)):
        fail("configure argument inventory is incomplete")
    if any(
        not isinstance(argument, str)
        or re.fullmatch(r"--[a-z0-9-]+(?:=[A-Za-z0-9_./+-]*)?", argument) is None
        for argument in configure_args
    ):
        fail("configure argument inventory contains an unsafe argument")
    expected_configure_command = (
        "emconfigure /src/configure "
        + " ".join(configure_args)
        + ' --extra-cflags="$EXTRA_CFLAGS"'
        + ' --extra-cxxflags="$EXTRA_CFLAGS"'
        + ' --extra-ldflags="$EXTRA_LDFLAGS"'
    )
    if configuration.get("configure_command") != expected_configure_command:
        fail("configure command differs from its argument inventory")
    if configuration.get("build_command") != "emmake make -j1 qemu-system-x86_64":
        fail("build command is not the deterministic single-job command")
    for key in ("extra_cflags", "extra_ldflags"):
        if not configuration.get(key):
            fail(f"configuration {key} is missing")

    patches = data.get("patches")
    if not isinstance(patches, list):
        fail("patch inventory must be a list")
    for index, patch in enumerate(patches):
        if set(patch) != {"path", "sha256", "upstream_status"}:
            fail(f"patch {index} does not have the complete explicit inventory")
        require_hash(patch.get("sha256"), f"patch {index} SHA-256")
        patch_path = ROOT / patch["path"]
        if not patch_path.is_file():
            fail(f"patch file is missing: {patch['path']}")
        if hashlib.sha256(patch_path.read_bytes()).hexdigest() != patch["sha256"]:
            fail(f"patch hash differs: {patch['path']}")
        if patch["path"] not in BUILD_SCRIPT.read_text():
            fail(f"build script does not apply declared patch: {patch['path']}")

    licenses = unique(data.get("licenses", []), "component", "license")
    if set(licenses) != LICENSE_COMPONENTS:
        fail("license inventory is incomplete or contains undeclared components")
    for component, license_entry in licenses.items():
        if not license_entry.get("identifier") or not license_entry.get("notice_source"):
            fail(f"license entry {component} is incomplete")

    outputs = unique(data.get("outputs", []), "path", "output")
    if set(outputs) != OUTPUTS:
        fail("prototype output inventory is incomplete or contains extra files")
    for path, output in outputs.items():
        if not output.get("role"):
            fail(f"output {path} has no role")
        if output.get("sha256") is not None or output.get("size") is not None:
            fail("prototype output hashes must stay unresolved until two clean builds pass")
    if not data.get("deferred_outputs"):
        fail("prototype must list outputs deferred on browser acceptance")

    dockerfile = DOCKERFILE.read_text()
    expected_base = (
        f"{container['image']}:{container['version']}@{container['digest']}"
    )
    if f"FROM {expected_base}" not in dockerfile:
        fail("Dockerfile base does not match the manifest container identity")
    for dependency in dependencies.values():
        if dependency["sha256"] not in dockerfile:
            fail(f"Dockerfile does not enforce {dependency['name']} SHA-256")
    if pcre["patch_sha256"] not in dockerfile:
        fail("Dockerfile does not enforce the pcre2 patch SHA-256")
    for package in apt:
        if package not in dockerfile:
            fail(f"Dockerfile does not exact-pin apt package {package}")
    if (
        f"ARG UBUNTU_SNAPSHOT_URL={apt_snapshot['url']}" not in dockerfile
        or f"ARG UBUNTU_SNAPSHOT={apt_snapshot['timestamp']}" not in dockerfile
    ):
        fail("Dockerfile APT snapshot does not match the manifest")
    for pocket in apt_snapshot["pockets"]:
        if f" {pocket} main universe" not in dockerfile:
            fail(f"Dockerfile does not configure APT snapshot pocket {pocket}")
    if "Acquire::Check-Valid-Until=false" not in dockerfile:
        fail("Dockerfile does not permit the immutable APT snapshot timestamp")

    forbidden = ("qemu-wasm-demo/docs/images", "qemu-system-x86_64.wasm\" \"$")
    implementation = dockerfile + "\n" + BUILD_SCRIPT.read_text()
    for marker in forbidden:
        if marker in implementation:
            fail(f"source build contains forbidden prebuilt marker: {marker}")


def validate_release(data: dict, staging: pathlib.Path | None) -> None:
    if data.get("acceptance", {}).get("ready") is not True:
        fail("release manifest is blocked: acceptance.ready is not true")
    if data.get("deferred_outputs"):
        fail("release manifest still has deferred outputs")
    outputs = unique(data.get("outputs", []), "path", "output")
    asset_classes: set[str] = set()
    for path, output in outputs.items():
        asset_class = output.get("asset_class")
        if not isinstance(asset_class, str) or not asset_class:
            fail(f"output {path} has no asset class")
        asset_classes.add(asset_class)
        require_hash(output.get("sha256"), f"output {path} SHA-256")
        size = output.get("size")
        if not isinstance(size, int) or size < 0:
            fail(f"output {path} has no exact size")
    missing_asset_classes = REQUIRED_RELEASE_ASSET_CLASSES - asset_classes
    if missing_asset_classes:
        fail(
            "release output asset classes are incomplete: "
            f"missing={sorted(missing_asset_classes)}"
        )
    if staging is None:
        return
    observed = flat_regular_file_inventory(staging)
    if observed != set(outputs):
        fail(
            "staging inventory differs from manifest: "
            f"missing={sorted(set(outputs) - observed)} "
            f"extra={sorted(observed - set(outputs))}"
        )
    for path, output in outputs.items():
        artifact = staging / path
        digest = hashlib.sha256(artifact.read_bytes()).hexdigest()
        if digest != output["sha256"] or artifact.stat().st_size != output["size"]:
            fail(f"staged output differs from manifest: {path}")


def validate_prototype(
    data: dict,
    manifest: pathlib.Path,
    staging: pathlib.Path | None,
    comparison: pathlib.Path | None,
) -> None:
    if data.get("acceptance", {}).get("ready") is not False:
        fail("prototype validation requires acceptance.ready=false")
    if staging is None:
        fail("prototype validation requires --staging")
    outputs = unique(data.get("outputs", []), "path", "output")
    expected = set(outputs)
    observed = flat_regular_file_inventory(staging)
    if observed != expected:
        fail(
            "prototype inventory differs from manifest: "
            f"missing={sorted(expected - observed)} "
            f"extra={sorted(observed - expected)}"
        )

    checksum_paths = expected - {"SHA256SUMS"}
    checksum_lines = (staging / "SHA256SUMS").read_text().splitlines()
    checksums: dict[str, str] = {}
    for line in checksum_lines:
        match = re.fullmatch(r"([0-9a-f]{64})  ([^/]+)", line)
        if match is None:
            fail("prototype SHA256SUMS is not canonical")
        digest, path = match.groups()
        if path in checksums:
            fail(f"duplicate prototype checksum: {path}")
        checksums[path] = digest
    if set(checksums) != checksum_paths:
        fail("prototype checksum inventory differs from manifest")
    for path, digest in checksums.items():
        observed_digest = hashlib.sha256((staging / path).read_bytes()).hexdigest()
        if observed_digest != digest:
            fail(f"prototype output differs from SHA256SUMS: {path}")

    manifest_digest = hashlib.sha256(manifest.read_bytes()).hexdigest()
    commands = (staging / "BUILD_COMMANDS.txt").read_text()
    if f"manifest-sha256: {manifest_digest}\n" not in commands:
        fail("prototype build command evidence has the wrong manifest hash")
    configuration = data["configuration"]
    for label, value in (
        ("configure", configuration["configure_command"]),
        ("build", configuration["build_command"]),
    ):
        if f"{label}: {value}\n" not in commands:
            fail(f"prototype build command evidence has the wrong {label} command")

    patches = json.loads((staging / "PATCHES.json").read_text())
    if patches != data["patches"]:
        fail("prototype patch evidence differs from manifest")
    toolchain = (staging / "TOOLCHAIN.txt").read_text()
    emscripten = data["toolchain"]["emscripten"]
    if emscripten["version"] not in toolchain or emscripten["revision"] not in toolchain:
        fail("prototype toolchain evidence has the wrong Emscripten identity")

    if comparison is not None:
        comparison_observed = {
            path.name for path in comparison.iterdir() if path.is_file()
        }
        if comparison_observed != expected:
            fail("comparison inventory differs from manifest")
        for path in outputs:
            if (staging / path).read_bytes() != (comparison / path).read_bytes():
                fail(f"clean builds are not byte-identical: {path}")


def validate_evidence(
    data: dict,
    evidence: dict,
    manifest: pathlib.Path,
    staging: pathlib.Path | None,
    comparison: pathlib.Path | None,
) -> None:
    if evidence.get("schema") != "leanos-qemu-wasm-source-build-evidence/v1":
        fail("unexpected source-build evidence schema")
    if evidence.get("issue") != 194 or evidence.get("acceptance_ready") is not False:
        fail("source-build evidence has the wrong acceptance scope")
    manifest_digest = hashlib.sha256(manifest.read_bytes()).hexdigest()
    if evidence.get("manifest_sha256") != manifest_digest:
        fail("source-build evidence has the wrong manifest hash")
    if evidence.get("clean_builds") != 2 or evidence.get("comparison") != "byte-identical":
        fail("source-build evidence does not record two byte-identical builds")
    require_hash(
        str(evidence.get("container_image_id", "")).removeprefix("sha256:"),
        "source-build container image ID",
    )
    outputs = unique(data.get("outputs", []), "path", "output")
    evidence_outputs = unique(evidence.get("outputs", []), "path", "evidence output")
    if set(evidence_outputs) != set(outputs):
        fail("source-build evidence output inventory differs from manifest")
    for path, output in evidence_outputs.items():
        require_hash(output.get("sha256"), f"evidence output {path} SHA-256")
        if not isinstance(output.get("size"), int) or output["size"] < 0:
            fail(f"evidence output {path} has no exact size")
    if staging is None:
        return
    validate_prototype(data, manifest, staging, comparison)
    for path, output in evidence_outputs.items():
        artifact = staging / path
        if (
            hashlib.sha256(artifact.read_bytes()).hexdigest() != output["sha256"]
            or artifact.stat().st_size != output["size"]
        ):
            fail(f"prototype output differs from source-build evidence: {path}")


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--inputs", action="store_true")
    mode.add_argument("--prototype", action="store_true")
    mode.add_argument("--evidence", action="store_true")
    mode.add_argument("--release", action="store_true")
    parser.add_argument("--manifest", type=pathlib.Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--evidence-file", type=pathlib.Path, default=DEFAULT_EVIDENCE)
    parser.add_argument("--staging", type=pathlib.Path)
    parser.add_argument("--compare", type=pathlib.Path)
    args = parser.parse_args()
    try:
        data = json.loads(args.manifest.read_text())
        if args.inputs:
            validate_inputs(data)
        elif args.prototype:
            validate_prototype(data, args.manifest, args.staging, args.compare)
        elif args.evidence:
            evidence = json.loads(args.evidence_file.read_text())
            validate_evidence(data, evidence, args.manifest, args.staging, args.compare)
        else:
            validate_release(data, args.staging)
    except (OSError, json.JSONDecodeError, ValueError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    selected_mode = (
        "inputs"
        if args.inputs
        else "prototype"
        if args.prototype
        else "evidence"
        if args.evidence
        else "release"
    )
    print(f"validated {args.manifest} ({selected_mode})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
