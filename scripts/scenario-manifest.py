#!/usr/bin/env python3
"""Query scripts/scenario-manifest.json for the build script.

The manifest is the one declarative source for the evidence matrix's
scenarios and the image build wiring; this tool prints the per-image build
data as tab-separated rows so scripts/build-image.sh can loop over it instead
of restating every image by hand.  Every field is validated here with a named
diagnostic before the build reads it.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_MANIFEST = ROOT / "scripts/scenario-manifest.json"
SCHEMA = "leanos-scenario-manifest-v1"
NAME = re.compile(r"^[a-z][a-z0-9-]*$")
GRUB_CONFIGS = {"boot/grub.cfg", "boot/grub-double-fault.cfg", "boot/grub-nmi-cpl3.cfg"}
PAGE_PLAN_FLAG = re.compile(r'^-DLEANOS_BOOT_PAGE_PLAN_HEADER="([a-z0-9.-]+)"$')


class ManifestError(RuntimeError):
    pass


def load(path: Path) -> dict:
    try:
        manifest = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise ManifestError(f"scenario manifest is unreadable: {error}") from error
    if manifest.get("schema") != SCHEMA:
        raise ManifestError("scenario manifest has an unsupported schema")
    build = manifest.get("build")
    if not isinstance(build, dict) or not isinstance(build.get("images"), dict):
        raise ManifestError("scenario manifest lacks build images")
    return manifest


def image_name(stem: str) -> str:
    return stem[len("leanos-"):] if stem != "leanos" else ""


def page_plan_header(build: dict, kernel: str) -> str:
    """The page-plan header a kernel object compiles against: the value of
    its LEANOS_BOOT_PAGE_PLAN_HEADER definition, or the canonical plan."""
    header = "boot-page-plan.h"
    for flag in build["kernel_objects"].get(kernel, []):
        match = PAGE_PLAN_FLAG.match(flag)
        if match:
            header = match.group(1)
    return header


def image_rows(manifest: dict) -> list[dict[str, str]]:
    """One row per object-graph image: its objects and the page-plan header
    its kernel object compiles against."""
    build = manifest["build"]
    rows = []
    for stem, entry in build["images"].items():
        if not NAME.match(stem):
            raise ManifestError(f"image {stem!r} has an invalid name")
        kernel = entry.get("kernel")
        if kernel not in build["kernel_objects"]:
            raise ManifestError(f"image {stem} links unknown kernel object {kernel!r}")
        rows.append({
            "stem": stem,
            "name": image_name(stem),
            "boot": entry["boot"],
            "kernel": kernel,
            "page_plan": page_plan_header(build, kernel),
            "final_link": "1" if entry.get("final_link") else "0",
        })
    return rows


def packaged_rows(manifest: dict) -> list[dict[str, str]]:
    """One row per packaged final ELF: the ISO it is staged into, the GRUB
    configuration that boots it, and the final-ELF policy check queued for
    it (with an optional environment pair)."""
    build = manifest["build"]
    packaged = build.get("packaged_images")
    if not isinstance(packaged, dict) or not packaged:
        raise ManifestError("scenario manifest lacks build packaged_images")
    rows = []
    for stem, entry in packaged.items():
        if not NAME.match(stem) or not stem.startswith("leanos") or not isinstance(entry, dict):
            raise ManifestError(f"packaged image {stem!r} is malformed")
        iso = entry.get("iso")
        if not isinstance(iso, str) or not iso.startswith("leanos-@VERSION@-x86_64") or not iso.endswith(".iso"):
            raise ManifestError(f"packaged image {stem} names an invalid iso {iso!r}")
        if entry.get("grub") not in GRUB_CONFIGS:
            raise ManifestError(f"packaged image {stem} names an unknown grub config {entry.get('grub')!r}")
        row = {
            "stem": stem,
            "iso": iso,
            "iso_root": "iso" if stem == "leanos" else "iso-" + image_name(stem),
            "grub": entry["grub"],
            "policy_key": "-",
            "policy_env_name": "-",
            "policy_env_value": "-",
            "port_sites": "-",
        }
        port_sites = entry.get("port_sites")
        if port_sites is not None:
            if not re.match(r"^direct-port-sites(-[a-z0-9-]+)?\.tsv$", str(port_sites)):
                raise ManifestError(f"packaged image {stem} names a malformed port-sites inventory {port_sites!r}")
            if not (ROOT / "scripts" / port_sites).is_file():
                raise ManifestError(f"packaged image {stem} port-sites inventory is missing: {port_sites}")
            row["port_sites"] = port_sites
        policy = entry.get("policy")
        if policy is not None:
            if not isinstance(policy, dict) or not NAME.match(str(policy.get("key", ""))):
                raise ManifestError(f"packaged image {stem} policy must carry a key")
            environment = policy.get("environment")
            if environment is not None:
                if (
                    not isinstance(environment, list) or len(environment) != 2
                    or not re.match(r"^LEANOS_[A-Z0-9_]+$", str(environment[0]))
                    or not NAME.match(str(environment[1]))
                ):
                    raise ManifestError(f"packaged image {stem} policy environment must be a [name, value] pair")
                row["policy_env_name"], row["policy_env_value"] = environment
            row["policy_key"] = policy["key"]
        rows.append(row)
    keys = [row["policy_key"] for row in rows if row["policy_key"] != "-"]
    if len(keys) != len(set(keys)):
        raise ManifestError("packaged image policy keys are not unique")
    isos = [row["iso"] for row in rows]
    if len(isos) != len(set(isos)):
        raise ManifestError("packaged image iso names are not unique")
    return rows


def page_plan_stubs(manifest: dict) -> list[str]:
    """Every page-plan header a kernel object compiles against, in kernel
    object order, plus the headers the hand-linked images declare as extras."""
    build = manifest["build"]
    headers = ["boot-page-plan.h"]
    for kernel in build["kernel_objects"]:
        header = page_plan_header(build, kernel)
        if header not in headers:
            headers.append(header)
    for extra in build.get("page_plan_stub_extras", []):
        if not re.match(r"^boot-page-plan-[a-z0-9-]+\.h$", str(extra)):
            raise ManifestError(f"page-plan stub extra {extra!r} is not a plan header name")
        if extra not in headers:
            headers.append(extra)
    return headers


PLAN_CHECKS = {"validate", "converge"}
PLAN_HEADER = re.compile(r"^boot-page-plan(-[a-z0-9-]+)?\.h$")
FINAL_HEADER = re.compile(r"^boot-page-plan(-[a-z0-9-]+)?\.final\.h$")
ENVIRONMENT_NAME = re.compile(r"^LEANOS_[A-Z0-9_]+$")


def ordered_list(build: dict, key: str) -> list:
    entries = build.get(key)
    if not isinstance(entries, list) or not entries:
        raise ManifestError(f"scenario manifest lacks build {key}")
    return entries


def require_packaged(build: dict, key: str, image: str) -> None:
    if image not in build.get("packaged_images", {}):
        raise ManifestError(f"build {key} names an unpackaged image {image!r}")


def plan_check_rows(manifest: dict) -> list[dict[str, str]]:
    """The final-ELF page-plan checks in the order the build runs them: a
    validate compares an image's linker-resolved plan with its expected
    header; a converge feeds the resolved plan back through every listed
    graph target until it is stable."""
    build = manifest["build"]
    rows = []
    for entry in ordered_list(build, "plan_checks"):
        if not isinstance(entry, dict) or not {"image", "check", "expected", "final", "description"} <= set(entry):
            raise ManifestError("build plan_checks entry is malformed")
        image = str(entry["image"])
        require_packaged(build, "plan_checks", image)
        if entry["check"] not in PLAN_CHECKS:
            raise ManifestError(f"plan check for {image} has unknown kind {entry['check']!r}")
        if not PLAN_HEADER.match(str(entry["expected"])) or not FINAL_HEADER.match(str(entry["final"])):
            raise ManifestError(f"plan check for {image} names malformed plan headers")
        targets = entry.get("targets", [])
        if entry["check"] == "converge":
            if not isinstance(targets, list) or not targets:
                raise ManifestError(f"plan convergence for {image} lists no graph targets")
            for target in targets:
                if target not in build["images"]:
                    raise ManifestError(f"plan convergence for {image} names a non-graph target {target!r}")
        elif targets:
            raise ManifestError(f"plan validation for {image} must not list targets")
        rows.append({
            "image": image, "check": entry["check"], "expected": entry["expected"],
            "final": entry["final"], "description": str(entry["description"]),
            "targets": ",".join(targets) if targets else "-",
        })
    finals = [row["final"] for row in rows]
    if len(finals) != len(set(finals)):
        raise ManifestError("build plan_checks write the same final plan twice")
    return rows


def disassembly_rows(manifest: dict) -> list[dict[str, str]]:
    build = manifest["build"]
    rows = []
    for entry in ordered_list(build, "disassemblies"):
        if not isinstance(entry, dict) or set(entry) != {"image", "output"}:
            raise ManifestError("build disassemblies entry is malformed")
        require_packaged(build, "disassemblies", str(entry["image"]))
        if not re.match(r"^[a-z0-9-]+\.disassembly\.txt$", str(entry["output"])):
            raise ManifestError(f"disassembly for {entry['image']} has a malformed output name")
        rows.append({"image": entry["image"], "output": entry["output"]})
    outputs = [row["output"] for row in rows]
    if len(outputs) != len(set(outputs)):
        raise ManifestError("build disassemblies write the same output twice")
    return rows


def entry_policy_rows(manifest: dict) -> list[dict[str, str]]:
    build = manifest["build"]
    rows = []
    for entry in ordered_list(build, "entry_policies"):
        if not isinstance(entry, dict) or not {"image", "key", "report"} <= set(entry):
            raise ManifestError("build entry_policies entry is malformed")
        require_packaged(build, "entry_policies", str(entry["image"]))
        if not NAME.match(str(entry["key"])) or not re.match(r"^[a-z0-9-]+\.txt$", str(entry["report"])):
            raise ManifestError(f"entry policy for {entry['image']} has a malformed key or report")
        row = {"image": entry["image"], "key": entry["key"], "report": entry["report"], "env_name": "-", "env_value": "-"}
        environment = entry.get("environment")
        if environment is not None:
            if not isinstance(environment, list) or len(environment) != 2 or not ENVIRONMENT_NAME.match(str(environment[0])) or not NAME.match(str(environment[1])):
                raise ManifestError(f"entry policy for {entry['image']} environment must be a [name, value] pair")
            row["env_name"], row["env_value"] = environment
        rows.append(row)
    keys = [row["key"] for row in rows]
    if len(keys) != len(set(keys)):
        raise ManifestError("build entry_policies keys are not unique")
    return rows


def extended_state_policy_rows(manifest: dict) -> list[dict[str, str]]:
    build = manifest["build"]
    rows = []
    for entry in ordered_list(build, "extended_state_policies"):
        if not isinstance(entry, dict) or set(entry) != {"image", "variant", "report"}:
            raise ManifestError("build extended_state_policies entry is malformed")
        require_packaged(build, "extended_state_policies", str(entry["image"]))
        if not re.match(r"^[a-z0-9]+$", str(entry["variant"])) or not re.match(r"^[a-z0-9-]+\.txt$", str(entry["report"])):
            raise ManifestError(f"extended-state policy for {entry['image']} has a malformed variant or report")
        rows.append({"image": entry["image"], "variant": entry["variant"], "report": entry["report"]})
    return rows


COLUMNS = ("stem", "name", "boot", "kernel", "page_plan", "final_link")
PACKAGED_COLUMNS = (
    "stem", "iso", "iso_root", "grub", "policy_key", "policy_env_name", "policy_env_value",
    "port_sites",
)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    sub = parser.add_subparsers(dest="operation", required=True)
    sub.add_parser("images", help="one row per object-graph image")
    packaged = sub.add_parser("packaged-images", help="one row per packaged final ELF")
    packaged.add_argument("--version", default="0.1.0")
    sub.add_parser("page-plans", help="every page-plan header stub the build needs")
    sub.add_parser("plan-checks", help="final-ELF page-plan checks in build order")
    sub.add_parser("disassemblies", help="final-ELF disassembly outputs")
    sub.add_parser("entry-policies", help="entry-policy checks queued per final ELF")
    sub.add_parser("extended-state-policies", help="extended-state policy runs per final ELF")
    args = parser.parse_args()
    try:
        manifest = load(args.manifest)
        if args.operation == "images":
            for row in image_rows(manifest):
                print("\t".join(row[column] for column in COLUMNS))
        elif args.operation == "packaged-images":
            image_rows(manifest)
            for row in packaged_rows(manifest):
                values = [row[column] for column in PACKAGED_COLUMNS]
                values[PACKAGED_COLUMNS.index("iso")] = row["iso"].replace("@VERSION@", args.version)
                print("\t".join(values))
        elif args.operation == "page-plans":
            for header in page_plan_stubs(manifest):
                print(header)
        elif args.operation == "plan-checks":
            for row in plan_check_rows(manifest):
                print("\t".join(row[c] for c in ("image", "check", "expected", "final", "description", "targets")))
        elif args.operation == "disassemblies":
            for row in disassembly_rows(manifest):
                print(f"{row['image']}\t{row['output']}")
        elif args.operation == "entry-policies":
            for row in entry_policy_rows(manifest):
                print("\t".join(row[c] for c in ("image", "key", "report", "env_name", "env_value")))
        else:
            for row in extended_state_policy_rows(manifest):
                print(f"{row['image']}\t{row['variant']}\t{row['report']}")
    except ManifestError as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
