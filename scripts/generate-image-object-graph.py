#!/usr/bin/env python3
"""Generate the shared and variant C-object portion of the image Make graph."""

from __future__ import annotations

import argparse
import re
import json
from pathlib import Path
import shlex


GENERATED_MODULES = (
    "KernelTransition",
    "Syscall",
    "IPCSyscall",
    "Preemption",
    "BootAllocation",
    "BootMemoryMapStreaming",
    "BootMemoryMapStreamAuthority",
    "BootTopology",
    "Interrupt",
    "InterruptEntry",
    "BlockingIPC",
    "CapabilityReuse",
    "ExtendedState",
    "PrivilegeEntryControl",
    "FaultDispatch",
    "DirectPortIO",
    "StaleTranslation",
    "FrameBudgetScenario",
    "CompositeDispatcher",
    "VTdBootPlan",
    "IOTLB",
)

BOOT_ALLOCATION_PARTS = (
    "BootAllocation",
    "BootMemoryMapStreaming",
    "BootMemoryMapStreamAuthority",
    "BootTopology",
)

FAULT_DISPATCH_PARTS = (
    "FaultDispatch",
    "DirectPortIO",
    "StaleTranslation",
    "FrameBudgetScenario",
    "CompositeDispatcher",
    "VTdBootPlan",
    "IOTLB",
)

DEFAULT_MANIFEST = Path(__file__).resolve().parent / "scenario-manifest.json"
MANIFEST_SCHEMA = "leanos-scenario-manifest-v1"
OBJECT_NAME = re.compile(r"^[a-z][a-z0-9-]*$")


def load_build_manifest(path: Path = DEFAULT_MANIFEST) -> dict:
    """The build-variant wiring declared once in scripts/scenario-manifest.json:
    kernel objects with their macro sets, boot objects, the images linked from
    them, and the policy-negative fixtures.  Every table this generator used
    to restate as Python literals is derived from it."""
    try:
        manifest = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise SystemExit(f"error: scenario manifest is unreadable: {error}") from error
    if manifest.get("schema") != MANIFEST_SCHEMA:
        raise SystemExit("error: scenario manifest has an unsupported schema")
    build = manifest.get("build")
    if not isinstance(build, dict):
        raise SystemExit("error: scenario manifest lacks a build section")
    for key in ("kernel_objects", "boot_objects", "images", "policy_fixtures"):
        if not isinstance(build.get(key), dict) or not build[key]:
            raise SystemExit(f"error: scenario manifest build.{key} is missing or empty")
    for name, definitions in build["kernel_objects"].items():
        if not OBJECT_NAME.match(name) or not isinstance(definitions, list) or not all(
            isinstance(flag, str) and flag.startswith("-D") for flag in definitions
        ):
            raise SystemExit(f"error: scenario manifest kernel object {name!r} is malformed")
    for name, entry in build["boot_objects"].items():
        if (
            not OBJECT_NAME.match(name)
            or not isinstance(entry, dict)
            or set(entry) != {"source", "definitions"}
            or not str(entry["source"]).endswith(".S")
            or not all(isinstance(flag, str) and flag.startswith("-D") for flag in entry["definitions"])
        ):
            raise SystemExit(f"error: scenario manifest boot object {name!r} is malformed")
    for section, required in (("images", {"boot", "kernel", "extra_objects", "final_link"}), ("policy_fixtures", {"boot", "kernel", "extra_objects"})):
        for stem, entry in build[section].items():
            if not OBJECT_NAME.match(stem) or not stem.startswith("leanos") or not isinstance(entry, dict) or set(entry) != required:
                raise SystemExit(f"error: scenario manifest {section} entry {stem!r} is malformed")
            if entry["boot"] not in build["boot_objects"]:
                raise SystemExit(f"error: image {stem} links unknown boot object {entry['boot']!r}")
            if entry["kernel"] not in build["kernel_objects"]:
                raise SystemExit(f"error: image {stem} links unknown kernel object {entry['kernel']!r}")
            for extra in entry["extra_objects"]:
                if extra not in build["boot_objects"]:
                    raise SystemExit(f"error: image {stem} links unknown extra object {extra!r}")
            if section == "images" and not isinstance(entry["final_link"], bool):
                raise SystemExit(f"error: image {stem} final_link must be true or false")
    return build


def image_name(stem: str) -> str:
    return stem[len("leanos-"):] if stem != "leanos" else ""


def variant_tables(build: dict) -> tuple[tuple, tuple, tuple, tuple, tuple]:
    kernel = tuple((name, tuple(defs)) for name, defs in build["kernel_objects"].items())
    assembly = tuple(
        (name, entry["source"], tuple(entry["definitions"]))
        for name, entry in build["boot_objects"].items()
    )
    prelink = tuple(
        (image_name(stem), entry["boot"], entry["kernel"], tuple(entry["extra_objects"]))
        for stem, entry in build["images"].items()
    )
    final = tuple(
        (image_name(stem), entry["boot"], entry["kernel"], tuple(entry["extra_objects"]))
        for stem, entry in build["images"].items()
        if entry["final_link"]
    )
    fixtures = tuple(
        (image_name(stem), entry["boot"], entry["kernel"], tuple(entry["extra_objects"]))
        for stem, entry in build["policy_fixtures"].items()
    )
    return kernel, assembly, prelink, final, fixtures


BUILD_MANIFEST = load_build_manifest()
(
    KERNEL_VARIANTS,
    ASSEMBLY_VARIANTS,
    PRELINK_VARIANTS,
    FINAL_LINK_VARIANTS,
    POLICY_FIXTURE_VARIANTS,
) = variant_tables(BUILD_MANIFEST)


COMMON_LINK_OBJECTS = (
    "KernelTransition",
    "Syscall",
    "IPCSyscall",
    "Preemption",
    "BootAllocation",
    "Interrupt",
    "InterruptEntry",
    "BlockingIPC",
    "CapabilityReuse",
    "ExtendedState",
    "PrivilegeEntryControl",
    "FaultDispatch",
)

# Start the link graph with the canonical image and the authority-boundary
# fixtures that use the same boot object.  The tuple order is the reviewed
# linker input order and must remain stable for byte-identity evidence.
def make_escape(value: str) -> str:
    return value.replace("$", "$$").replace(" ", "\\ ").replace("#", "\\#")


def shell_join(arguments: list[str]) -> str:
    return " ".join(shlex.quote(argument) for argument in arguments)


def render_graph(
    build_dir: Path,
    cc: str,
    cflags: list[str],
    lean_prefix: Path,
    source_root: Path,
    return_corruptions: list[tuple[str, int]] | None = None,
    tables: tuple[tuple, tuple, tuple, tuple, tuple] | None = None,
) -> str:
    return_corruptions = return_corruptions or []
    kernel_variants, assembly_variants, prelink_variants, final_link_variants, policy_fixture_variants = (
        tables
        if tables is not None
        else (KERNEL_VARIANTS, ASSEMBLY_VARIANTS, PRELINK_VARIANTS, FINAL_LINK_VARIANTS, POLICY_FIXTURE_VARIANTS)
    )
    build = make_escape(str(build_dir))
    compile_flags = shell_join([*cflags, f"-I{lean_prefix / 'include'}"])
    lines = [
        "# Generated by scripts/generate-image-object-graph.py; do not edit.",
        f"IMAGE_CC := {shlex.quote(cc)}",
        f"IMAGE_CFLAGS := {compile_flags}",
        f"IMAGE_LINKER_SCRIPT := {make_escape(str(source_root / 'boot/linker.ld'))}",
        "",
    ]

    combined = set(BOOT_ALLOCATION_PARTS) | set(FAULT_DISPATCH_PARTS)
    for module in GENERATED_MODULES:
        object_name = f"{module}.part.o" if module in combined else f"{module}.o"
        target = f"{build}/{object_name}"
        depfile = f"{target}.d"
        lines.extend(
            [
                f"{target} {depfile} &: {build}/{module}.c",
                f"\t$(IMAGE_CC) $(IMAGE_CFLAGS) -MMD -MP -MF {depfile} -c $< -o {target}",
            ]
        )

    boot_inputs = " ".join(
        f"{build}/{module}.part.o" for module in BOOT_ALLOCATION_PARTS
    )
    fault_inputs = " ".join(
        f"{build}/{module}.part.o" for module in FAULT_DISPATCH_PARTS
    )
    lines.extend(
        [
            f"{build}/BootAllocation.o: {boot_inputs}",
            "\tld -r $^ -o $@",
            f"{build}/FaultDispatch.o: {fault_inputs}",
            "\tld -r $^ -o $@",
            "",
            ".PHONY: shared-generated-objects",
            "shared-generated-objects: "
            + " ".join(
                f"{build}/{module}.o"
                for module in GENERATED_MODULES
                if module not in combined
            )
            + f" {build}/BootAllocation.o {build}/FaultDispatch.o",
            "",
            "-include "
            + " ".join(
                f"{build}/{module}.{'part.o' if module in combined else 'o'}.d"
                for module in GENERATED_MODULES
            ),
            "",
        ]
    )
    kernel_source = make_escape(str(source_root / "boot/kernel.c"))
    kernel_flags = [*cflags, f"-I{build_dir}", "-Wall", "-Wextra", "-Werror"]
    for name, definitions in kernel_variants:
        target = f"{build}/{name}.o"
        depfile = f"{target}.d"
        arguments = shell_join([*kernel_flags, *definitions])
        lines.extend(
            [
                f"{target} {depfile} &: {kernel_source}",
                "\t@set -e; "
                f"tmp_target={target}.tmp; tmp_dep={depfile}.tmp; "
                "trap 'rm -f \"$$tmp_target\" \"$$tmp_dep\"' EXIT; "
                f"$(IMAGE_CC) {arguments} -MMD -MP -MF \"$$tmp_dep\" "
                f"-MT {target} -MT {depfile} -c $< -o \"$$tmp_target\"; "
                f"if [ -f {target} ] && [ -f {depfile} ] && "
                f"cmp -s \"$$tmp_target\" {target} && "
                f"cmp -s \"$$tmp_dep\" {depfile}; then :; else "
                f"mv \"$$tmp_target\" {target}; mv \"$$tmp_dep\" {depfile}; fi",
            ]
        )
    return_prelink_kernel_names = []
    return_final_kernel_names = []
    for fixture, mode in return_corruptions:
        name = f"kernel-return-{fixture}-prelink"
        target = f"{build}/{name}.o"
        depfile = f"{target}.d"
        arguments = shell_join([
            *kernel_flags, f"-DLEANOS_RETURN_CORRUPTION_MODE={mode}",
        ])
        lines.extend(
            [
                f"{target} {depfile} &: {kernel_source}",
                "\t@set -e; "
                f"tmp_target={target}.tmp; tmp_dep={depfile}.tmp; "
                "trap 'rm -f \"$$tmp_target\" \"$$tmp_dep\"' EXIT; "
                f"$(IMAGE_CC) {arguments} -MMD -MP -MF \"$$tmp_dep\" "
                f"-MT {target} -MT {depfile} -c $< -o \"$$tmp_target\"; "
                f"if [ -f {target} ] && [ -f {depfile} ] && "
                f"cmp -s \"$$tmp_target\" {target} && "
                f"cmp -s \"$$tmp_dep\" {depfile}; then :; else "
                f"mv \"$$tmp_target\" {target}; mv \"$$tmp_dep\" {depfile}; fi",
            ]
        )
        return_prelink_kernel_names.append(name)
        final_name = f"kernel-return-{fixture}"
        final_target = f"{build}/{final_name}.o"
        final_depfile = f"{final_target}.d"
        final_arguments = shell_join([
            *kernel_flags,
            f"-DLEANOS_RETURN_CORRUPTION_MODE={mode}",
            f'-DLEANOS_BOOT_PAGE_PLAN_HEADER="boot-page-plan-return-{fixture}.h"',
        ])
        lines.extend(
            [
                f"{final_target} {final_depfile} &: {kernel_source} {build}/boot-page-plan-return-{fixture}.h",
                "\t@set -e; "
                f"tmp_target={final_target}.tmp; tmp_dep={final_depfile}.tmp; "
                "trap 'rm -f \"$$tmp_target\" \"$$tmp_dep\"' EXIT; "
                f"$(IMAGE_CC) {final_arguments} -MMD -MP -MF \"$$tmp_dep\" "
                f"-MT {final_target} -MT {final_depfile} -c $< -o \"$$tmp_target\"; "
                f"if [ -f {final_target} ] && [ -f {final_depfile} ] && "
                f"cmp -s \"$$tmp_target\" {final_target} && "
                f"cmp -s \"$$tmp_dep\" {final_depfile}; then :; else "
                f"mv \"$$tmp_target\" {final_target}; "
                f"mv \"$$tmp_dep\" {final_depfile}; fi",
            ]
        )
        return_final_kernel_names.append(final_name)
    lines.extend(
        [
            "",
            ".PHONY: variant-kernel-objects final-kernel-objects",
            "variant-kernel-objects: "
            + " ".join(
                f"{build}/{name}.o"
                for name in [
                    *(name for name, _ in kernel_variants),
                    *return_prelink_kernel_names,
                ]
            ),
            "final-kernel-objects: "
            + " ".join(
                f"{build}/{name}.o"
                for name in [
                    *(name for name, _ in kernel_variants),
                    *return_final_kernel_names,
                ]
            ),
            "",
            "-include "
            + " ".join(
                f"{build}/{name}.o.d"
                for name in [
                    *(name for name, _ in kernel_variants),
                    *return_prelink_kernel_names,
                    *return_final_kernel_names,
                ]
            ),
            "",
        ]
    )
    assembly_flags = shell_join([
        "-m64", "-ffreestanding", f"-fdebug-prefix-map={source_root}=.",
        f"-ffile-prefix-map={source_root}=.", "-g3", f"-I{build}",
    ])
    for name, source, definitions in assembly_variants:
        target = f"{build}/{name}.o"
        depfile = f"{target}.d"
        source_path = make_escape(str(source_root / source))
        arguments = shell_join(list(definitions))
        lines.extend(
            [
                f"{target} {depfile} &: {source_path}",
                f"\t$(IMAGE_CC) {assembly_flags} {arguments} -MMD -MP -MF {depfile} -c $< -o {target}",
            ]
        )
    lines.extend(
        [
            "",
            ".PHONY: variant-assembly-objects",
            "variant-assembly-objects: "
            + " ".join(f"{build}/{name}.o" for name, _, _ in assembly_variants),
            "",
            "-include "
            + " ".join(f"{build}/{name}.o.d" for name, _, _ in assembly_variants),
            "",
        ]
    )
    common_link_inputs = [f"{build}/{name}.o" for name in COMMON_LINK_OBJECTS]
    return_prelink_targets = []
    for fixture, _mode in return_corruptions:
        boot_object = (
            "boot-return-post-validation-qemu"
            if fixture == "post-validation-mutation"
            else "boot"
        )
        target = f"{build}/leanos-return-{fixture}-prelink.elf"
        map_file = f"{build}/leanos-return-{fixture}-prelink.map"
        inputs = [
            f"{build}/{boot_object}.o",
            f"{build}/kernel-return-{fixture}-prelink.o",
            *common_link_inputs,
        ]
        input_list = " ".join(inputs)
        lines.extend(
            [
                f"{target}: {input_list} $(IMAGE_LINKER_SCRIPT)",
                "\tld -m elf_x86_64 -nostdlib --gc-sections --build-id=none "
                f"-T $(IMAGE_LINKER_SCRIPT) -Map {map_file} -o $@ {input_list}",
            ]
        )
        return_prelink_targets.append(target)
    lines.extend(
        [
            "",
            ".PHONY: return-corruption-prelinks",
            "return-corruption-prelinks: " + " ".join(return_prelink_targets),
            "",
        ]
    )
    return_final_targets = []
    for fixture, _mode in return_corruptions:
        boot_object = (
            "boot-return-post-validation-qemu"
            if fixture == "post-validation-mutation"
            else "boot"
        )
        target = f"{build}/leanos-return-{fixture}.elf"
        map_file = f"{build}/leanos-return-{fixture}.map"
        inputs = [
            f"{build}/{boot_object}.o",
            f"{build}/kernel-return-{fixture}.o",
            *common_link_inputs,
        ]
        input_list = " ".join(inputs)
        lines.extend(
            [
                f"{target}: {input_list} $(IMAGE_LINKER_SCRIPT)",
                "\tld -m elf_x86_64 -nostdlib --gc-sections --build-id=none "
                f"-T $(IMAGE_LINKER_SCRIPT) -Map {map_file} -o $@ {input_list}",
            ]
        )
        return_final_targets.append(target)
    lines.extend(
        [
            "",
            ".PHONY: return-corruption-final-images",
            "return-corruption-final-images: " + " ".join(return_final_targets),
            "",
        ]
    )
    prelink_targets = []
    for name, boot_object, kernel_object, extra_objects in prelink_variants:
        stem = f"leanos-{name}" if name else "leanos"
        target = f"{build}/{stem}-prelink.elf"
        map_file = f"{build}/{stem}-prelink.map"
        inputs = [
            f"{build}/{boot_object}.o",
            *[f"{build}/{extra}.o" for extra in extra_objects],
            f"{build}/{kernel_object}.o",
            *common_link_inputs,
        ]
        input_list = " ".join(inputs)
        lines.extend(
            [
                f"{target}: {input_list} $(IMAGE_LINKER_SCRIPT)",
                "\tld -m elf_x86_64 -nostdlib --gc-sections --build-id=none "
                f"-T $(IMAGE_LINKER_SCRIPT) -Map {map_file} -o $@ {input_list}",
            ]
        )
        prelink_targets.append(target)
    lines.extend(
        [
            "",
            ".PHONY: prelink-images",
            "prelink-images: " + " ".join(prelink_targets),
            "",
        ]
    )
    final_link_targets = []
    for name, boot_object, kernel_object, extra_objects in final_link_variants:
        stem = f"leanos-{name}" if name else "leanos"
        target = f"{build}/{stem}.elf"
        map_file = f"{build}/{stem}.map"
        inputs = [
            f"{build}/{boot_object}.o",
            *[f"{build}/{extra}.o" for extra in extra_objects],
            f"{build}/{kernel_object}.o",
            *common_link_inputs,
        ]
        input_list = " ".join(inputs)
        lines.extend(
            [
                f"{target}: {input_list} $(IMAGE_LINKER_SCRIPT)",
                "\tld -m elf_x86_64 -nostdlib --gc-sections --build-id=none "
                f"-T $(IMAGE_LINKER_SCRIPT) -Map {map_file} -o $@ {input_list}",
            ]
        )
        final_link_targets.append(target)
    lines.extend(
        [
            "",
            ".PHONY: final-image-links",
            "final-image-links: " + " ".join(final_link_targets),
            "",
        ]
    )
    policy_fixture_targets = []
    for name, boot_object, kernel_object, extra_objects in policy_fixture_variants:
        target = f"{build}/leanos-{name}.elf"
        map_file = f"{build}/leanos-{name}.map"
        inputs = [
            f"{build}/{boot_object}.o",
            *[f"{build}/{extra}.o" for extra in extra_objects],
            f"{build}/{kernel_object}.o",
            *common_link_inputs,
        ]
        input_list = " ".join(inputs)
        lines.extend(
            [
                f"{target}: {input_list} $(IMAGE_LINKER_SCRIPT)",
                "\tld -m elf_x86_64 -nostdlib --gc-sections --build-id=none "
                f"-T $(IMAGE_LINKER_SCRIPT) -Map {map_file} -o $@ {input_list}",
            ]
        )
        policy_fixture_targets.append(target)
    lines.extend(
        [
            "",
            ".PHONY: policy-fixture-images",
            "policy-fixture-images: " + " ".join(policy_fixture_targets),
            "",
        ]
    )
    return "\n".join(lines)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--build-dir", type=Path, required=True)
    parser.add_argument("--cc", required=True)
    parser.add_argument("--lean-prefix", type=Path, required=True)
    parser.add_argument("--source-root", type=Path, required=True)
    parser.add_argument("--cflag", action="append", default=[])
    parser.add_argument("--return-corruption", action="append", default=[])
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    return parser.parse_args()


def parse_return_corruptions(values: list[str]) -> list[tuple[str, int]]:
    parsed = []
    for value in values:
        fixture, separator, mode_text = value.rpartition(":")
        if not separator or not fixture or not mode_text.isdecimal():
            raise ValueError(f"invalid return-corruption specification: {value!r}")
        parsed.append((fixture, int(mode_text)))
    return parsed


def main() -> None:
    args = parse_args()
    graph = render_graph(
        args.build_dir,
        args.cc,
        args.cflag,
        args.lean_prefix,
        args.source_root,
        parse_return_corruptions(args.return_corruption),
        tables=variant_tables(load_build_manifest(args.manifest)),
    )
    args.output.write_text(graph, encoding="utf-8")


if __name__ == "__main__":
    main()
