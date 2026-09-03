#!/usr/bin/env python3
"""Generate the shared and variant C-object portion of the image Make graph."""

from __future__ import annotations

import argparse
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

KERNEL_VARIANTS = (
    ("kernel", ("-DLEANOS_ENTRY_HIGH_WATER=1",)),
    ("kernel-malformed-handoff", (
        "-DLEANOS_MALFORMED_HANDOFF_FIXTURE=1",
        '-DLEANOS_BOOT_PAGE_PLAN_HEADER="boot-page-plan-malformed-handoff.h"',
    )),
    ("kernel-projection-authority-mutation", (
        "-DLEANOS_PROJECTION_SELECTION_MUTATION_FIXTURE=1",
        '-DLEANOS_BOOT_PAGE_PLAN_HEADER="boot-page-plan-projection-authority-mutation.h"',
    )),
    ("kernel-raw-selection-authority-mutation", (
        "-DLEANOS_RAW_SELECTION_MUTATION_FIXTURE=1",
        '-DLEANOS_BOOT_PAGE_PLAN_HEADER="boot-page-plan-raw-selection-authority-mutation.h"',
    )),
    ("kernel-preemption", (
        "-DLEANOS_PREEMPTION_SCENARIO=1", "-DLEANOS_ENTRY_HIGH_WATER=1",
        '-DLEANOS_BOOT_PAGE_PLAN_HEADER="boot-page-plan-preemption.h"',
    )),
    ("kernel-frame-budget", (
        "-DLEANOS_FRAME_BUDGET_SCENARIO=1",
        '-DLEANOS_BOOT_PAGE_PLAN_HEADER="boot-page-plan-frame-budget.h"',
    )),
    ("kernel-capability-transfer", (
        "-DLEANOS_CAPABILITY_TRANSFER_SCENARIO=1",
        '-DLEANOS_BOOT_PAGE_PLAN_HEADER="boot-page-plan-capability-transfer.h"',
    )),
    ("kernel-inflight-revocation", (
        "-DLEANOS_INFLIGHT_REVOCATION_SCENARIO=1",
        '-DLEANOS_BOOT_PAGE_PLAN_HEADER="boot-page-plan-inflight-revocation.h"',
    )),
    ("kernel-fault-containment", (
        "-DLEANOS_FAULT_CONTAINMENT_SCENARIO=1",
        '-DLEANOS_BOOT_PAGE_PLAN_HEADER="boot-page-plan-fault-containment.h"',
    )),
    ("kernel-fault-reserved-bit", (
        "-DLEANOS_FAULT_CONTAINMENT_SCENARIO=1",
        "-DLEANOS_PAGE_FAULT_PROBE_RESERVED_BIT=1",
        '-DLEANOS_BOOT_PAGE_PLAN_HEADER="boot-page-plan-fault-reserved-bit.h"',
    )),
    ("kernel-fault-walk-mismatch", (
        "-DLEANOS_FAULT_CONTAINMENT_SCENARIO=1",
        "-DLEANOS_PAGE_FAULT_PROBE_WALK_MISMATCH=1",
        '-DLEANOS_BOOT_PAGE_PLAN_HEADER="boot-page-plan-fault-walk-mismatch.h"',
    )),
    ("kernel-fault-stale-translation", (
        "-DLEANOS_FAULT_CONTAINMENT_SCENARIO=1",
        "-DLEANOS_PAGE_FAULT_PROBE_STALE_TRANSLATION=1",
        '-DLEANOS_BOOT_PAGE_PLAN_HEADER="boot-page-plan-fault-stale-translation.h"',
    )),
    ("kernel-extended-state", (
        "-DLEANOS_EXTENDED_STATE_SCENARIO=1",
        '-DLEANOS_BOOT_PAGE_PLAN_HEADER="boot-page-plan-extended-state.h"',
    )),
    ("kernel-extended-state-peer-pke", (
        "-DLEANOS_EXTENDED_STATE_SCENARIO=1",
        "-DLEANOS_EXTENDED_STATE_PEER_PKE_FIXTURE=1",
        '-DLEANOS_BOOT_PAGE_PLAN_HEADER="boot-page-plan-extended-state-peer-pke.h"',
    )),
    ("kernel-double-fault", ("-DLEANOS_DOUBLE_FAULT_PROBE=1",)),
    ("kernel-entry-stack-overflow", (
        "-DLEANOS_DOUBLE_FAULT_PROBE=1",
        '-DLEANOS_BOOT_PAGE_PLAN_HEADER="boot-page-plan-entry-overflow.h"',
    )),
    ("kernel-double-fault-guard-mapped", (
        "-DLEANOS_DOUBLE_FAULT_PROBE=1", "-DLEANOS_DF_MAP_GUARD=1",
    )),
    ("kernel-entry-adversarial", (
        "-DLEANOS_ENTRY_ADVERSARIAL=1",
        '-DLEANOS_BOOT_PAGE_PLAN_HEADER="boot-page-plan-entry-adversarial.h"',
    )),
    ("kernel-nmi", (
        "-DLEANOS_NMI_PROBE=1",
        '-DLEANOS_BOOT_PAGE_PLAN_HEADER="boot-page-plan-nmi.h"',
    )),
    ("kernel-bootstrap32-ud", (
        "-DLEANOS_ENTRY_HIGH_WATER=1",
        '-DLEANOS_BOOT_PAGE_PLAN_HEADER="boot-page-plan-bootstrap32-ud.h"',
    )),
    ("kernel-bootstrap64-nmi", (
        "-DLEANOS_ENTRY_HIGH_WATER=1",
        '-DLEANOS_BOOT_PAGE_PLAN_HEADER="boot-page-plan-bootstrap64-nmi.h"',
    )),
    ("kernel-direct-port", (
        "-DLEANOS_DIRECT_PORT_CONTAINMENT_SCENARIO=1",
        '-DLEANOS_BOOT_PAGE_PLAN_HEADER="boot-page-plan-direct-port.h"',
    )),
    ("kernel-integer-fault", (
        "-DLEANOS_INTEGER_FAULT_SCENARIO=1",
        '-DLEANOS_BOOT_PAGE_PLAN_HEADER="boot-page-plan-integer-fault.h"',
    )),
)

ASSEMBLY_VARIANTS = (
    ("boot", "boot/boot.S", ()),
    ("boot-preemption", "boot/boot.S", ("-DLEANOS_PREEMPTION_SCENARIO=1",)),
    ("boot-frame-budget", "boot/boot.S", ("-DLEANOS_FRAME_BUDGET_SCENARIO=1",)),
    ("boot-capability-transfer", "boot/boot.S", (
        "-DLEANOS_CAPABILITY_TRANSFER_SCENARIO=1",
    )),
    ("boot-inflight-revocation", "boot/boot.S", (
        "-DLEANOS_INFLIGHT_REVOCATION_SCENARIO=1",
    )),
    ("boot-fault-containment", "boot/boot.S", ("-DLEANOS_FAULT_CONTAINMENT_SCENARIO=1",)),
    ("boot-fault-readonly-write", "boot/boot.S", (
        "-DLEANOS_FAULT_CONTAINMENT_SCENARIO=1",
        "-DLEANOS_PAGE_FAULT_PROBE_READONLY_WRITE=1",
    )),
    ("boot-fault-nx-execute", "boot/boot.S", (
        "-DLEANOS_FAULT_CONTAINMENT_SCENARIO=1",
        "-DLEANOS_PAGE_FAULT_PROBE_NX_EXECUTE=1",
    )),
    ("boot-fault-reserved-bit", "boot/boot.S", (
        "-DLEANOS_FAULT_CONTAINMENT_SCENARIO=1",
        "-DLEANOS_PAGE_FAULT_PROBE_RESERVED_BIT=1",
    )),
    ("boot-fault-walk-mismatch", "boot/boot.S", (
        "-DLEANOS_FAULT_CONTAINMENT_SCENARIO=1",
        "-DLEANOS_PAGE_FAULT_PROBE_WALK_MISMATCH=1",
    )),
    ("boot-fault-stale-translation", "boot/boot.S", (
        "-DLEANOS_FAULT_CONTAINMENT_SCENARIO=1",
        "-DLEANOS_PAGE_FAULT_PROBE_STALE_TRANSLATION=1",
    )),
    ("boot-extended-state", "boot/boot.S", ("-DLEANOS_EXTENDED_STATE_SCENARIO=1",)),
    ("boot-extended-state-mmx", "boot/boot.S", (
        "-DLEANOS_EXTENDED_STATE_SCENARIO=1", "-DLEANOS_EXTENDED_STATE_MMX_PROBE=1",
    )),
    ("boot-extended-state-sse", "boot/boot.S", (
        "-DLEANOS_EXTENDED_STATE_SCENARIO=1", "-DLEANOS_EXTENDED_STATE_SSE_PROBE=1",
    )),
    ("boot-extended-state-sse2", "boot/boot.S", (
        "-DLEANOS_EXTENDED_STATE_SCENARIO=1", "-DLEANOS_EXTENDED_STATE_SSE2_PROBE=1",
    )),
    ("boot-extended-state-avx", "boot/boot.S", (
        "-DLEANOS_EXTENDED_STATE_SCENARIO=1", "-DLEANOS_EXTENDED_STATE_AVX_PROBE=1",
    )),
    ("boot-extended-state-peer-pke", "boot/boot.S", (
        "-DLEANOS_EXTENDED_STATE_SCENARIO=1",
        "-DLEANOS_EXTENDED_STATE_PEER_PKE_FIXTURE=1",
    )),
    ("boot-fast-entry-syscall", "boot/boot.S", (
        "-DLEANOS_EXTENDED_STATE_SCENARIO=1", "-DLEANOS_FAST_ENTRY_SYSCALL_PROBE=1",
    )),
    ("boot-fast-entry-sysenter", "boot/boot.S", (
        "-DLEANOS_EXTENDED_STATE_SCENARIO=1", "-DLEANOS_FAST_ENTRY_SYSENTER_PROBE=1",
    )),
    ("peer-pke-fixture", "boot/peer-pke-fixture.S", ()),
    ("boot-return-restore-fixture", "boot/boot.S", ("-DLEANOS_RETURN_RESTORE_FIXTURE=1",)),
    ("boot-return-branch-fixture", "boot/boot.S", ("-DLEANOS_RETURN_BRANCH_FIXTURE=1",)),
    ("boot-return-indirect-fixture", "boot/boot.S", ("-DLEANOS_RETURN_INDIRECT_FIXTURE=1",)),
    ("boot-return-initial-indirect-fixture", "boot/boot.S", ("-DLEANOS_RETURN_INITIAL_INDIRECT_FIXTURE=1",)),
    ("boot-return-post-validation-qemu", "boot/boot.S", ("-DLEANOS_RETURN_POST_VALIDATE_QEMU_FIXTURE=1",)),
    ("boot-df-guard-mapped", "boot/boot.S", ("-DLEANOS_DF_MAP_GUARD=1",)),
    ("boot-entry-stack-overflow", "boot/boot.S", ("-DLEANOS_ENTRY_STACK_OVERFLOW_PROBE=1",)),
    ("boot-entry-adversarial", "boot/boot.S", ("-DLEANOS_ENTRY_ADVERSARIAL=1",)),
    ("boot-nmi", "boot/boot.S", ("-DLEANOS_NMI_PROBE=1",)),
    ("boot-bootstrap32-ud", "boot/boot.S", ("-DLEANOS_BOOTSTRAP32_UD_PROBE=1",)),
    ("boot-bootstrap64-nmi", "boot/boot.S", ("-DLEANOS_BOOTSTRAP64_NMI_PROBE=1",)),
    ("boot-direct-port-serial", "boot/boot.S", ("-DLEANOS_DIRECT_PORT_CONTAINMENT_SCENARIO=1",)),
    ("boot-direct-port-debug", "boot/boot.S", (
        "-DLEANOS_DIRECT_PORT_CONTAINMENT_SCENARIO=1", "-DLEANOS_DIRECT_PORT_PROBE_DEBUG=1",
    )),
    ("boot-direct-port-in", "boot/boot.S", (
        "-DLEANOS_DIRECT_PORT_CONTAINMENT_SCENARIO=1", "-DLEANOS_DIRECT_PORT_PROBE_IN=1",
    )),
    ("boot-direct-port-pic", "boot/boot.S", (
        "-DLEANOS_DIRECT_PORT_CONTAINMENT_SCENARIO=1", "-DLEANOS_DIRECT_PORT_PROBE_PIC=1",
    )),
    ("boot-divide-error", "boot/boot.S", ("-DLEANOS_INTEGER_FAULT_SCENARIO=1",)),
    ("boot-breakpoint", "boot/boot.S", (
        "-DLEANOS_INTEGER_FAULT_SCENARIO=1", "-DLEANOS_INTEGER_FAULT_PROBE_BP=1",
    )),
)

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
PRELINK_VARIANTS = (
    ("", "boot", "kernel", ()),
    ("malformed-handoff", "boot", "kernel-malformed-handoff", ()),
    (
        "projection-authority-mutation",
        "boot",
        "kernel-projection-authority-mutation",
        (),
    ),
    (
        "raw-selection-authority-mutation",
        "boot",
        "kernel-raw-selection-authority-mutation",
        (),
    ),
    ("preemption", "boot-preemption", "kernel-preemption", ()),
    ("frame-budget", "boot-frame-budget", "kernel-frame-budget", ()),
    (
        "capability-transfer",
        "boot-capability-transfer",
        "kernel-capability-transfer",
        (),
    ),
    (
        "inflight-revocation",
        "boot-inflight-revocation",
        "kernel-inflight-revocation",
        (),
    ),
    (
        "fault-containment",
        "boot-fault-containment",
        "kernel-fault-containment",
        (),
    ),
    (
        "fault-readonly-write",
        "boot-fault-readonly-write",
        "kernel-fault-containment",
        (),
    ),
    (
        "fault-nx-execute",
        "boot-fault-nx-execute",
        "kernel-fault-containment",
        (),
    ),
    (
        "fault-reserved-bit",
        "boot-fault-reserved-bit",
        "kernel-fault-reserved-bit",
        (),
    ),
    (
        "fault-walk-mismatch",
        "boot-fault-walk-mismatch",
        "kernel-fault-walk-mismatch",
        (),
    ),
    (
        "fault-stale-translation",
        "boot-fault-stale-translation",
        "kernel-fault-stale-translation",
        (),
    ),
    ("extended-state", "boot-extended-state", "kernel-extended-state", ()),
    (
        "extended-state-mmx",
        "boot-extended-state-mmx",
        "kernel-extended-state",
        (),
    ),
    (
        "extended-state-sse",
        "boot-extended-state-sse",
        "kernel-extended-state",
        (),
    ),
    (
        "extended-state-sse2",
        "boot-extended-state-sse2",
        "kernel-extended-state",
        (),
    ),
    (
        "extended-state-avx",
        "boot-extended-state-avx",
        "kernel-extended-state",
        (),
    ),
    (
        "extended-state-peer-pke",
        "boot-extended-state-peer-pke",
        "kernel-extended-state-peer-pke",
        ("peer-pke-fixture",),
    ),
    (
        "fast-entry-syscall",
        "boot-fast-entry-syscall",
        "kernel-extended-state",
        (),
    ),
    (
        "fast-entry-sysenter",
        "boot-fast-entry-sysenter",
        "kernel-extended-state",
        (),
    ),
    ("double-fault", "boot", "kernel-double-fault", ()),
    (
        "entry-stack-overflow",
        "boot-entry-stack-overflow",
        "kernel-double-fault",
        (),
    ),
    (
        "entry-adversarial",
        "boot-entry-adversarial",
        "kernel-entry-adversarial",
        (),
    ),
    ("direct-port-serial", "boot-direct-port-serial", "kernel-direct-port", ()),
    ("direct-port-debug", "boot-direct-port-debug", "kernel-direct-port", ()),
    ("direct-port-in", "boot-direct-port-in", "kernel-direct-port", ()),
    ("direct-port-pic", "boot-direct-port-pic", "kernel-direct-port", ()),
    ("divide-error", "boot-divide-error", "kernel-integer-fault", ()),
    ("breakpoint", "boot-breakpoint", "kernel-integer-fault", ()),
    ("nmi", "boot-nmi", "kernel-nmi", ()),
    ("bootstrap32-ud", "boot-bootstrap32-ud", "kernel-bootstrap32-ud", ()),
    (
        "bootstrap64-nmi",
        "boot-bootstrap64-nmi",
        "kernel-bootstrap64-nmi",
        (),
    ),
    (
        "guard",
        "boot-df-guard-mapped",
        "kernel-double-fault-guard-mapped",
        (),
    ),
)

# These images can be linked immediately after their generated boot-page plans
# recompile the final kernel objects.  Double-fault, entry-stack-overflow, and
# guard images retain their later policy-specific link/validation sequence.
FINAL_LINK_VARIANTS = tuple(
    variant
    for variant in PRELINK_VARIANTS
    if variant[0] not in {"double-fault", "entry-stack-overflow", "guard"}
)

# Policy-negative fixtures are final ELFs rather than boot-page-plan prelinks,
# but they share the same reviewed linker inventory and can be scheduled with
# the independent prelink family.
POLICY_FIXTURE_VARIANTS = (
    ("return-restore-fixture", "boot-return-restore-fixture", "kernel", ()),
    ("return-branch-fixture", "boot-return-branch-fixture", "kernel", ()),
    ("return-indirect-fixture", "boot-return-indirect-fixture", "kernel", ()),
    (
        "return-initial-indirect-fixture",
        "boot-return-initial-indirect-fixture",
        "kernel",
        (),
    ),
)


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
) -> str:
    return_corruptions = return_corruptions or []
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
    for name, definitions in KERNEL_VARIANTS:
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
                    *(name for name, _ in KERNEL_VARIANTS),
                    *return_prelink_kernel_names,
                ]
            ),
            "final-kernel-objects: "
            + " ".join(
                f"{build}/{name}.o"
                for name in [
                    *(name for name, _ in KERNEL_VARIANTS),
                    *return_final_kernel_names,
                ]
            ),
            "",
            "-include "
            + " ".join(
                f"{build}/{name}.o.d"
                for name in [
                    *(name for name, _ in KERNEL_VARIANTS),
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
    for name, source, definitions in ASSEMBLY_VARIANTS:
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
            + " ".join(f"{build}/{name}.o" for name, _, _ in ASSEMBLY_VARIANTS),
            "",
            "-include "
            + " ".join(f"{build}/{name}.o.d" for name, _, _ in ASSEMBLY_VARIANTS),
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
    for name, boot_object, kernel_object, extra_objects in PRELINK_VARIANTS:
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
    for name, boot_object, kernel_object, extra_objects in FINAL_LINK_VARIANTS:
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
    for name, boot_object, kernel_object, extra_objects in POLICY_FIXTURE_VARIANTS:
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
    )
    args.output.write_text(graph, encoding="utf-8")


if __name__ == "__main__":
    main()
