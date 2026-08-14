#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

require_tool() {
  if ! command -v "$1" >/dev/null 2>&1; then
    echo "error: missing required tool '$1'; $2" >&2
    exit 1
  fi
}

require_tool lake "install Elan from https://elan.lean-lang.org/"
cc="${LEANOS_CC:-gcc}"
require_tool "$cc" "install Ubuntu package gcc=4:13.2.0-7ubuntu1"
require_tool ld "install Ubuntu package binutils=2.42-4ubuntu2.10"
require_tool nm "install Ubuntu package binutils=2.42-4ubuntu2.10"
require_tool grub-file "install Ubuntu package grub-common=2.12-1ubuntu7.3"
require_tool grub-mkrescue "install Ubuntu package grub-common=2.12-1ubuntu7.3"
require_tool mformat "install Ubuntu package mtools=4.0.43-1build1"
require_tool xorriso "install Ubuntu package xorriso=1:1.5.6-1.1ubuntu3"
if [[ ! -d /usr/lib/grub/i386-pc ]]; then
  echo "error: missing GRUB BIOS modules; install Ubuntu package grub-pc-bin=2.12-1ubuntu7.3" >&2
  exit 1
fi

build="$repo_root/build/boot"
iso_root="$build/iso"
preemption_iso_root="$build/iso-preemption"
frame_budget_iso_root="$build/iso-frame-budget"
fault_containment_iso_root="$build/iso-fault-containment"
fault_readonly_write_iso_root="$build/iso-fault-readonly-write"
fault_nx_execute_iso_root="$build/iso-fault-nx-execute"
fault_fatal_probes=(reserved-bit walk-mismatch)
fault_image_probes=("${fault_fatal_probes[@]}" stale-translation)
declare -A fault_fatal_probe_flags=(
  [reserved-bit]="-DLEANOS_PAGE_FAULT_PROBE_RESERVED_BIT=1"
  [walk-mismatch]="-DLEANOS_PAGE_FAULT_PROBE_WALK_MISMATCH=1"
  [stale-translation]="-DLEANOS_PAGE_FAULT_PROBE_STALE_TRANSLATION=1"
)
extended_state_iso_root="$build/iso-extended-state"
extended_state_mmx_iso_root="$build/iso-extended-state-mmx"
extended_state_sse_iso_root="$build/iso-extended-state-sse"
extended_state_sse2_iso_root="$build/iso-extended-state-sse2"
extended_state_avx_iso_root="$build/iso-extended-state-avx"
extended_state_peer_pke_iso_root="$build/iso-extended-state-peer-pke"
fast_entry_syscall_iso_root="$build/iso-fast-entry-syscall"
fast_entry_sysenter_iso_root="$build/iso-fast-entry-sysenter"
df_iso_root="$build/iso-double-fault"
df_negative_iso_root="$build/iso-double-fault-guard-mapped"
entry_overflow_iso_root="$build/iso-entry-stack-overflow"
entry_adversarial_iso_root="$build/iso-entry-adversarial"
nmi_iso_root="$build/iso-nmi"
nmi_cpl3_iso_root="$build/iso-nmi-cpl3"
bootstrap32_ud_iso_root="$build/iso-bootstrap32-ud"
bootstrap64_nmi_iso_root="$build/iso-bootstrap64-nmi"
malformed_handoff_iso_root="$build/iso-malformed-handoff"
projection_authority_iso_root="$build/iso-projection-authority-mutation"
raw_selection_authority_iso_root="$build/iso-raw-selection-authority-mutation"
# Direct-port-containment family (#130): one shared kernel object, one reviewed
# raw CPL3 port instruction per probe selected by a boot.S -D variant.
direct_port_probes=(serial debug in pic)
declare -A direct_port_probe_flags=(
  [serial]=""
  [debug]="-DLEANOS_DIRECT_PORT_PROBE_DEBUG=1"
  [in]="-DLEANOS_DIRECT_PORT_PROBE_IN=1"
  [pic]="-DLEANOS_DIRECT_PORT_PROBE_PIC=1"
)
# Integer-fault-containment family (#150): one shared kernel object, one real
# faulting instruction per probe selected by a boot.S -D variant.
integer_fault_probes=(divide-error breakpoint)
declare -A integer_fault_probe_flags=(
  [divide-error]=""
  [breakpoint]="-DLEANOS_INTEGER_FAULT_PROBE_BP=1"
)
version="${LEANOS_VERSION:-0.1.0}"
source_revision="${LEANOS_SOURCE_REVISION:-$(git rev-parse HEAD)}"
matrix="${LEANOS_EVIDENCE_MATRIX:-scripts/emulator-evidence-matrix.tsv}"
[[ -f "$matrix" ]] || { echo "error: evidence matrix '$matrix' not found" >&2; exit 1; }
return_corruptions=()
while IFS=$'\t' read -r _id runner _class _timeout _image _elf _log \
    fixture mode reason; do
  [[ "$runner" == return ]] || continue
  return_corruptions+=("${fixture}:${mode}:${reason}")
done < "$matrix"
[[ ${#return_corruptions[@]} -gt 0 ]] || {
  echo "error: evidence matrix has no return-corruption scenarios" >&2; exit 1;
}
if [[ ! "$version" =~ ^[0-9]+\.[0-9]+\.[0-9]+$ ]]; then
  echo "error: LEANOS_VERSION must be MAJOR.MINOR.PATCH" >&2
  exit 1
fi
if [[ ! "$source_revision" =~ ^[0-9a-f]{40}$ ]]; then
  echo "error: LEANOS_SOURCE_REVISION must be a full lowercase Git commit" >&2
  exit 1
fi
rm -rf "$build"
mkdir -p "$iso_root/boot/grub" "$preemption_iso_root/boot/grub" \
  "$frame_budget_iso_root/boot/grub" \
  "$fault_containment_iso_root/boot/grub" \
  "$fault_readonly_write_iso_root/boot/grub" \
  "$fault_nx_execute_iso_root/boot/grub" \
  "$extended_state_iso_root/boot/grub" "$extended_state_mmx_iso_root/boot/grub" \
  "$extended_state_sse_iso_root/boot/grub" \
  "$extended_state_sse2_iso_root/boot/grub" \
  "$extended_state_avx_iso_root/boot/grub" \
  "$extended_state_peer_pke_iso_root/boot/grub" \
  "$fast_entry_syscall_iso_root/boot/grub" \
  "$fast_entry_sysenter_iso_root/boot/grub" \
  "$df_iso_root/boot/grub" \
  "$df_negative_iso_root/boot/grub" "$entry_overflow_iso_root/boot/grub" \
  "$entry_adversarial_iso_root/boot/grub" "$nmi_iso_root/boot/grub" \
  "$nmi_cpl3_iso_root/boot/grub" "$bootstrap32_ud_iso_root/boot/grub" \
  "$bootstrap64_nmi_iso_root/boot/grub" \
  "$malformed_handoff_iso_root/boot/grub" \
  "$projection_authority_iso_root/boot/grub" \
  "$raw_selection_authority_iso_root/boot/grub"
for probe in "${fault_image_probes[@]}"; do
  mkdir -p "$build/iso-fault-${probe}/boot/grub"
done
for probe in "${direct_port_probes[@]}"; do
  mkdir -p "$build/iso-direct-port-${probe}/boot/grub"
done
for probe in "${integer_fault_probes[@]}"; do
  mkdir -p "$build/iso-${probe}/boot/grub"
done
./scripts/generate-oracle.sh "$build"
./scripts/generate-boot-page-plan.sh --stub "$build/boot-page-plan.h"
./scripts/generate-boot-page-plan.sh --stub \
  "$build/boot-page-plan-malformed-handoff.h"
./scripts/generate-boot-page-plan.sh --stub \
  "$build/boot-page-plan-projection-authority-mutation.h"
./scripts/generate-boot-page-plan.sh --stub \
  "$build/boot-page-plan-raw-selection-authority-mutation.h"
./scripts/generate-boot-page-plan.sh --stub "$build/boot-page-plan-preemption.h"
./scripts/generate-boot-page-plan.sh --stub "$build/boot-page-plan-frame-budget.h"
./scripts/generate-boot-page-plan.sh --stub "$build/boot-page-plan-fault-containment.h"
./scripts/generate-boot-page-plan.sh --stub "$build/boot-page-plan-fault-nx-execute.h"
for probe in "${fault_image_probes[@]}"; do
  ./scripts/generate-boot-page-plan.sh --stub \
    "$build/boot-page-plan-fault-${probe}.h"
done
./scripts/generate-boot-page-plan.sh --stub "$build/boot-page-plan-extended-state.h"
./scripts/generate-boot-page-plan.sh --stub "$build/boot-page-plan-extended-state-peer-pke.h"
./scripts/generate-boot-page-plan.sh --stub "$build/boot-page-plan-double-fault.h"
./scripts/generate-boot-page-plan.sh --stub "$build/boot-page-plan-entry-overflow.h"
./scripts/generate-boot-page-plan.sh --stub "$build/boot-page-plan-guard.h"
./scripts/generate-boot-page-plan.sh --stub "$build/boot-page-plan-entry-adversarial.h"
./scripts/generate-boot-page-plan.sh --stub "$build/boot-page-plan-nmi.h"
./scripts/generate-boot-page-plan.sh --stub "$build/boot-page-plan-bootstrap32-ud.h"
./scripts/generate-boot-page-plan.sh --stub "$build/boot-page-plan-bootstrap64-nmi.h"
./scripts/generate-boot-page-plan.sh --stub "$build/boot-page-plan-direct-port.h"
./scripts/generate-boot-page-plan.sh --stub "$build/boot-page-plan-integer-fault.h"

# C generation resolves project imports through Lake's compiled module path.
# Build them here because image jobs and clean checkouts cannot rely on a
# previous proof-check job's workspace.
lake build
lake env lean --c="$build/KernelTransition.c" LeanOS/KernelTransition.lean
lake env lean --c="$build/Syscall.c" LeanOS/Syscall.lean
lake env lean --c="$build/IPCSyscall.c" LeanOS/IPCSyscall.lean
lake env lean --c="$build/Preemption.c" LeanOS/Preemption.lean
lake env lean --c="$build/BootAllocation.c" LeanOS/BootAllocation.lean
lake env lean --c="$build/BootMemoryMapStreaming.c" \
  LeanOS/BootMemoryMapStreaming.lean
lake env lean --c="$build/BootMemoryMapStreamAuthority.c" \
  LeanOS/BootMemoryMapStreamAuthority.lean
lake env lean --c="$build/BootTopology.c" LeanOS/BootTopology.lean
lake env lean --c="$build/Interrupt.c" LeanOS/Interrupt.lean
lake env lean --c="$build/InterruptEntry.c" LeanOS/InterruptEntry.lean
lake env lean --c="$build/BlockingIPC.c" LeanOS/BlockingIPC.lean
lake env lean --c="$build/CapabilityReuse.c" LeanOS/CapabilityReuse.lean
lake env lean --c="$build/ExtendedState.c" LeanOS/ExtendedState.lean
lake env lean --c="$build/PrivilegeEntryControl.c" LeanOS/PrivilegeEntryControl.lean
lake env lean --c="$build/FaultDispatch.c" LeanOS/FaultDispatch.lean
lake env lean --c="$build/DirectPortIO.c" LeanOS/DirectPortIO.lean
lake env lean --c="$build/StaleTranslation.c" LeanOS/StaleTranslation.lean
lake env lean --c="$build/FrameBudgetScenario.c" \
  LeanOS/FrameBudgetScenario.lean
lake env lean --c="$build/CompositeDispatcher.c" LeanOS/CompositeDispatcher.lean
lake env lean --c="$build/VTdBootPlan.c" LeanOS/VTdBootPlan.lean
lean_prefix="$(lake env lean --print-prefix)"
cflags=(-m64 -std=c11 -ffreestanding -fno-stack-protector -fno-pic -Iinclude
  -mno-red-zone -mgeneral-regs-only -ffunction-sections -fdata-sections
  -fstack-usage
  -fdebug-prefix-map="$repo_root"=. -ffile-prefix-map="$repo_root"=.
  -fdebug-prefix-map="$lean_prefix"=/lean-toolchain
  -ffile-prefix-map="$lean_prefix"=/lean-toolchain -g3 -O2)
if "$cc" --version | sed -n '1p' | grep -qi clang; then
  # With general-registers-only Clang otherwise reports an extended
  # FLT_EVAL_METHOD, which Lean correctly rejects. Clang 18 also diagnoses
  # source-width evaluation on the no-SSE target once per parsed function.
  # Keep that diagnostic visible but do not promote this one known limitation
  # to an error; -Werror remains active for every source warning, while
  # -mgeneral-regs-only rejects any actual floating-point register use.
  # The entry-stack final-ELF gate rejects indirect control-flow edges because
  # their targets cannot be bounded by the reviewed static call graph. Clang
  # otherwise lowers the generated finite entry classifier through a jump
  # table, so retain direct conditional branches in this independent lane.
  cflags+=(-ffp-eval-method=source -Wno-error=pragmas -fno-jump-tables)
fi
{
  printf 'image-compiler-command\t%s\n' "$cc"
  printf 'image-compiler-version\t'
  "$cc" --version | sed -n '1p'
  printf 'image-compiler-flags'
  printf '\t%q' "${cflags[@]}"
  printf '\nassembler-linker\tGNU binutils (shared with reference lane)\n'
} > "$build/compiler-and-flags.tsv"
"$cc" "${cflags[@]}" -I"$lean_prefix/include" -c "$build/KernelTransition.c" \
  -o "$build/KernelTransition.o"
"$cc" "${cflags[@]}" -I"$lean_prefix/include" -c "$build/Syscall.c" \
  -o "$build/Syscall.o"
"$cc" "${cflags[@]}" -I"$lean_prefix/include" -c "$build/IPCSyscall.c" \
  -o "$build/IPCSyscall.o"
"$cc" "${cflags[@]}" -I"$lean_prefix/include" -c "$build/Preemption.c" \
  -o "$build/Preemption.o"
"$cc" "${cflags[@]}" -I"$lean_prefix/include" -c "$build/BootAllocation.c" \
  -o "$build/BootAllocation.o"
"$cc" "${cflags[@]}" -I"$lean_prefix/include" \
  -c "$build/BootMemoryMapStreaming.c" \
  -o "$build/BootMemoryMapStreaming.o"
"$cc" "${cflags[@]}" -I"$lean_prefix/include" \
  -c "$build/BootMemoryMapStreamAuthority.c" \
  -o "$build/BootMemoryMapStreamAuthority.o"
"$cc" "${cflags[@]}" -I"$lean_prefix/include" \
  -c "$build/BootTopology.c" -o "$build/BootTopology.o"
# All existing image variants link BootAllocation.o.  Combine the generated
# stream transport and allocation-free topology scalar boundary into that
# reviewed object so no variant can omit either machine-enforcement edge.
# Section GC retains only the called BootTopology closure; the hosted
# ByteArray/list topology query and its Lean runtime dependencies stay absent.
ld -r "$build/BootAllocation.o" "$build/BootMemoryMapStreaming.o" \
  "$build/BootMemoryMapStreamAuthority.o" "$build/BootTopology.o" \
  -o "$build/BootAllocationAndHandoffStream.o"
mv "$build/BootAllocationAndHandoffStream.o" "$build/BootAllocation.o"
"$cc" "${cflags[@]}" -I"$lean_prefix/include" -c "$build/Interrupt.c" \
  -o "$build/Interrupt.o"
"$cc" "${cflags[@]}" -I"$lean_prefix/include" -c "$build/InterruptEntry.c" \
  -o "$build/InterruptEntry.o"
"$cc" "${cflags[@]}" -I"$lean_prefix/include" -c "$build/BlockingIPC.c" \
  -o "$build/BlockingIPC.o"
"$cc" "${cflags[@]}" -I"$lean_prefix/include" -c "$build/CapabilityReuse.c" \
  -o "$build/CapabilityReuse.o"
"$cc" "${cflags[@]}" -I"$lean_prefix/include" -c "$build/ExtendedState.c" \
  -o "$build/ExtendedState.o"
"$cc" "${cflags[@]}" -I"$lean_prefix/include" \
  -c "$build/PrivilegeEntryControl.c" -o "$build/PrivilegeEntryControl.o"
"$cc" "${cflags[@]}" -I"$lean_prefix/include" -c "$build/FaultDispatch.c" \
  -o "$build/FaultDispatch.o"
"$cc" "${cflags[@]}" -I"$lean_prefix/include" -c "$build/DirectPortIO.c" \
  -o "$build/DirectPortIO.o"
"$cc" "${cflags[@]}" -I"$lean_prefix/include" -c "$build/StaleTranslation.c" \
  -o "$build/StaleTranslation.o"
"$cc" "${cflags[@]}" -I"$lean_prefix/include" \
  -c "$build/FrameBudgetScenario.c" -o "$build/FrameBudgetScenario.o"
# Keep the existing bounded link inventory compact while retaining the
# independently generated model adapters in every image variant.
"$cc" "${cflags[@]}" -I"$lean_prefix/include" \
  -c "$build/CompositeDispatcher.c" -o "$build/CompositeDispatcher.o"
"$cc" "${cflags[@]}" -I"$lean_prefix/include" \
  -c "$build/VTdBootPlan.c" -o "$build/VTdBootPlan.o"
ld -r "$build/FaultDispatch.o" "$build/DirectPortIO.o" \
  "$build/StaleTranslation.o" "$build/FrameBudgetScenario.o" \
  "$build/CompositeDispatcher.o" "$build/VTdBootPlan.o" \
  -o "$build/FaultDispatchAndCompositeAdapters.o"
mv "$build/FaultDispatchAndCompositeAdapters.o" "$build/FaultDispatch.o"
"$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
  -DLEANOS_ENTRY_HIGH_WATER=1 -c boot/kernel.c \
  -o "$build/kernel.o"
"$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
  -DLEANOS_MALFORMED_HANDOFF_FIXTURE=1 \
  -DLEANOS_BOOT_PAGE_PLAN_HEADER='"boot-page-plan-malformed-handoff.h"' \
  -c boot/kernel.c -o "$build/kernel-malformed-handoff.o"
"$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
  -DLEANOS_PROJECTION_SELECTION_MUTATION_FIXTURE=1 \
  -DLEANOS_BOOT_PAGE_PLAN_HEADER='"boot-page-plan-projection-authority-mutation.h"' \
  -c boot/kernel.c -o "$build/kernel-projection-authority-mutation.o"
"$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
  -DLEANOS_RAW_SELECTION_MUTATION_FIXTURE=1 \
  -DLEANOS_BOOT_PAGE_PLAN_HEADER='"boot-page-plan-raw-selection-authority-mutation.h"' \
  -c boot/kernel.c -o "$build/kernel-raw-selection-authority-mutation.o"
"$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
  -DLEANOS_PREEMPTION_SCENARIO=1 -DLEANOS_ENTRY_HIGH_WATER=1 \
  -DLEANOS_BOOT_PAGE_PLAN_HEADER='"boot-page-plan-preemption.h"' \
  -c boot/kernel.c -o "$build/kernel-preemption.o"
"$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
  -DLEANOS_FRAME_BUDGET_SCENARIO=1 \
  -DLEANOS_BOOT_PAGE_PLAN_HEADER='"boot-page-plan-frame-budget.h"' \
  -c boot/kernel.c -o "$build/kernel-frame-budget.o"
"$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
  -DLEANOS_FAULT_CONTAINMENT_SCENARIO=1 \
  -DLEANOS_BOOT_PAGE_PLAN_HEADER='"boot-page-plan-fault-containment.h"' \
  -c boot/kernel.c -o "$build/kernel-fault-containment.o"
for probe in "${fault_image_probes[@]}"; do
  fault_plan_header="boot-page-plan-fault-containment.h"
  if [[ "$probe" == stale-translation ]]; then
    fault_plan_header="boot-page-plan-fault-stale-translation.h"
  fi
  "$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
    -DLEANOS_FAULT_CONTAINMENT_SCENARIO=1 \
    "${fault_fatal_probe_flags[$probe]}" \
    -DLEANOS_BOOT_PAGE_PLAN_HEADER="\"${fault_plan_header}\"" \
    -c boot/kernel.c -o "$build/kernel-fault-${probe}.o"
done
"$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
  -DLEANOS_EXTENDED_STATE_SCENARIO=1 \
  -DLEANOS_BOOT_PAGE_PLAN_HEADER='"boot-page-plan-extended-state.h"' \
  -c boot/kernel.c -o "$build/kernel-extended-state.o"
"$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
  -DLEANOS_EXTENDED_STATE_SCENARIO=1 \
  -DLEANOS_EXTENDED_STATE_PEER_PKE_FIXTURE=1 \
  -DLEANOS_BOOT_PAGE_PLAN_HEADER='"boot-page-plan-extended-state-peer-pke.h"' \
  -c boot/kernel.c -o "$build/kernel-extended-state-peer-pke.o"
"$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
  -DLEANOS_DOUBLE_FAULT_PROBE=1 -c boot/kernel.c -o "$build/kernel-double-fault.o"
"$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
  -DLEANOS_DOUBLE_FAULT_PROBE=1 -DLEANOS_DF_MAP_GUARD=1 \
  -c boot/kernel.c -o "$build/kernel-double-fault-guard-mapped.o"
"$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
  -DLEANOS_ENTRY_ADVERSARIAL=1 \
  -DLEANOS_BOOT_PAGE_PLAN_HEADER='"boot-page-plan-entry-adversarial.h"' \
  -c boot/kernel.c -o "$build/kernel-entry-adversarial.o"
"$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
  -DLEANOS_NMI_PROBE=1 -c boot/kernel.c -o "$build/kernel-nmi.o"
"$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
  -DLEANOS_ENTRY_HIGH_WATER=1 -c boot/kernel.c \
  -o "$build/kernel-bootstrap32-ud.o"
"$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
  -DLEANOS_ENTRY_HIGH_WATER=1 -c boot/kernel.c \
  -o "$build/kernel-bootstrap64-nmi.o"
"$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
  -DLEANOS_DIRECT_PORT_CONTAINMENT_SCENARIO=1 \
  -DLEANOS_BOOT_PAGE_PLAN_HEADER='"boot-page-plan-direct-port.h"' \
  -c boot/kernel.c -o "$build/kernel-direct-port.o"
"$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
  -DLEANOS_INTEGER_FAULT_SCENARIO=1 \
  -DLEANOS_BOOT_PAGE_PLAN_HEADER='"boot-page-plan-integer-fault.h"' \
  -c boot/kernel.c -o "$build/kernel-integer-fault.o"

cp scripts/entry-stack-callgraph.tsv "$build/entry-stack-callgraph.tsv"
cp scripts/entry-stack-extended-callgraph.tsv \
  "$build/entry-stack-extended-callgraph.tsv"
./scripts/check-entry-stack-budget.sh | tee "$build/entry-stack-budget.txt"
"$cc" -m64 -ffreestanding -fdebug-prefix-map="$repo_root"=. \
  -ffile-prefix-map="$repo_root"=. -g3 -c boot/boot.S -o "$build/boot.o"
"$cc" -m64 -ffreestanding -fdebug-prefix-map="$repo_root"=. \
  -ffile-prefix-map="$repo_root"=. -g3 -DLEANOS_PREEMPTION_SCENARIO=1 \
  -c boot/boot.S -o "$build/boot-preemption.o"
"$cc" -m64 -ffreestanding -fdebug-prefix-map="$repo_root"=. \
  -ffile-prefix-map="$repo_root"=. -g3 -DLEANOS_FRAME_BUDGET_SCENARIO=1 \
  -c boot/boot.S -o "$build/boot-frame-budget.o"
"$cc" -m64 -ffreestanding -fdebug-prefix-map="$repo_root"=. \
  -ffile-prefix-map="$repo_root"=. -g3 -DLEANOS_FAULT_CONTAINMENT_SCENARIO=1 \
  -c boot/boot.S -o "$build/boot-fault-containment.o"
"$cc" -m64 -ffreestanding -fdebug-prefix-map="$repo_root"=. \
  -ffile-prefix-map="$repo_root"=. -g3 -DLEANOS_FAULT_CONTAINMENT_SCENARIO=1 \
  -DLEANOS_PAGE_FAULT_PROBE_READONLY_WRITE=1 \
  -c boot/boot.S -o "$build/boot-fault-readonly-write.o"
"$cc" -m64 -ffreestanding -fdebug-prefix-map="$repo_root"=. \
  -ffile-prefix-map="$repo_root"=. -g3 -DLEANOS_FAULT_CONTAINMENT_SCENARIO=1 \
  -DLEANOS_PAGE_FAULT_PROBE_NX_EXECUTE=1 \
  -c boot/boot.S -o "$build/boot-fault-nx-execute.o"
for probe in "${fault_image_probes[@]}"; do
  "$cc" -m64 -ffreestanding -fdebug-prefix-map="$repo_root"=. \
    -ffile-prefix-map="$repo_root"=. -g3 \
    -DLEANOS_FAULT_CONTAINMENT_SCENARIO=1 \
    ${fault_fatal_probe_flags[$probe]} \
    -c boot/boot.S -o "$build/boot-fault-${probe}.o"
done
"$cc" -m64 -ffreestanding -fdebug-prefix-map="$repo_root"=. \
  -ffile-prefix-map="$repo_root"=. -g3 -DLEANOS_EXTENDED_STATE_SCENARIO=1 \
  -c boot/boot.S -o "$build/boot-extended-state.o"
"$cc" -m64 -ffreestanding -fdebug-prefix-map="$repo_root"=. \
  -ffile-prefix-map="$repo_root"=. -g3 -DLEANOS_EXTENDED_STATE_SCENARIO=1 \
  -DLEANOS_EXTENDED_STATE_MMX_PROBE=1 \
  -c boot/boot.S -o "$build/boot-extended-state-mmx.o"
"$cc" -m64 -ffreestanding -fdebug-prefix-map="$repo_root"=. \
  -ffile-prefix-map="$repo_root"=. -g3 -DLEANOS_EXTENDED_STATE_SCENARIO=1 \
  -DLEANOS_EXTENDED_STATE_SSE_PROBE=1 \
  -c boot/boot.S -o "$build/boot-extended-state-sse.o"
"$cc" -m64 -ffreestanding -fdebug-prefix-map="$repo_root"=. \
  -ffile-prefix-map="$repo_root"=. -g3 -DLEANOS_EXTENDED_STATE_SCENARIO=1 \
  -DLEANOS_EXTENDED_STATE_SSE2_PROBE=1 \
  -c boot/boot.S -o "$build/boot-extended-state-sse2.o"
"$cc" -m64 -ffreestanding -fdebug-prefix-map="$repo_root"=. \
  -ffile-prefix-map="$repo_root"=. -g3 -DLEANOS_EXTENDED_STATE_SCENARIO=1 \
  -DLEANOS_EXTENDED_STATE_AVX_PROBE=1 \
  -c boot/boot.S -o "$build/boot-extended-state-avx.o"
"$cc" -m64 -ffreestanding -fdebug-prefix-map="$repo_root"=. \
  -ffile-prefix-map="$repo_root"=. -g3 -DLEANOS_EXTENDED_STATE_SCENARIO=1 \
  -DLEANOS_EXTENDED_STATE_PEER_PKE_FIXTURE=1 \
  -c boot/boot.S -o "$build/boot-extended-state-peer-pke.o"
"$cc" -m64 -ffreestanding -fdebug-prefix-map="$repo_root"=. \
  -ffile-prefix-map="$repo_root"=. -g3 -DLEANOS_EXTENDED_STATE_SCENARIO=1 \
  -DLEANOS_FAST_ENTRY_SYSCALL_PROBE=1 \
  -c boot/boot.S -o "$build/boot-fast-entry-syscall.o"
"$cc" -m64 -ffreestanding -fdebug-prefix-map="$repo_root"=. \
  -ffile-prefix-map="$repo_root"=. -g3 -DLEANOS_EXTENDED_STATE_SCENARIO=1 \
  -DLEANOS_FAST_ENTRY_SYSENTER_PROBE=1 \
  -c boot/boot.S -o "$build/boot-fast-entry-sysenter.o"
"$cc" -m64 -ffreestanding -fdebug-prefix-map="$repo_root"=. \
  -ffile-prefix-map="$repo_root"=. -g3 -c boot/peer-pke-fixture.S \
  -o "$build/peer-pke-fixture.o"
"$cc" -m64 -ffreestanding -fdebug-prefix-map="$repo_root"=. \
  -ffile-prefix-map="$repo_root"=. -g3 -DLEANOS_RETURN_RESTORE_FIXTURE=1 \
  -c boot/boot.S -o "$build/boot-return-restore-fixture.o"
"$cc" -m64 -ffreestanding -fdebug-prefix-map="$repo_root"=. \
  -ffile-prefix-map="$repo_root"=. -g3 -DLEANOS_RETURN_BRANCH_FIXTURE=1 \
  -c boot/boot.S -o "$build/boot-return-branch-fixture.o"
"$cc" -m64 -ffreestanding -fdebug-prefix-map="$repo_root"=. \
  -ffile-prefix-map="$repo_root"=. -g3 -DLEANOS_RETURN_INDIRECT_FIXTURE=1 \
  -c boot/boot.S -o "$build/boot-return-indirect-fixture.o"
"$cc" -m64 -ffreestanding -fdebug-prefix-map="$repo_root"=. \
  -ffile-prefix-map="$repo_root"=. -g3 -DLEANOS_RETURN_INITIAL_INDIRECT_FIXTURE=1 \
  -c boot/boot.S -o "$build/boot-return-initial-indirect-fixture.o"
"$cc" -m64 -ffreestanding -fdebug-prefix-map="$repo_root"=. \
  -ffile-prefix-map="$repo_root"=. -g3 -DLEANOS_RETURN_POST_VALIDATE_QEMU_FIXTURE=1 \
  -c boot/boot.S -o "$build/boot-return-post-validation-qemu.o"
"$cc" -m64 -ffreestanding -fdebug-prefix-map="$repo_root"=. \
  -ffile-prefix-map="$repo_root"=. -g3 -DLEANOS_DF_MAP_GUARD=1 \
  -c boot/boot.S -o "$build/boot-df-guard-mapped.o"
"$cc" -m64 -ffreestanding -fdebug-prefix-map="$repo_root"=. \
  -ffile-prefix-map="$repo_root"=. -g3 -DLEANOS_ENTRY_STACK_OVERFLOW_PROBE=1 \
  -c boot/boot.S -o "$build/boot-entry-stack-overflow.o"
"$cc" -m64 -ffreestanding -fdebug-prefix-map="$repo_root"=. \
  -ffile-prefix-map="$repo_root"=. -g3 -DLEANOS_ENTRY_ADVERSARIAL=1 \
  -c boot/boot.S -o "$build/boot-entry-adversarial.o"
"$cc" -m64 -ffreestanding -fdebug-prefix-map="$repo_root"=. \
  -ffile-prefix-map="$repo_root"=. -g3 -DLEANOS_NMI_PROBE=1 \
  -c boot/boot.S -o "$build/boot-nmi.o"
"$cc" -m64 -ffreestanding -fdebug-prefix-map="$repo_root"=. \
  -ffile-prefix-map="$repo_root"=. -g3 -DLEANOS_BOOTSTRAP32_UD_PROBE=1 \
  -c boot/boot.S -o "$build/boot-bootstrap32-ud.o"
"$cc" -m64 -ffreestanding -fdebug-prefix-map="$repo_root"=. \
  -ffile-prefix-map="$repo_root"=. -g3 -DLEANOS_BOOTSTRAP64_NMI_PROBE=1 \
  -c boot/boot.S -o "$build/boot-bootstrap64-nmi.o"
for probe in "${direct_port_probes[@]}"; do
  "$cc" -m64 -ffreestanding -fdebug-prefix-map="$repo_root"=. \
    -ffile-prefix-map="$repo_root"=. -g3 \
    -DLEANOS_DIRECT_PORT_CONTAINMENT_SCENARIO=1 \
    ${direct_port_probe_flags[$probe]} \
    -c boot/boot.S -o "$build/boot-direct-port-${probe}.o"
done
for probe in "${integer_fault_probes[@]}"; do
  "$cc" -m64 -ffreestanding -fdebug-prefix-map="$repo_root"=. \
    -ffile-prefix-map="$repo_root"=. -g3 \
    -DLEANOS_INTEGER_FAULT_SCENARIO=1 \
    ${integer_fault_probe_flags[$probe]} \
    -c boot/boot.S -o "$build/boot-${probe}.o"
done

# The first link fixes every symbol address while using a same-sized plan
# placeholder. Lean then accepts the linker-resolved Input and emits the exact
# PTE arrays used by the guest walker. Recompiling only kernel.c preserves all
# section sizes; the final comparison rejects any unexpected address drift.
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-prelink.map" \
  -o "$build/leanos-prelink.elf" "$build/boot.o" "$build/kernel.o" \
  "$build/KernelTransition.o" "$build/Syscall.o" "$build/IPCSyscall.o" \
  "$build/Preemption.o" "$build/BootAllocation.o" "$build/Interrupt.o" "$build/InterruptEntry.o" \
  "$build/BlockingIPC.o" "$build/CapabilityReuse.o" "$build/ExtendedState.o" "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-malformed-handoff-prelink.map" \
  -o "$build/leanos-malformed-handoff-prelink.elf" "$build/boot.o" \
  "$build/kernel-malformed-handoff.o" "$build/KernelTransition.o" \
  "$build/Syscall.o" "$build/IPCSyscall.o" "$build/Preemption.o" \
  "$build/BootAllocation.o" "$build/Interrupt.o" "$build/InterruptEntry.o" \
  "$build/BlockingIPC.o" "$build/CapabilityReuse.o" "$build/ExtendedState.o" \
  "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-projection-authority-mutation-prelink.map" \
  -o "$build/leanos-projection-authority-mutation-prelink.elf" "$build/boot.o" \
  "$build/kernel-projection-authority-mutation.o" "$build/KernelTransition.o" \
  "$build/Syscall.o" "$build/IPCSyscall.o" "$build/Preemption.o" \
  "$build/BootAllocation.o" "$build/Interrupt.o" "$build/InterruptEntry.o" \
  "$build/BlockingIPC.o" "$build/CapabilityReuse.o" "$build/ExtendedState.o" \
  "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-raw-selection-authority-mutation-prelink.map" \
  -o "$build/leanos-raw-selection-authority-mutation-prelink.elf" "$build/boot.o" \
  "$build/kernel-raw-selection-authority-mutation.o" "$build/KernelTransition.o" \
  "$build/Syscall.o" "$build/IPCSyscall.o" "$build/Preemption.o" \
  "$build/BootAllocation.o" "$build/Interrupt.o" "$build/InterruptEntry.o" \
  "$build/BlockingIPC.o" "$build/CapabilityReuse.o" "$build/ExtendedState.o" \
  "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-preemption-prelink.map" \
  -o "$build/leanos-preemption-prelink.elf" "$build/boot-preemption.o" \
  "$build/kernel-preemption.o" "$build/KernelTransition.o" "$build/Syscall.o" \
  "$build/IPCSyscall.o" "$build/Preemption.o" "$build/BootAllocation.o" \
  "$build/Interrupt.o" "$build/InterruptEntry.o" "$build/BlockingIPC.o" \
  "$build/CapabilityReuse.o" "$build/ExtendedState.o" "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-frame-budget-prelink.map" \
  -o "$build/leanos-frame-budget-prelink.elf" "$build/boot-frame-budget.o" \
  "$build/kernel-frame-budget.o" "$build/KernelTransition.o" "$build/Syscall.o" \
  "$build/IPCSyscall.o" "$build/Preemption.o" "$build/BootAllocation.o" \
  "$build/Interrupt.o" "$build/InterruptEntry.o" "$build/BlockingIPC.o" \
  "$build/CapabilityReuse.o" "$build/ExtendedState.o" \
  "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-fault-containment-prelink.map" \
  -o "$build/leanos-fault-containment-prelink.elf" \
  "$build/boot-fault-containment.o" "$build/kernel-fault-containment.o" \
  "$build/KernelTransition.o" "$build/Syscall.o" "$build/IPCSyscall.o" \
  "$build/Preemption.o" "$build/BootAllocation.o" "$build/Interrupt.o" \
  "$build/InterruptEntry.o" "$build/BlockingIPC.o" \
  "$build/CapabilityReuse.o" "$build/ExtendedState.o" "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-fault-readonly-write-prelink.map" \
  -o "$build/leanos-fault-readonly-write-prelink.elf" \
  "$build/boot-fault-readonly-write.o" "$build/kernel-fault-containment.o" \
  "$build/KernelTransition.o" "$build/Syscall.o" "$build/IPCSyscall.o" \
  "$build/Preemption.o" "$build/BootAllocation.o" "$build/Interrupt.o" \
  "$build/InterruptEntry.o" "$build/BlockingIPC.o" \
  "$build/CapabilityReuse.o" "$build/ExtendedState.o" \
  "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-fault-nx-execute-prelink.map" \
  -o "$build/leanos-fault-nx-execute-prelink.elf" \
  "$build/boot-fault-nx-execute.o" "$build/kernel-fault-containment.o" \
  "$build/KernelTransition.o" "$build/Syscall.o" "$build/IPCSyscall.o" \
  "$build/Preemption.o" "$build/BootAllocation.o" "$build/Interrupt.o" \
  "$build/InterruptEntry.o" "$build/BlockingIPC.o" \
  "$build/CapabilityReuse.o" "$build/ExtendedState.o" \
  "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
for probe in "${fault_image_probes[@]}"; do
  ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
    -T boot/linker.ld -Map "$build/leanos-fault-${probe}-prelink.map" \
    -o "$build/leanos-fault-${probe}-prelink.elf" \
    "$build/boot-fault-${probe}.o" "$build/kernel-fault-${probe}.o" \
    "$build/KernelTransition.o" "$build/Syscall.o" "$build/IPCSyscall.o" \
    "$build/Preemption.o" "$build/BootAllocation.o" "$build/Interrupt.o" \
    "$build/InterruptEntry.o" "$build/BlockingIPC.o" \
    "$build/CapabilityReuse.o" "$build/ExtendedState.o" \
    "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
done
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-extended-state-prelink.map" \
  -o "$build/leanos-extended-state-prelink.elf" "$build/boot-extended-state.o" \
  "$build/kernel-extended-state.o" "$build/KernelTransition.o" "$build/Syscall.o" \
  "$build/IPCSyscall.o" "$build/Preemption.o" "$build/BootAllocation.o" \
  "$build/Interrupt.o" "$build/InterruptEntry.o" "$build/BlockingIPC.o" \
  "$build/CapabilityReuse.o" "$build/ExtendedState.o" "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-extended-state-mmx-prelink.map" \
  -o "$build/leanos-extended-state-mmx-prelink.elf" \
  "$build/boot-extended-state-mmx.o" "$build/kernel-extended-state.o" \
  "$build/KernelTransition.o" "$build/Syscall.o" "$build/IPCSyscall.o" \
  "$build/Preemption.o" "$build/BootAllocation.o" "$build/Interrupt.o" \
  "$build/InterruptEntry.o" "$build/BlockingIPC.o" \
  "$build/CapabilityReuse.o" "$build/ExtendedState.o" "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-extended-state-sse-prelink.map" \
  -o "$build/leanos-extended-state-sse-prelink.elf" \
  "$build/boot-extended-state-sse.o" "$build/kernel-extended-state.o" \
  "$build/KernelTransition.o" "$build/Syscall.o" "$build/IPCSyscall.o" \
  "$build/Preemption.o" "$build/BootAllocation.o" "$build/Interrupt.o" \
  "$build/InterruptEntry.o" "$build/BlockingIPC.o" \
  "$build/CapabilityReuse.o" "$build/ExtendedState.o" "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-extended-state-sse2-prelink.map" \
  -o "$build/leanos-extended-state-sse2-prelink.elf" \
  "$build/boot-extended-state-sse2.o" "$build/kernel-extended-state.o" \
  "$build/KernelTransition.o" "$build/Syscall.o" "$build/IPCSyscall.o" \
  "$build/Preemption.o" "$build/BootAllocation.o" "$build/Interrupt.o" \
  "$build/InterruptEntry.o" "$build/BlockingIPC.o" \
  "$build/CapabilityReuse.o" "$build/ExtendedState.o" "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-extended-state-avx-prelink.map" \
  -o "$build/leanos-extended-state-avx-prelink.elf" \
  "$build/boot-extended-state-avx.o" "$build/kernel-extended-state.o" \
  "$build/KernelTransition.o" "$build/Syscall.o" "$build/IPCSyscall.o" \
  "$build/Preemption.o" "$build/BootAllocation.o" "$build/Interrupt.o" \
  "$build/InterruptEntry.o" "$build/BlockingIPC.o" \
  "$build/CapabilityReuse.o" "$build/ExtendedState.o" "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-extended-state-peer-pke-prelink.map" \
  -o "$build/leanos-extended-state-peer-pke-prelink.elf" \
  "$build/boot-extended-state-peer-pke.o" "$build/peer-pke-fixture.o" \
  "$build/kernel-extended-state-peer-pke.o" "$build/KernelTransition.o" \
  "$build/Syscall.o" "$build/IPCSyscall.o" "$build/Preemption.o" \
  "$build/BootAllocation.o" "$build/Interrupt.o" "$build/InterruptEntry.o" \
  "$build/BlockingIPC.o" "$build/CapabilityReuse.o" "$build/ExtendedState.o" "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
for mechanism in syscall sysenter; do
  ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
    -T boot/linker.ld -Map "$build/leanos-fast-entry-${mechanism}-prelink.map" \
    -o "$build/leanos-fast-entry-${mechanism}-prelink.elf" \
    "$build/boot-fast-entry-${mechanism}.o" "$build/kernel-extended-state.o" \
    "$build/KernelTransition.o" "$build/Syscall.o" "$build/IPCSyscall.o" \
    "$build/Preemption.o" "$build/BootAllocation.o" "$build/Interrupt.o" \
    "$build/InterruptEntry.o" "$build/BlockingIPC.o" "$build/CapabilityReuse.o" \
    "$build/ExtendedState.o" "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
done
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-double-fault-prelink.map" \
  -o "$build/leanos-double-fault-prelink.elf" "$build/boot.o" \
  "$build/kernel-double-fault.o" "$build/KernelTransition.o" \
  "$build/Syscall.o" "$build/IPCSyscall.o" "$build/Preemption.o" \
  "$build/BootAllocation.o" "$build/Interrupt.o" "$build/InterruptEntry.o" \
  "$build/BlockingIPC.o" "$build/CapabilityReuse.o" "$build/ExtendedState.o" "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-entry-stack-overflow-prelink.map" \
  -o "$build/leanos-entry-stack-overflow-prelink.elf" \
  "$build/boot-entry-stack-overflow.o" "$build/kernel-double-fault.o" \
  "$build/KernelTransition.o" "$build/Syscall.o" "$build/IPCSyscall.o" \
  "$build/Preemption.o" "$build/BootAllocation.o" "$build/Interrupt.o" \
  "$build/InterruptEntry.o" "$build/BlockingIPC.o" "$build/CapabilityReuse.o" \
  "$build/ExtendedState.o" "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-entry-adversarial-prelink.map" \
  -o "$build/leanos-entry-adversarial-prelink.elf" "$build/boot-entry-adversarial.o" \
  "$build/kernel-entry-adversarial.o" "$build/KernelTransition.o" "$build/Syscall.o" \
  "$build/IPCSyscall.o" "$build/Preemption.o" "$build/BootAllocation.o" \
  "$build/Interrupt.o" "$build/InterruptEntry.o" "$build/BlockingIPC.o" \
  "$build/CapabilityReuse.o" "$build/ExtendedState.o" "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
for probe in "${direct_port_probes[@]}"; do
  ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
    -T boot/linker.ld -Map "$build/leanos-direct-port-${probe}-prelink.map" \
    -o "$build/leanos-direct-port-${probe}-prelink.elf" \
    "$build/boot-direct-port-${probe}.o" "$build/kernel-direct-port.o" \
    "$build/KernelTransition.o" "$build/Syscall.o" "$build/IPCSyscall.o" \
    "$build/Preemption.o" "$build/BootAllocation.o" "$build/Interrupt.o" \
    "$build/InterruptEntry.o" "$build/BlockingIPC.o" "$build/CapabilityReuse.o" \
    "$build/ExtendedState.o" "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
done
for probe in "${integer_fault_probes[@]}"; do
  ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
    -T boot/linker.ld -Map "$build/leanos-${probe}-prelink.map" \
    -o "$build/leanos-${probe}-prelink.elf" \
    "$build/boot-${probe}.o" "$build/kernel-integer-fault.o" \
    "$build/KernelTransition.o" "$build/Syscall.o" "$build/IPCSyscall.o" \
    "$build/Preemption.o" "$build/BootAllocation.o" "$build/Interrupt.o" \
    "$build/InterruptEntry.o" "$build/BlockingIPC.o" "$build/CapabilityReuse.o" \
    "$build/ExtendedState.o" "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
done
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-nmi-prelink.map" \
  -o "$build/leanos-nmi-prelink.elf" "$build/boot-nmi.o" \
  "$build/kernel-nmi.o" "$build/KernelTransition.o" "$build/Syscall.o" \
  "$build/IPCSyscall.o" "$build/Preemption.o" "$build/BootAllocation.o" \
  "$build/Interrupt.o" "$build/InterruptEntry.o" "$build/BlockingIPC.o" \
  "$build/CapabilityReuse.o" "$build/ExtendedState.o" \
  "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-bootstrap32-ud-prelink.map" \
  -o "$build/leanos-bootstrap32-ud-prelink.elf" "$build/boot-bootstrap32-ud.o" \
  "$build/kernel-bootstrap32-ud.o" "$build/KernelTransition.o" "$build/Syscall.o" \
  "$build/IPCSyscall.o" "$build/Preemption.o" "$build/BootAllocation.o" \
  "$build/Interrupt.o" "$build/InterruptEntry.o" "$build/BlockingIPC.o" \
  "$build/CapabilityReuse.o" "$build/ExtendedState.o" \
  "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-bootstrap64-nmi-prelink.map" \
  -o "$build/leanos-bootstrap64-nmi-prelink.elf" "$build/boot-bootstrap64-nmi.o" \
  "$build/kernel-bootstrap64-nmi.o" "$build/KernelTransition.o" "$build/Syscall.o" \
  "$build/IPCSyscall.o" "$build/Preemption.o" "$build/BootAllocation.o" \
  "$build/Interrupt.o" "$build/InterruptEntry.o" "$build/BlockingIPC.o" \
  "$build/CapabilityReuse.o" "$build/ExtendedState.o" \
  "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-guard-prelink.map" \
  -o "$build/leanos-guard-prelink.elf" "$build/boot-df-guard-mapped.o" \
  "$build/kernel-double-fault-guard-mapped.o" "$build/KernelTransition.o" \
  "$build/Syscall.o" "$build/IPCSyscall.o" "$build/Preemption.o" \
  "$build/BootAllocation.o" "$build/Interrupt.o" "$build/InterruptEntry.o" \
  "$build/BlockingIPC.o" "$build/CapabilityReuse.o" "$build/ExtendedState.o" "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
./scripts/generate-boot-page-plan.sh "$build/leanos-prelink.elf" \
  "$build/boot-page-plan.h"
./scripts/generate-boot-page-plan.sh "$build/leanos-malformed-handoff-prelink.elf" \
  "$build/boot-page-plan-malformed-handoff.h"
./scripts/generate-boot-page-plan.sh \
  "$build/leanos-projection-authority-mutation-prelink.elf" \
  "$build/boot-page-plan-projection-authority-mutation.h"
./scripts/generate-boot-page-plan.sh \
  "$build/leanos-raw-selection-authority-mutation-prelink.elf" \
  "$build/boot-page-plan-raw-selection-authority-mutation.h"
./scripts/generate-boot-page-plan.sh "$build/leanos-preemption-prelink.elf" \
  "$build/boot-page-plan-preemption.h"
./scripts/generate-boot-page-plan.sh "$build/leanos-frame-budget-prelink.elf" \
  "$build/boot-page-plan-frame-budget.h"
./scripts/generate-boot-page-plan.sh "$build/leanos-fault-containment-prelink.elf" \
  "$build/boot-page-plan-fault-containment.h"
./scripts/generate-boot-page-plan.sh \
  "$build/leanos-fault-readonly-write-prelink.elf" \
  "$build/boot-page-plan-fault-readonly-write.h"
cmp "$build/boot-page-plan-fault-containment.h" \
  "$build/boot-page-plan-fault-readonly-write.h" || {
  echo "error: read-only-write probe changed shared fault page-table plan" >&2
  exit 1
}
./scripts/generate-boot-page-plan.sh \
  "$build/leanos-fault-nx-execute-prelink.elf" \
  "$build/boot-page-plan-fault-nx-execute.h"
cmp "$build/boot-page-plan-fault-containment.h" \
  "$build/boot-page-plan-fault-nx-execute.h" || {
  echo "error: NX-execute probe changed shared fault page-table plan" >&2
  exit 1
}
for probe in "${fault_image_probes[@]}"; do
  ./scripts/generate-boot-page-plan.sh \
    "$build/leanos-fault-${probe}-prelink.elf" \
    "$build/boot-page-plan-fault-${probe}.h"
  if [[ "$probe" != stale-translation ]]; then
    cmp "$build/boot-page-plan-fault-containment.h" \
      "$build/boot-page-plan-fault-${probe}.h" || {
      echo "error: $probe probe changed shared fault page-table plan" >&2
      exit 1
    }
  fi
done
./scripts/generate-boot-page-plan.sh "$build/leanos-extended-state-prelink.elf" \
  "$build/boot-page-plan-extended-state.h"
./scripts/generate-boot-page-plan.sh "$build/leanos-extended-state-mmx-prelink.elf" \
  "$build/boot-page-plan-extended-state-mmx.h"
cmp "$build/boot-page-plan-extended-state.h" \
  "$build/boot-page-plan-extended-state-mmx.h" || {
  echo "error: MMX probe changed the shared extended-state page-table plan" >&2
  exit 1
}
./scripts/generate-boot-page-plan.sh "$build/leanos-extended-state-sse-prelink.elf" \
  "$build/boot-page-plan-extended-state-sse.h"
cmp "$build/boot-page-plan-extended-state.h" \
  "$build/boot-page-plan-extended-state-sse.h" || {
  echo "error: SSE probe changed the shared extended-state page-table plan" >&2
  exit 1
}
./scripts/generate-boot-page-plan.sh "$build/leanos-extended-state-sse2-prelink.elf" \
  "$build/boot-page-plan-extended-state-sse2.h"
cmp "$build/boot-page-plan-extended-state.h" \
  "$build/boot-page-plan-extended-state-sse2.h" || {
  echo "error: SSE2 probe changed the shared extended-state page-table plan" >&2
  exit 1
}
./scripts/generate-boot-page-plan.sh "$build/leanos-extended-state-avx-prelink.elf" \
  "$build/boot-page-plan-extended-state-avx.h"
cmp "$build/boot-page-plan-extended-state.h" \
  "$build/boot-page-plan-extended-state-avx.h" || {
  echo "error: AVX probe changed the shared extended-state page-table plan" >&2
  exit 1
}
./scripts/generate-boot-page-plan.sh \
  "$build/leanos-extended-state-peer-pke-prelink.elf" \
  "$build/boot-page-plan-extended-state-peer-pke.h"
for mechanism in syscall sysenter; do
  ./scripts/generate-boot-page-plan.sh \
    "$build/leanos-fast-entry-${mechanism}-prelink.elf" \
    "$build/boot-page-plan-fast-entry-${mechanism}.h"
  cmp "$build/boot-page-plan-extended-state.h" \
    "$build/boot-page-plan-fast-entry-${mechanism}.h" || {
    echo "error: fast-entry $mechanism probe changed the shared page-table plan" >&2
    exit 1
  }
done
./scripts/generate-boot-page-plan.sh "$build/leanos-double-fault-prelink.elf" \
  "$build/boot-page-plan-double-fault.h"
./scripts/generate-boot-page-plan.sh "$build/leanos-entry-stack-overflow-prelink.elf" \
  "$build/boot-page-plan-entry-overflow.h"
./scripts/generate-boot-page-plan.sh "$build/leanos-guard-prelink.elf" \
  "$build/boot-page-plan-guard.h"
./scripts/generate-boot-page-plan.sh "$build/leanos-entry-adversarial-prelink.elf" \
  "$build/boot-page-plan-entry-adversarial.h"
./scripts/generate-boot-page-plan.sh \
  "$build/leanos-direct-port-serial-prelink.elf" \
  "$build/boot-page-plan-direct-port.h"
for probe in debug in pic; do
  ./scripts/generate-boot-page-plan.sh \
    "$build/leanos-direct-port-${probe}-prelink.elf" \
    "$build/boot-page-plan-direct-port-${probe}.h"
  cmp "$build/boot-page-plan-direct-port.h" \
    "$build/boot-page-plan-direct-port-${probe}.h" || {
    echo "error: direct-port $probe probe changed the shared page-table plan" >&2
    exit 1
  }
done
./scripts/generate-boot-page-plan.sh \
  "$build/leanos-divide-error-prelink.elf" \
  "$build/boot-page-plan-integer-fault.h"
./scripts/generate-boot-page-plan.sh \
  "$build/leanos-breakpoint-prelink.elf" \
  "$build/boot-page-plan-breakpoint.h"
cmp "$build/boot-page-plan-integer-fault.h" \
  "$build/boot-page-plan-breakpoint.h" || {
  echo "error: breakpoint probe changed the shared integer-fault page-table plan" >&2
  exit 1
}
./scripts/generate-boot-page-plan.sh "$build/leanos-nmi-prelink.elf" \
  "$build/boot-page-plan-nmi.h"
./scripts/generate-boot-page-plan.sh "$build/leanos-bootstrap32-ud-prelink.elf" \
  "$build/boot-page-plan-bootstrap32-ud.h"
./scripts/generate-boot-page-plan.sh "$build/leanos-bootstrap64-nmi-prelink.elf" \
  "$build/boot-page-plan-bootstrap64-nmi.h"
"$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
  -DLEANOS_ENTRY_HIGH_WATER=1 -c boot/kernel.c \
  -o "$build/kernel.o"
"$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
  -DLEANOS_MALFORMED_HANDOFF_FIXTURE=1 \
  -DLEANOS_BOOT_PAGE_PLAN_HEADER='"boot-page-plan-malformed-handoff.h"' \
  -c boot/kernel.c -o "$build/kernel-malformed-handoff.o"
"$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
  -DLEANOS_PROJECTION_SELECTION_MUTATION_FIXTURE=1 \
  -DLEANOS_BOOT_PAGE_PLAN_HEADER='"boot-page-plan-projection-authority-mutation.h"' \
  -c boot/kernel.c -o "$build/kernel-projection-authority-mutation.o"
"$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
  -DLEANOS_RAW_SELECTION_MUTATION_FIXTURE=1 \
  -DLEANOS_BOOT_PAGE_PLAN_HEADER='"boot-page-plan-raw-selection-authority-mutation.h"' \
  -c boot/kernel.c -o "$build/kernel-raw-selection-authority-mutation.o"
"$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
  -DLEANOS_PREEMPTION_SCENARIO=1 -DLEANOS_ENTRY_HIGH_WATER=1 \
  -DLEANOS_BOOT_PAGE_PLAN_HEADER='"boot-page-plan-preemption.h"' \
  -c boot/kernel.c -o "$build/kernel-preemption.o"
"$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
  -DLEANOS_FRAME_BUDGET_SCENARIO=1 \
  -DLEANOS_BOOT_PAGE_PLAN_HEADER='"boot-page-plan-frame-budget.h"' \
  -c boot/kernel.c -o "$build/kernel-frame-budget.o"
"$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
  -DLEANOS_FAULT_CONTAINMENT_SCENARIO=1 \
  -DLEANOS_BOOT_PAGE_PLAN_HEADER='"boot-page-plan-fault-containment.h"' \
  -c boot/kernel.c -o "$build/kernel-fault-containment.o"
for probe in "${fault_image_probes[@]}"; do
  fault_plan_header="boot-page-plan-fault-containment.h"
  if [[ "$probe" == stale-translation ]]; then
    fault_plan_header="boot-page-plan-fault-stale-translation.h"
  fi
  "$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
    -DLEANOS_FAULT_CONTAINMENT_SCENARIO=1 \
    "${fault_fatal_probe_flags[$probe]}" \
    -DLEANOS_BOOT_PAGE_PLAN_HEADER="\"${fault_plan_header}\"" \
    -c boot/kernel.c -o "$build/kernel-fault-${probe}.o"
done
"$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
  -DLEANOS_EXTENDED_STATE_SCENARIO=1 \
  -DLEANOS_BOOT_PAGE_PLAN_HEADER='"boot-page-plan-extended-state.h"' \
  -c boot/kernel.c -o "$build/kernel-extended-state.o"
"$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
  -DLEANOS_EXTENDED_STATE_SCENARIO=1 \
  -DLEANOS_EXTENDED_STATE_PEER_PKE_FIXTURE=1 \
  -DLEANOS_BOOT_PAGE_PLAN_HEADER='"boot-page-plan-extended-state-peer-pke.h"' \
  -c boot/kernel.c -o "$build/kernel-extended-state-peer-pke.o"
if nm "$build/kernel.o" | grep -Eq \
    'return_corruption_mode|return_corruption_name|inject_return_corruption'; then
  echo "error: normal kernel object contains return-corruption fixture code" >&2
  exit 1
fi
for spec in "${return_corruptions[@]}"; do
  IFS=: read -r fixture mode _reason <<<"$spec"
  "$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
    -DLEANOS_RETURN_CORRUPTION_MODE="$mode" -c boot/kernel.c \
    -o "$build/kernel-return-${fixture}.o"
done
"$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
  -DLEANOS_DOUBLE_FAULT_PROBE=1 -c boot/kernel.c -o "$build/kernel-double-fault.o"
"$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
  -DLEANOS_DOUBLE_FAULT_PROBE=1 \
  -DLEANOS_BOOT_PAGE_PLAN_HEADER='"boot-page-plan-entry-overflow.h"' \
  -c boot/kernel.c -o "$build/kernel-entry-stack-overflow.o"
"$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
  -DLEANOS_DOUBLE_FAULT_PROBE=1 -DLEANOS_DF_MAP_GUARD=1 \
  -c boot/kernel.c -o "$build/kernel-double-fault-guard-mapped.o"
"$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
  -DLEANOS_ENTRY_ADVERSARIAL=1 \
  -DLEANOS_BOOT_PAGE_PLAN_HEADER='"boot-page-plan-entry-adversarial.h"' \
  -c boot/kernel.c -o "$build/kernel-entry-adversarial.o"
"$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
  -DLEANOS_NMI_PROBE=1 \
  -DLEANOS_BOOT_PAGE_PLAN_HEADER='"boot-page-plan-nmi.h"' \
  -c boot/kernel.c -o "$build/kernel-nmi.o"
"$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
  -DLEANOS_ENTRY_HIGH_WATER=1 \
  -DLEANOS_BOOT_PAGE_PLAN_HEADER='"boot-page-plan-bootstrap32-ud.h"' \
  -c boot/kernel.c -o "$build/kernel-bootstrap32-ud.o"
"$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
  -DLEANOS_ENTRY_HIGH_WATER=1 \
  -DLEANOS_BOOT_PAGE_PLAN_HEADER='"boot-page-plan-bootstrap64-nmi.h"' \
  -c boot/kernel.c -o "$build/kernel-bootstrap64-nmi.o"
"$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
  -DLEANOS_DIRECT_PORT_CONTAINMENT_SCENARIO=1 \
  -DLEANOS_BOOT_PAGE_PLAN_HEADER='"boot-page-plan-direct-port.h"' \
  -c boot/kernel.c -o "$build/kernel-direct-port.o"
"$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
  -DLEANOS_INTEGER_FAULT_SCENARIO=1 \
  -DLEANOS_BOOT_PAGE_PLAN_HEADER='"boot-page-plan-integer-fault.h"' \
  -c boot/kernel.c -o "$build/kernel-integer-fault.o"

ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map build/boot/leanos.map \
  -o build/boot/leanos.elf build/boot/boot.o build/boot/kernel.o \
  build/boot/KernelTransition.o build/boot/Syscall.o build/boot/IPCSyscall.o \
  build/boot/Preemption.o build/boot/BootAllocation.o build/boot/Interrupt.o build/boot/InterruptEntry.o \
  build/boot/BlockingIPC.o build/boot/CapabilityReuse.o build/boot/ExtendedState.o build/boot/PrivilegeEntryControl.o build/boot/FaultDispatch.o
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-malformed-handoff.map" \
  -o "$build/leanos-malformed-handoff.elf" "$build/boot.o" \
  "$build/kernel-malformed-handoff.o" "$build/KernelTransition.o" \
  "$build/Syscall.o" "$build/IPCSyscall.o" "$build/Preemption.o" \
  "$build/BootAllocation.o" "$build/Interrupt.o" "$build/InterruptEntry.o" \
  "$build/BlockingIPC.o" "$build/CapabilityReuse.o" "$build/ExtendedState.o" \
  "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-projection-authority-mutation.map" \
  -o "$build/leanos-projection-authority-mutation.elf" "$build/boot.o" \
  "$build/kernel-projection-authority-mutation.o" "$build/KernelTransition.o" \
  "$build/Syscall.o" "$build/IPCSyscall.o" "$build/Preemption.o" \
  "$build/BootAllocation.o" "$build/Interrupt.o" "$build/InterruptEntry.o" \
  "$build/BlockingIPC.o" "$build/CapabilityReuse.o" "$build/ExtendedState.o" \
  "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-raw-selection-authority-mutation.map" \
  -o "$build/leanos-raw-selection-authority-mutation.elf" "$build/boot.o" \
  "$build/kernel-raw-selection-authority-mutation.o" "$build/KernelTransition.o" \
  "$build/Syscall.o" "$build/IPCSyscall.o" "$build/Preemption.o" \
  "$build/BootAllocation.o" "$build/Interrupt.o" "$build/InterruptEntry.o" \
  "$build/BlockingIPC.o" "$build/CapabilityReuse.o" "$build/ExtendedState.o" \
  "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-entry-adversarial.map" \
  -o "$build/leanos-entry-adversarial.elf" "$build/boot-entry-adversarial.o" \
  "$build/kernel-entry-adversarial.o" "$build/KernelTransition.o" "$build/Syscall.o" \
  "$build/IPCSyscall.o" "$build/Preemption.o" "$build/BootAllocation.o" \
  "$build/Interrupt.o" "$build/InterruptEntry.o" "$build/BlockingIPC.o" \
  "$build/CapabilityReuse.o" "$build/ExtendedState.o" "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
for probe in "${direct_port_probes[@]}"; do
  ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
    -T boot/linker.ld -Map "$build/leanos-direct-port-${probe}.map" \
    -o "$build/leanos-direct-port-${probe}.elf" \
    "$build/boot-direct-port-${probe}.o" "$build/kernel-direct-port.o" \
    "$build/KernelTransition.o" "$build/Syscall.o" "$build/IPCSyscall.o" \
    "$build/Preemption.o" "$build/BootAllocation.o" "$build/Interrupt.o" \
    "$build/InterruptEntry.o" "$build/BlockingIPC.o" "$build/CapabilityReuse.o" \
    "$build/ExtendedState.o" "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
done
for probe in "${integer_fault_probes[@]}"; do
  ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
    -T boot/linker.ld -Map "$build/leanos-${probe}.map" \
    -o "$build/leanos-${probe}.elf" \
    "$build/boot-${probe}.o" "$build/kernel-integer-fault.o" \
    "$build/KernelTransition.o" "$build/Syscall.o" "$build/IPCSyscall.o" \
    "$build/Preemption.o" "$build/BootAllocation.o" "$build/Interrupt.o" \
    "$build/InterruptEntry.o" "$build/BlockingIPC.o" "$build/CapabilityReuse.o" \
    "$build/ExtendedState.o" "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
done
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-nmi.map" \
  -o "$build/leanos-nmi.elf" "$build/boot-nmi.o" "$build/kernel-nmi.o" \
  "$build/KernelTransition.o" "$build/Syscall.o" "$build/IPCSyscall.o" \
  "$build/Preemption.o" "$build/BootAllocation.o" "$build/Interrupt.o" \
  "$build/InterruptEntry.o" "$build/BlockingIPC.o" \
  "$build/CapabilityReuse.o" "$build/ExtendedState.o" \
  "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-bootstrap32-ud.map" \
  -o "$build/leanos-bootstrap32-ud.elf" "$build/boot-bootstrap32-ud.o" \
  "$build/kernel-bootstrap32-ud.o" "$build/KernelTransition.o" "$build/Syscall.o" \
  "$build/IPCSyscall.o" "$build/Preemption.o" "$build/BootAllocation.o" \
  "$build/Interrupt.o" "$build/InterruptEntry.o" "$build/BlockingIPC.o" \
  "$build/CapabilityReuse.o" "$build/ExtendedState.o" \
  "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-bootstrap64-nmi.map" \
  -o "$build/leanos-bootstrap64-nmi.elf" "$build/boot-bootstrap64-nmi.o" \
  "$build/kernel-bootstrap64-nmi.o" "$build/KernelTransition.o" "$build/Syscall.o" \
  "$build/IPCSyscall.o" "$build/Preemption.o" "$build/BootAllocation.o" \
  "$build/Interrupt.o" "$build/InterruptEntry.o" "$build/BlockingIPC.o" \
  "$build/CapabilityReuse.o" "$build/ExtendedState.o" \
  "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-preemption.map" \
  -o "$build/leanos-preemption.elf" "$build/boot-preemption.o" \
  "$build/kernel-preemption.o" "$build/KernelTransition.o" "$build/Syscall.o" \
  "$build/IPCSyscall.o" "$build/Preemption.o" "$build/BootAllocation.o" \
  "$build/Interrupt.o" "$build/InterruptEntry.o" "$build/BlockingIPC.o" \
  "$build/CapabilityReuse.o" "$build/ExtendedState.o" "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-frame-budget.map" \
  -o "$build/leanos-frame-budget.elf" "$build/boot-frame-budget.o" \
  "$build/kernel-frame-budget.o" "$build/KernelTransition.o" "$build/Syscall.o" \
  "$build/IPCSyscall.o" "$build/Preemption.o" "$build/BootAllocation.o" \
  "$build/Interrupt.o" "$build/InterruptEntry.o" "$build/BlockingIPC.o" \
  "$build/CapabilityReuse.o" "$build/ExtendedState.o" \
  "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-fault-containment.map" \
  -o "$build/leanos-fault-containment.elf" "$build/boot-fault-containment.o" \
  "$build/kernel-fault-containment.o" "$build/KernelTransition.o" \
  "$build/Syscall.o" "$build/IPCSyscall.o" "$build/Preemption.o" \
  "$build/BootAllocation.o" "$build/Interrupt.o" "$build/InterruptEntry.o" \
  "$build/BlockingIPC.o" "$build/CapabilityReuse.o" \
  "$build/ExtendedState.o" "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-fault-readonly-write.map" \
  -o "$build/leanos-fault-readonly-write.elf" \
  "$build/boot-fault-readonly-write.o" "$build/kernel-fault-containment.o" \
  "$build/KernelTransition.o" "$build/Syscall.o" "$build/IPCSyscall.o" \
  "$build/Preemption.o" "$build/BootAllocation.o" "$build/Interrupt.o" \
  "$build/InterruptEntry.o" "$build/BlockingIPC.o" \
  "$build/CapabilityReuse.o" "$build/ExtendedState.o" \
  "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-fault-nx-execute.map" \
  -o "$build/leanos-fault-nx-execute.elf" \
  "$build/boot-fault-nx-execute.o" "$build/kernel-fault-containment.o" \
  "$build/KernelTransition.o" "$build/Syscall.o" "$build/IPCSyscall.o" \
  "$build/Preemption.o" "$build/BootAllocation.o" "$build/Interrupt.o" \
  "$build/InterruptEntry.o" "$build/BlockingIPC.o" \
  "$build/CapabilityReuse.o" "$build/ExtendedState.o" \
  "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
for probe in "${fault_image_probes[@]}"; do
  ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
    -T boot/linker.ld -Map "$build/leanos-fault-${probe}.map" \
    -o "$build/leanos-fault-${probe}.elf" \
    "$build/boot-fault-${probe}.o" "$build/kernel-fault-${probe}.o" \
    "$build/KernelTransition.o" "$build/Syscall.o" "$build/IPCSyscall.o" \
    "$build/Preemption.o" "$build/BootAllocation.o" "$build/Interrupt.o" \
    "$build/InterruptEntry.o" "$build/BlockingIPC.o" \
    "$build/CapabilityReuse.o" "$build/ExtendedState.o" \
    "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
done
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-extended-state.map" \
  -o "$build/leanos-extended-state.elf" "$build/boot-extended-state.o" \
  "$build/kernel-extended-state.o" "$build/KernelTransition.o" "$build/Syscall.o" \
  "$build/IPCSyscall.o" "$build/Preemption.o" "$build/BootAllocation.o" \
  "$build/Interrupt.o" "$build/InterruptEntry.o" "$build/BlockingIPC.o" \
  "$build/CapabilityReuse.o" "$build/ExtendedState.o" "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-extended-state-mmx.map" \
  -o "$build/leanos-extended-state-mmx.elf" \
  "$build/boot-extended-state-mmx.o" "$build/kernel-extended-state.o" \
  "$build/KernelTransition.o" "$build/Syscall.o" "$build/IPCSyscall.o" \
  "$build/Preemption.o" "$build/BootAllocation.o" "$build/Interrupt.o" \
  "$build/InterruptEntry.o" "$build/BlockingIPC.o" \
  "$build/CapabilityReuse.o" "$build/ExtendedState.o" "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-extended-state-sse.map" \
  -o "$build/leanos-extended-state-sse.elf" \
  "$build/boot-extended-state-sse.o" "$build/kernel-extended-state.o" \
  "$build/KernelTransition.o" "$build/Syscall.o" "$build/IPCSyscall.o" \
  "$build/Preemption.o" "$build/BootAllocation.o" "$build/Interrupt.o" \
  "$build/InterruptEntry.o" "$build/BlockingIPC.o" \
  "$build/CapabilityReuse.o" "$build/ExtendedState.o" "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-extended-state-sse2.map" \
  -o "$build/leanos-extended-state-sse2.elf" \
  "$build/boot-extended-state-sse2.o" "$build/kernel-extended-state.o" \
  "$build/KernelTransition.o" "$build/Syscall.o" "$build/IPCSyscall.o" \
  "$build/Preemption.o" "$build/BootAllocation.o" "$build/Interrupt.o" \
  "$build/InterruptEntry.o" "$build/BlockingIPC.o" \
  "$build/CapabilityReuse.o" "$build/ExtendedState.o" "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-extended-state-avx.map" \
  -o "$build/leanos-extended-state-avx.elf" \
  "$build/boot-extended-state-avx.o" "$build/kernel-extended-state.o" \
  "$build/KernelTransition.o" "$build/Syscall.o" "$build/IPCSyscall.o" \
  "$build/Preemption.o" "$build/BootAllocation.o" "$build/Interrupt.o" \
  "$build/InterruptEntry.o" "$build/BlockingIPC.o" \
  "$build/CapabilityReuse.o" "$build/ExtendedState.o" "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-extended-state-peer-pke.map" \
  -o "$build/leanos-extended-state-peer-pke.elf" \
  "$build/boot-extended-state-peer-pke.o" "$build/peer-pke-fixture.o" \
  "$build/kernel-extended-state-peer-pke.o" "$build/KernelTransition.o" \
  "$build/Syscall.o" "$build/IPCSyscall.o" "$build/Preemption.o" \
  "$build/BootAllocation.o" "$build/Interrupt.o" "$build/InterruptEntry.o" \
  "$build/BlockingIPC.o" "$build/CapabilityReuse.o" "$build/ExtendedState.o" "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
for mechanism in syscall sysenter; do
  ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
    -T boot/linker.ld -Map "$build/leanos-fast-entry-${mechanism}.map" \
    -o "$build/leanos-fast-entry-${mechanism}.elf" \
    "$build/boot-fast-entry-${mechanism}.o" "$build/kernel-extended-state.o" \
    "$build/KernelTransition.o" "$build/Syscall.o" "$build/IPCSyscall.o" \
    "$build/Preemption.o" "$build/BootAllocation.o" "$build/Interrupt.o" \
    "$build/InterruptEntry.o" "$build/BlockingIPC.o" "$build/CapabilityReuse.o" \
    "$build/ExtendedState.o" "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
done

for spec in "${return_corruptions[@]}"; do
  IFS=: read -r fixture mode _reason <<<"$spec"
  boot_object="$build/boot.o"
  if [[ "$fixture" == post-validation-mutation ]]; then
    boot_object="$build/boot-return-post-validation-qemu.o"
  fi
  ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
    -T boot/linker.ld -Map "$build/leanos-return-${fixture}-prelink.map" \
    -o "$build/leanos-return-${fixture}-prelink.elf" "$boot_object" \
    "$build/kernel-return-${fixture}.o" "$build/KernelTransition.o" \
    "$build/Syscall.o" "$build/IPCSyscall.o" "$build/Preemption.o" \
    "$build/BootAllocation.o" "$build/Interrupt.o" "$build/InterruptEntry.o" \
    "$build/BlockingIPC.o" "$build/CapabilityReuse.o" "$build/ExtendedState.o" "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
  ./scripts/generate-boot-page-plan.sh "$build/leanos-return-${fixture}-prelink.elf" \
    "$build/boot-page-plan-return-${fixture}.h"
  "$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
    -DLEANOS_RETURN_CORRUPTION_MODE="$mode" \
    -DLEANOS_BOOT_PAGE_PLAN_HEADER="\"boot-page-plan-return-${fixture}.h\"" \
    -c boot/kernel.c -o "$build/kernel-return-${fixture}.o"
  ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
    -T boot/linker.ld -Map "$build/leanos-return-${fixture}.map" \
    -o "$build/leanos-return-${fixture}.elf" "$boot_object" \
    "$build/kernel-return-${fixture}.o" "$build/KernelTransition.o" \
    "$build/Syscall.o" "$build/IPCSyscall.o" "$build/Preemption.o" \
    "$build/BootAllocation.o" "$build/Interrupt.o" "$build/InterruptEntry.o" \
    "$build/BlockingIPC.o" "$build/CapabilityReuse.o" "$build/ExtendedState.o" "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
  ./scripts/generate-boot-page-plan.sh "$build/leanos-return-${fixture}.elf" \
    "$build/boot-page-plan-return-${fixture}.final.h"
  cmp "$build/boot-page-plan-return-${fixture}.h" \
    "$build/boot-page-plan-return-${fixture}.final.h" || {
    echo "error: ${fixture} boot page-table plan drifted after final link" >&2
    exit 1
  }
  if [[ "$fixture" == post-validation-mutation ]]; then
    if ./scripts/check-image-policy.sh "$build/leanos-return-${fixture}.elf" \
        >"$build/return-${fixture}-policy.log" 2>&1; then
      echo "error: post-validation mutation policy fixture unexpectedly passed" >&2
      exit 1
    fi
    grep -Fq 'mutation or control flow added after user-return validation' \
      "$build/return-${fixture}-policy.log" || {
      echo "error: post-validation fixture lacked policy diagnostic" >&2; exit 1;
    }
  elif [[ "$fixture" == fast-entry-sce-relaxation ||
      "$fixture" == fast-entry-lstar-relaxation ||
      "$fixture" == fast-entry-sysenter-eip-relaxation ||
      "$fixture" == fast-entry-star-relaxation ||
      "$fixture" == fast-entry-cstar-relaxation ||
      "$fixture" == fast-entry-sfmask-relaxation ||
      "$fixture" == fast-entry-sysenter-cs-relaxation ||
      "$fixture" == fast-entry-sysenter-esp-relaxation ]]; then
    if ./scripts/check-image-policy.sh "$build/leanos-return-${fixture}.elf" \
        >"$build/return-${fixture}-policy.log" 2>&1; then
      echo "error: fast-entry relaxation policy fixture unexpectedly passed" >&2
      exit 1
    fi
    grep -Fq 'fast-entry final-ELF write inventory drifted' \
      "$build/return-${fixture}-policy.log" || {
      echo "error: fast-entry relaxation fixture lacked write-inventory diagnostic" >&2
      exit 1
    }
  else
    ./scripts/check-image-policy.sh "$build/leanos-return-${fixture}.elf"
  fi
done

./scripts/generate-boot-page-plan.sh "$build/leanos.elf" \
  "$build/boot-page-plan.final.h"
cmp "$build/boot-page-plan.h" "$build/boot-page-plan.final.h" || {
  echo "error: linker-resolved boot page-table plan drifted after final link" >&2
  exit 1
}
./scripts/generate-boot-page-plan.sh "$build/leanos-malformed-handoff.elf" \
  "$build/boot-page-plan-malformed-handoff.final.h"
cmp "$build/boot-page-plan-malformed-handoff.h" \
  "$build/boot-page-plan-malformed-handoff.final.h" || {
  echo "error: malformed-handoff page-table plan drifted after final link" >&2
  exit 1
}
./scripts/generate-boot-page-plan.sh \
  "$build/leanos-projection-authority-mutation.elf" \
  "$build/boot-page-plan-projection-authority-mutation.final.h"
cmp "$build/boot-page-plan-projection-authority-mutation.h" \
  "$build/boot-page-plan-projection-authority-mutation.final.h" || {
  echo "error: projection-authority mutation page-table plan drifted after final link" >&2
  exit 1
}
./scripts/generate-boot-page-plan.sh \
  "$build/leanos-raw-selection-authority-mutation.elf" \
  "$build/boot-page-plan-raw-selection-authority-mutation.final.h"
cmp "$build/boot-page-plan-raw-selection-authority-mutation.h" \
  "$build/boot-page-plan-raw-selection-authority-mutation.final.h" || {
  echo "error: raw-selection authority mutation page-table plan drifted after final link" >&2
  exit 1
}
./scripts/generate-boot-page-plan.sh "$build/leanos-nmi.elf" \
  "$build/boot-page-plan-nmi.final.h"
cmp "$build/boot-page-plan-nmi.h" "$build/boot-page-plan-nmi.final.h" || {
  echo "error: NMI probe boot page-table plan drifted after final link" >&2
  exit 1
}
./scripts/generate-boot-page-plan.sh "$build/leanos-bootstrap32-ud.elf" \
  "$build/boot-page-plan-bootstrap32-ud.final.h"
cmp "$build/boot-page-plan-bootstrap32-ud.h" \
  "$build/boot-page-plan-bootstrap32-ud.final.h" || {
  echo "error: bootstrap32-ud probe page-table plan drifted after final link" >&2
  exit 1
}
./scripts/generate-boot-page-plan.sh "$build/leanos-bootstrap64-nmi.elf" \
  "$build/boot-page-plan-bootstrap64-nmi.final.h"
cmp "$build/boot-page-plan-bootstrap64-nmi.h" \
  "$build/boot-page-plan-bootstrap64-nmi.final.h" || {
  echo "error: bootstrap64-nmi probe page-table plan drifted after final link" >&2
  exit 1
}
./scripts/generate-boot-page-plan.sh "$build/leanos-preemption.elf" \
  "$build/boot-page-plan-preemption.final.h"
cmp "$build/boot-page-plan-preemption.h" \
  "$build/boot-page-plan-preemption.final.h" || {
  echo "error: preemption boot page-table plan drifted after final link" >&2
  exit 1
}
frame_budget_plan_converged=false
for pass in 1 2 3 4; do
  ./scripts/generate-boot-page-plan.sh "$build/leanos-frame-budget.elf" \
    "$build/boot-page-plan-frame-budget.final.h"
  if cmp -s "$build/boot-page-plan-frame-budget.h" \
      "$build/boot-page-plan-frame-budget.final.h"; then
    frame_budget_plan_converged=true
    break
  fi
  [[ "$pass" -lt 4 ]] || break

  # Clang can change a page-boundary comparison after the linker-derived plan
  # replaces the fixed-size stub. Rebuild to a bounded fixed point instead of
  # accepting a plan that describes the preceding ELF.
  cp "$build/boot-page-plan-frame-budget.final.h" \
    "$build/boot-page-plan-frame-budget.h"
  "$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
    -DLEANOS_FRAME_BUDGET_SCENARIO=1 \
    -DLEANOS_BOOT_PAGE_PLAN_HEADER='"boot-page-plan-frame-budget.h"' \
    -c boot/kernel.c -o "$build/kernel-frame-budget.o"
  ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
    -T boot/linker.ld -Map "$build/leanos-frame-budget.map" \
    -o "$build/leanos-frame-budget.elf" "$build/boot-frame-budget.o" \
    "$build/kernel-frame-budget.o" "$build/KernelTransition.o" \
    "$build/Syscall.o" "$build/IPCSyscall.o" "$build/Preemption.o" \
    "$build/BootAllocation.o" "$build/Interrupt.o" \
    "$build/InterruptEntry.o" "$build/BlockingIPC.o" \
    "$build/CapabilityReuse.o" "$build/ExtendedState.o" \
    "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
done
[[ "$frame_budget_plan_converged" == true ]] || {
  echo "error: frame-budget boot page-table plan drifted after final link" >&2
  exit 1
}
./scripts/generate-boot-page-plan.sh "$build/leanos-fault-containment.elf" \
  "$build/boot-page-plan-fault-containment.final.h"
cmp "$build/boot-page-plan-fault-containment.h" \
  "$build/boot-page-plan-fault-containment.final.h" || {
  echo "error: fault-containment boot page-table plan drifted after final link" >&2
  exit 1
}
./scripts/generate-boot-page-plan.sh "$build/leanos-fault-readonly-write.elf" \
  "$build/boot-page-plan-fault-readonly-write.final.h"
cmp "$build/boot-page-plan-fault-containment.h" \
  "$build/boot-page-plan-fault-readonly-write.final.h" || {
  echo "error: read-only-write page-table plan drifted after final link" >&2
  exit 1
}
./scripts/generate-boot-page-plan.sh "$build/leanos-fault-nx-execute.elf" \
  "$build/boot-page-plan-fault-nx-execute.final.h"
cmp "$build/boot-page-plan-fault-containment.h" \
  "$build/boot-page-plan-fault-nx-execute.final.h" || {
  echo "error: NX-execute page-table plan drifted after final link" >&2
  exit 1
}
for probe in "${fault_image_probes[@]}"; do
  ./scripts/generate-boot-page-plan.sh "$build/leanos-fault-${probe}.elf" \
    "$build/boot-page-plan-fault-${probe}.final.h"
  expected_fault_plan="$build/boot-page-plan-fault-containment.h"
  if [[ "$probe" == stale-translation ]]; then
    expected_fault_plan="$build/boot-page-plan-fault-stale-translation.h"
  fi
  cmp "$expected_fault_plan" \
    "$build/boot-page-plan-fault-${probe}.final.h" || {
    echo "error: $probe page-table plan drifted after final link" >&2
    exit 1
  }
done
./scripts/generate-boot-page-plan.sh "$build/leanos-extended-state.elf" \
  "$build/boot-page-plan-extended-state.final.h"
cmp "$build/boot-page-plan-extended-state.h" \
  "$build/boot-page-plan-extended-state.final.h" || {
  echo "error: extended-state boot page-table plan drifted after final link" >&2
  exit 1
}
./scripts/generate-boot-page-plan.sh "$build/leanos-extended-state-peer-pke.elf" \
  "$build/boot-page-plan-extended-state-peer-pke.final.h"
cmp "$build/boot-page-plan-extended-state-peer-pke.h" \
  "$build/boot-page-plan-extended-state-peer-pke.final.h" || {
  echo "error: peer-PKE boot page-table plan drifted after final link" >&2
  exit 1
}
for mechanism in syscall sysenter; do
  ./scripts/generate-boot-page-plan.sh "$build/leanos-fast-entry-${mechanism}.elf" \
    "$build/boot-page-plan-fast-entry-${mechanism}.final.h"
  cmp "$build/boot-page-plan-extended-state.h" \
    "$build/boot-page-plan-fast-entry-${mechanism}.final.h" || {
    echo "error: fast-entry $mechanism page-table plan drifted after final link" >&2
    exit 1
  }
done
./scripts/generate-boot-page-plan.sh "$build/leanos-extended-state-mmx.elf" \
  "$build/boot-page-plan-extended-state-mmx.final.h"
cmp "$build/boot-page-plan-extended-state.h" \
  "$build/boot-page-plan-extended-state-mmx.final.h" || {
  echo "error: MMX extended-state page-table plan drifted after final link" >&2
  exit 1
}
./scripts/generate-boot-page-plan.sh "$build/leanos-extended-state-sse.elf" \
  "$build/boot-page-plan-extended-state-sse.final.h"
cmp "$build/boot-page-plan-extended-state.h" \
  "$build/boot-page-plan-extended-state-sse.final.h" || {
  echo "error: SSE extended-state page-table plan drifted after final link" >&2
  exit 1
}
./scripts/generate-boot-page-plan.sh "$build/leanos-extended-state-sse2.elf" \
  "$build/boot-page-plan-extended-state-sse2.final.h"
cmp "$build/boot-page-plan-extended-state.h" \
  "$build/boot-page-plan-extended-state-sse2.final.h" || {
  echo "error: SSE2 extended-state page-table plan drifted after final link" >&2
  exit 1
}
./scripts/generate-boot-page-plan.sh "$build/leanos-extended-state-avx.elf" \
  "$build/boot-page-plan-extended-state-avx.final.h"
cmp "$build/boot-page-plan-extended-state.h" \
  "$build/boot-page-plan-extended-state-avx.final.h" || {
  echo "error: AVX extended-state page-table plan drifted after final link" >&2
  exit 1
}
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map build/boot/leanos-double-fault.map \
  -o build/boot/leanos-double-fault.elf build/boot/boot.o \
  build/boot/kernel-double-fault.o build/boot/KernelTransition.o \
  build/boot/Syscall.o build/boot/IPCSyscall.o build/boot/Preemption.o \
  build/boot/BootAllocation.o build/boot/Interrupt.o build/boot/InterruptEntry.o \
  build/boot/BlockingIPC.o build/boot/CapabilityReuse.o build/boot/ExtendedState.o build/boot/PrivilegeEntryControl.o build/boot/FaultDispatch.o
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-entry-stack-overflow.map" \
  -o "$build/leanos-entry-stack-overflow.elf" \
  "$build/boot-entry-stack-overflow.o" "$build/kernel-entry-stack-overflow.o" \
  "$build/KernelTransition.o" "$build/Syscall.o" "$build/IPCSyscall.o" \
  "$build/Preemption.o" "$build/BootAllocation.o" "$build/Interrupt.o" \
  "$build/InterruptEntry.o" "$build/BlockingIPC.o" "$build/CapabilityReuse.o" \
  "$build/ExtendedState.o" "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map build/boot/leanos-double-fault-guard-mapped.map \
  -o build/boot/leanos-double-fault-guard-mapped.elf \
  build/boot/boot-df-guard-mapped.o \
  build/boot/kernel-double-fault-guard-mapped.o \
  build/boot/KernelTransition.o build/boot/Syscall.o build/boot/IPCSyscall.o \
  build/boot/Preemption.o build/boot/BootAllocation.o build/boot/Interrupt.o build/boot/InterruptEntry.o \
  build/boot/BlockingIPC.o build/boot/CapabilityReuse.o build/boot/ExtendedState.o build/boot/PrivilegeEntryControl.o build/boot/FaultDispatch.o

./scripts/generate-boot-page-plan.sh "$build/leanos-double-fault.elf" \
  "$build/boot-page-plan-double-fault.final.h"
cmp "$build/boot-page-plan-double-fault.h" \
  "$build/boot-page-plan-double-fault.final.h" || {
  echo "error: double-fault boot page-table plan drifted after final link" >&2
  exit 1
}
./scripts/generate-boot-page-plan.sh "$build/leanos-entry-stack-overflow.elf" \
  "$build/boot-page-plan-entry-overflow.final.h"
cmp "$build/boot-page-plan-entry-overflow.h" \
  "$build/boot-page-plan-entry-overflow.final.h" || {
  echo "error: entry-stack overflow page-table plan drifted after final link" >&2
  exit 1
}
./scripts/generate-boot-page-plan.sh "$build/leanos-double-fault-guard-mapped.elf" \
  "$build/boot-page-plan-guard.final.h"
cmp "$build/boot-page-plan-guard.h" "$build/boot-page-plan-guard.final.h" || {
  echo "error: guard-mapped boot page-table plan drifted after final link" >&2
  exit 1
}
./scripts/generate-boot-page-plan.sh "$build/leanos-entry-adversarial.elf" \
  "$build/boot-page-plan-entry-adversarial.final.h"
cmp "$build/boot-page-plan-entry-adversarial.h" \
  "$build/boot-page-plan-entry-adversarial.final.h" || {
  echo "error: entry-adversarial page-table plan drifted after final link" >&2
  exit 1
}
for probe in "${direct_port_probes[@]}"; do
  ./scripts/generate-boot-page-plan.sh "$build/leanos-direct-port-${probe}.elf" \
    "$build/boot-page-plan-direct-port-${probe}.final.h"
  cmp "$build/boot-page-plan-direct-port.h" \
    "$build/boot-page-plan-direct-port-${probe}.final.h" || {
    echo "error: direct-port $probe boot page-table plan drifted after final link" >&2
    exit 1
  }
done
for probe in "${integer_fault_probes[@]}"; do
  ./scripts/generate-boot-page-plan.sh "$build/leanos-${probe}.elf" \
    "$build/boot-page-plan-${probe}.final.h"
  cmp "$build/boot-page-plan-integer-fault.h" \
    "$build/boot-page-plan-${probe}.final.h" || {
    echo "error: integer-fault $probe boot page-table plan drifted after final link" >&2
    exit 1
  }
done

undefined="$(nm -u "$build/leanos.elf")"
if [[ -n "$undefined" ]]; then
  echo "error: boot image has unexpected undefined symbols:" >&2
  echo "$undefined" >&2
  exit 1
fi
symbols="$(nm "$build/leanos.elf")"
if ! grep -q ' T leanos_boot_transition$' <<<"$symbols"; then
  echo "error: generated image does not retain leanos_boot_transition" >&2
  exit 1
fi
if ! grep -q ' T leanos_syscall_demo$' <<<"$symbols"; then
  echo "error: generated image does not retain leanos_syscall_demo" >&2
  exit 1
fi
if ! grep -q ' T leanos_ipc_demo$' <<<"$symbols"; then
  echo "error: generated image does not retain leanos_ipc_demo" >&2
  exit 1
fi
if ! grep -q ' T leanos_preemption_demo$' <<<"$symbols"; then
  echo "error: generated image does not retain leanos_preemption_demo" >&2
  exit 1
fi
if grep -q ' T leanos_boot_allocation_check$' <<<"$symbols"; then
  echo "error: generated image retained legacy scalar allocation authority" >&2
  exit 1
fi
for symbol in leanos_boot_handoff_stream_init leanos_boot_handoff_stream_step \
  leanos_boot_decode_init_v5 leanos_boot_decode_step_v5 \
  leanos_boot_consume_exact_projection leanos_boot_projection_entry \
  leanos_boot_projection_manifest leanos_boot_projection_free \
  leanos_boot_projection_finish leanos_boot_manifest_candidate \
  leanos_boot_authority_result \
  leanos_boot_machine_acpi_copy_stream_step_query \
  leanos_boot_machine_acpi_copy_sequence_step_query \
  leanos_boot_machine_madt_envelope_byte_step_query \
  leanos_boot_machine_madt_entry_stream_byte_step_query \
  leanos_boot_machine_topology_admission_result_query; do
  if ! grep -q " T ${symbol}$" <<<"$symbols"; then
    echo "error: generated image does not retain $symbol" >&2
    exit 1
  fi
done
for symbol in leanos_boot_manifest_start; do
  if grep -q " T ${symbol}$" <<<"$symbols"; then
    echo "error: generated image retained superseded production authority $symbol" >&2
    exit 1
  fi
done
if grep -q ' T leanos_boot_select_frame$' <<<"$symbols"; then
  echo "error: generated image retained superseded scalar selector" >&2
  exit 1
fi
grep -Fq 'projection=scalar-checked result=PASS' boot/kernel.c || {
  echo "error: production transcript omits scalar projection evidence" >&2
  exit 1
}
if ! grep -q ' T leanos_user_return_demo$' <<<"$symbols"; then
  echo "error: generated image does not retain leanos_user_return_demo" >&2
  exit 1
fi
if ! grep -q ' T leanos_blocking_ipc_demo$' <<<"$symbols"; then
  echo "error: generated image does not retain leanos_blocking_ipc_demo" >&2
  exit 1
fi
if ! grep -q ' T leanos_capability_reuse_demo$' <<<"$symbols"; then
  echo "error: generated image does not retain leanos_capability_reuse_demo" >&2
  exit 1
fi
if ! grep -q ' T leanos_extended_state_denial_demo$' <<<"$symbols"; then
  echo "error: generated image does not retain leanos_extended_state_denial_demo" >&2
  exit 1
fi
if ! grep -q ' T leanos_privilege_entry_control_demo$' <<<"$symbols"; then
  echo "error: generated image does not retain leanos_privilege_entry_control_demo" >&2
  exit 1
fi
if ! grep -q ' T leanos_direct_port_io_demo$' <<<"$symbols"; then
  echo "error: generated image does not retain leanos_direct_port_io_demo" >&2
  exit 1
fi
if ! grep -q ' T leanos_stale_translation_demo$' <<<"$symbols"; then
  echo "error: generated image does not retain leanos_stale_translation_demo" >&2
  exit 1
fi
if ! grep -q ' T leanos_page_fault_demo$' <<<"$symbols"; then
  echo "error: generated image does not retain leanos_page_fault_demo" >&2
  exit 1
fi
if ! grep -q ' T leanos_composite_dispatch$' <<<"$symbols"; then
  echo "error: generated image does not retain leanos_composite_dispatch" >&2
  exit 1
fi
if ! grep -q ' T leanos_validate_q35_dma_snapshot$' <<<"$symbols"; then
  echo "error: generated image does not retain leanos_validate_q35_dma_snapshot" >&2
  exit 1
fi
if ! grep -q ' T leanos_validate_vtd_activation$' <<<"$symbols"; then
  echo "error: generated image does not retain leanos_validate_vtd_activation" >&2
  exit 1
fi
if ! grub-file --is-x86-multiboot2 "$build/leanos.elf"; then
  echo "error: kernel ELF has no valid Multiboot2 header" >&2
  exit 1
fi
nm -n "$build/leanos.elf" >"$build/entry-stack-symbols.txt"
objdump -d --no-show-raw-insn "$build/leanos.elf" \
  >"$build/entry-stack-disassembly.txt"
LEANOS_ENTRY_STACK_ELF_EDGES_OUTPUT="$build/entry-stack-final-elf-edges.tsv" \
  ./scripts/check-entry-stack-budget.sh "$build/leanos.elf" \
  | tee "$build/entry-stack-final-elf.txt"
LEANOS_ENTRY_STACK_MANIFEST=scripts/entry-stack-extended-callgraph.tsv \
  LEANOS_ENTRY_STACK_OPTIMIZER_OPTIONAL=scripts/entry-stack-extended-optimizer-optional.tsv \
  LEANOS_ENTRY_STACK_ELF_EDGES_OUTPUT="$build/entry-stack-extended-final-elf-edges.tsv" \
  ./scripts/check-entry-stack-budget.sh "$build/leanos-extended-state.elf" \
  | tee "$build/entry-stack-extended-final-elf.txt"
LEANOS_ENTRY_STACK_MANIFEST=scripts/entry-stack-extended-callgraph.tsv \
  LEANOS_ENTRY_STACK_OPTIMIZER_OPTIONAL=scripts/entry-stack-extended-optimizer-optional.tsv \
  LEANOS_ENTRY_STACK_ELF_EDGES_OUTPUT="$build/entry-stack-extended-state-peer-pke-final-elf-edges.tsv" \
  ./scripts/check-entry-stack-budget.sh "$build/leanos-extended-state-peer-pke.elf" \
  | tee "$build/entry-stack-extended-state-peer-pke-final-elf.txt"
./scripts/check-image-policy.sh "$build/leanos.elf"
./scripts/check-image-policy.sh "$build/leanos-malformed-handoff.elf"
./scripts/check-image-policy.sh "$build/leanos-projection-authority-mutation.elf"
./scripts/check-image-policy.sh "$build/leanos-raw-selection-authority-mutation.elf"
./scripts/check-image-policy.sh "$build/leanos-preemption.elf"
./scripts/check-image-policy.sh "$build/leanos-frame-budget.elf"
./scripts/check-frame-budget-machine.sh "$build/leanos-frame-budget.elf"
./scripts/check-image-policy.sh "$build/leanos-fault-containment.elf"
./scripts/check-image-policy.sh "$build/leanos-fault-readonly-write.elf"
./scripts/check-image-policy.sh "$build/leanos-fault-nx-execute.elf"
for probe in "${fault_fatal_probes[@]}"; do
  LEANOS_PAGE_FAULT_FATAL_PROBE="$probe" \
    ./scripts/check-image-policy.sh "$build/leanos-fault-${probe}.elf"
done
./scripts/check-image-policy.sh "$build/leanos-fault-stale-translation.elf"
./scripts/check-image-policy.sh "$build/leanos-extended-state.elf"
./scripts/check-image-policy.sh "$build/leanos-extended-state-mmx.elf"
./scripts/check-image-policy.sh "$build/leanos-extended-state-sse.elf"
./scripts/check-image-policy.sh "$build/leanos-extended-state-sse2.elf"
./scripts/check-image-policy.sh "$build/leanos-extended-state-avx.elf"
for mechanism in syscall sysenter; do
  LEANOS_FAST_ENTRY_PROBE="$mechanism" \
    ./scripts/check-image-policy.sh "$build/leanos-fast-entry-${mechanism}.elf"
  LEANOS_FAST_ENTRY_PROBE="$mechanism" \
    ./scripts/check-entry-policy.sh "$build/leanos-fast-entry-${mechanism}.elf" \
    | tee "$build/fast-entry-${mechanism}-policy-report.txt"
done
./scripts/check-image-policy.sh "$build/leanos-double-fault.elf"
./scripts/check-image-policy.sh "$build/leanos-entry-stack-overflow.elf"
./scripts/check-image-policy.sh "$build/leanos-entry-adversarial.elf"
for probe in "${direct_port_probes[@]}"; do
  ./scripts/check-image-policy.sh "$build/leanos-direct-port-${probe}.elf"
done
for probe in "${integer_fault_probes[@]}"; do
  ./scripts/check-image-policy.sh "$build/leanos-${probe}.elf"
done
./scripts/check-nmi-image-policy.sh "$build/leanos-nmi.elf"
cp "$build/leanos-nmi.elf" "$build/leanos-nmi-cpl3.elf"
cp "$build/leanos-nmi.map" "$build/leanos-nmi-cpl3.map"
objdump -d --no-show-raw-insn "$build/leanos-nmi.elf" \
  > "$build/nmi.disassembly.txt"
cp "$build/nmi.disassembly.txt" "$build/nmi-cpl3.disassembly.txt"
./scripts/check-image-policy.sh "$build/leanos-bootstrap32-ud.elf"
./scripts/check-image-policy.sh "$build/leanos-bootstrap64-nmi.elf"
./scripts/check-early-probe-policy.py "$build/leanos-bootstrap32-ud.elf" \
  bootstrap32-ud | tee "$build/bootstrap32-ud-early-probe-policy.txt"
./scripts/check-early-probe-policy.py "$build/leanos-bootstrap64-nmi.elf" \
  bootstrap64-nmi | tee "$build/bootstrap64-nmi-early-probe-policy.txt"
objdump -d --no-show-raw-insn "$build/leanos-bootstrap32-ud.elf" \
  > "$build/bootstrap32-ud.disassembly.txt"
objdump -d --no-show-raw-insn "$build/leanos-bootstrap64-nmi.elf" \
  > "$build/bootstrap64-nmi.disassembly.txt"
objdump -d --no-show-raw-insn "$build/leanos-fault-containment.elf" \
  > "$build/fault-containment.disassembly.txt"
objdump -d --no-show-raw-insn "$build/leanos-fault-readonly-write.elf" \
  > "$build/fault-readonly-write.disassembly.txt"
objdump -d --no-show-raw-insn "$build/leanos-fault-nx-execute.elf" \
  > "$build/fault-nx-execute.disassembly.txt"
for probe in "${fault_image_probes[@]}"; do
  objdump -d --no-show-raw-insn "$build/leanos-fault-${probe}.elf" \
    > "$build/fault-${probe}.disassembly.txt"
done
objdump -d --no-show-raw-insn "$build/leanos-extended-state.elf" \
  > "$build/extended-state.disassembly.txt"
objdump -d --no-show-raw-insn "$build/leanos-extended-state-mmx.elf" \
  > "$build/extended-state-mmx.disassembly.txt"
objdump -d --no-show-raw-insn "$build/leanos-extended-state-sse.elf" \
  > "$build/extended-state-sse.disassembly.txt"
objdump -d --no-show-raw-insn "$build/leanos-extended-state-sse2.elf" \
  > "$build/extended-state-sse2.disassembly.txt"
objdump -d --no-show-raw-insn "$build/leanos-extended-state-avx.elf" \
  > "$build/extended-state-avx.disassembly.txt"
for probe in "${direct_port_probes[@]}"; do
  objdump -d --no-show-raw-insn "$build/leanos-direct-port-${probe}.elf" \
    > "$build/direct-port-${probe}.disassembly.txt"
done
for probe in "${integer_fault_probes[@]}"; do
  objdump -d --no-show-raw-insn "$build/leanos-${probe}.elf" \
    > "$build/${probe}.disassembly.txt"
done
./scripts/check-extended-state-policy.sh "$build/leanos-extended-state.elf" x87 \
  | tee "$build/extended-state-policy-report.txt"
./scripts/check-extended-state-policy.sh "$build/leanos-extended-state-mmx.elf" mmx \
  | tee "$build/extended-state-mmx-policy-report.txt"
./scripts/check-extended-state-policy.sh "$build/leanos-extended-state-sse.elf" sse \
  | tee "$build/extended-state-sse-policy-report.txt"
./scripts/check-extended-state-policy.sh "$build/leanos-extended-state-sse2.elf" sse2 \
  | tee "$build/extended-state-sse2-policy-report.txt"
./scripts/check-extended-state-policy.sh "$build/leanos-extended-state-avx.elf" avx \
  | tee "$build/extended-state-avx-policy-report.txt"
./scripts/test-extended-state-policy.sh "$build/leanos-extended-state.elf" \
  "$build/leanos-extended-state-mmx.elf" \
  "$build/leanos-extended-state-sse.elf" \
  "$build/leanos-extended-state-sse2.elf" \
  "$build/leanos-extended-state-avx.elf"
./scripts/check-entry-policy.sh "$build/leanos.elf" | tee "$build/entry-policy-report.txt"
LEANOS_PAGE_FAULT_PROBE=supervisor-read \
  ./scripts/check-entry-policy.sh "$build/leanos-fault-containment.elf" \
  | tee "$build/fault-containment-policy-report.txt"
LEANOS_PAGE_FAULT_PROBE=readonly-write \
  ./scripts/check-entry-policy.sh "$build/leanos-fault-readonly-write.elf" \
  | tee "$build/fault-readonly-write-policy-report.txt"
LEANOS_PAGE_FAULT_PROBE=nx-execute \
  ./scripts/check-entry-policy.sh "$build/leanos-fault-nx-execute.elf" \
  | tee "$build/fault-nx-execute-policy-report.txt"
for probe in "${fault_fatal_probes[@]}"; do
  LEANOS_PAGE_FAULT_FATAL_PROBE="$probe" \
    ./scripts/check-entry-policy.sh "$build/leanos-fault-${probe}.elf" \
    | tee "$build/fault-${probe}-policy-report.txt"
done
./scripts/check-entry-policy.sh "$build/leanos-fault-stale-translation.elf" \
  | tee "$build/fault-stale-translation-policy-report.txt"
./scripts/test-entry-policy.sh "$build/leanos.elf" \
  "$build/leanos-fault-nx-execute.elf" | tee "$build/entry-policy-fixtures.log"
./scripts/test-runtime-invalidation-policy.sh "$build/leanos.elf" \
  | tee "$build/runtime-invalidation-policy-fixtures.log"
./scripts/test-vtd-mmio-policy.sh "$build/leanos.elf" \
  | tee "$build/vtd-mmio-policy-fixtures.log"
./scripts/test-frame-budget-invalidation-policy.sh \
  "$build/leanos-frame-budget.elf" \
  | tee "$build/frame-budget-invalidation-policy-fixtures.log"
direct_port_report="$build/direct-port-sites-report.txt"
: > "$direct_port_report"
direct_port_images=0
while IFS=$'\t' read -r _id _runner _class _timeout _image elf_name \
    _log _scenario _mode _reason; do
  [[ "$elf_name" == *.elf ]] || continue
  manifest="scripts/direct-port-sites.tsv"
  direct_port_args=()
  case "$elf_name" in
    leanos-entry-adversarial.elf)
      manifest="scripts/direct-port-sites-entry-adversarial.tsv"
      ;;
    leanos-entry-stack-overflow.elf)
      manifest="scripts/direct-port-sites-entry-stack-overflow.tsv"
      ;;
    leanos-nmi.elf|leanos-nmi-cpl3.elf)
      manifest="scripts/direct-port-sites-nmi.tsv"
      ;;
    leanos-bootstrap32-ud.elf)
      manifest="scripts/direct-port-sites-bootstrap32-ud.tsv"
      ;;
    leanos-bootstrap64-nmi.elf)
      manifest="scripts/direct-port-sites-bootstrap64-nmi.tsv"
      ;;
    leanos-direct-port-serial.elf)
      manifest="scripts/direct-port-sites-direct-port-serial.tsv"
      ;;
    leanos-direct-port-debug.elf)
      manifest="scripts/direct-port-sites-direct-port-debug.tsv"
      ;;
    leanos-direct-port-in.elf)
      manifest="scripts/direct-port-sites-direct-port-in.tsv"
      ;;
    leanos-direct-port-pic.elf)
      manifest="scripts/direct-port-sites-direct-port-pic.tsv"
      ;;
  esac
  ./scripts/check-direct-port-sites.py "$build/$elf_name" "$manifest" \
    "${direct_port_args[@]}" \
    | sed "s/^/elf=$elf_name /" | tee -a "$direct_port_report"
  ((direct_port_images += 1))
done < "$matrix"
expected_evidence_images="$(
  awk -F $'\t' '$1 == "# mandatory-count" { print $2 }' \
    scripts/emulator-evidence-matrix.tsv
)"
[[ "$expected_evidence_images" =~ ^[0-9]+$ &&
   "$direct_port_images" -eq "$expected_evidence_images" ]] || {
  echo "error: direct-port evidence ELF count drifted: $direct_port_images" >&2
  exit 1
}
./scripts/test-direct-port-sites.sh "$build/leanos.elf" \
  | tee "$build/direct-port-sites-fixtures.log"
./scripts/test-direct-port-sites.sh "$build/leanos-entry-adversarial.elf" \
  scripts/direct-port-sites-entry-adversarial.tsv \
  | tee -a "$build/direct-port-sites-fixtures.log"

for fixture in restore branch indirect initial-indirect; do
  ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
    -T boot/linker.ld -Map "$build/leanos-return-${fixture}-fixture.map" \
    -o "$build/leanos-return-${fixture}-fixture.elf" \
    "$build/boot-return-${fixture}-fixture.o" "$build/kernel.o" \
    "$build/KernelTransition.o" "$build/Syscall.o" "$build/IPCSyscall.o" \
    "$build/Preemption.o" "$build/BootAllocation.o" "$build/Interrupt.o" "$build/InterruptEntry.o" \
    "$build/BlockingIPC.o" "$build/CapabilityReuse.o" "$build/ExtendedState.o" "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
  if ./scripts/check-image-policy.sh "$build/leanos-return-${fixture}-fixture.elf" \
      >"$build/return-${fixture}-fixture.log" 2>&1; then
    echo "error: user-return ${fixture} negative fixture unexpectedly passed" >&2
    exit 1
  fi
done
grep -Fq 'error: unexpected exact user-return restore sequence' \
  "$build/return-restore-fixture.log" || {
  echo "error: restore negative fixture lacked expected diagnostic" >&2; exit 1;
}
grep -Fq 'enters post-validation restore interval' \
  "$build/return-branch-fixture.log" || {
  echo "error: branch negative fixture lacked expected diagnostic" >&2; exit 1;
}
grep -Fq 'indirect control-flow instruction' \
  "$build/return-indirect-fixture.log" || {
  echo "error: indirect negative fixture lacked expected diagnostic" >&2; exit 1;
}
grep -Fq 'indirect control-flow instruction' \
  "$build/return-initial-indirect-fixture.log" || {
  echo "error: initial indirect fixture lacked expected diagnostic" >&2; exit 1;
}

cp "$build/leanos.elf" "$iso_root/boot/leanos.elf"
cp boot/grub.cfg "$iso_root/boot/grub/grub.cfg"
cp "$build/leanos-malformed-handoff.elf" \
  "$malformed_handoff_iso_root/boot/leanos.elf"
cp boot/grub.cfg "$malformed_handoff_iso_root/boot/grub/grub.cfg"
cp "$build/leanos-projection-authority-mutation.elf" \
  "$projection_authority_iso_root/boot/leanos.elf"
cp boot/grub.cfg "$projection_authority_iso_root/boot/grub/grub.cfg"
cp "$build/leanos-raw-selection-authority-mutation.elf" \
  "$raw_selection_authority_iso_root/boot/leanos.elf"
cp boot/grub.cfg "$raw_selection_authority_iso_root/boot/grub/grub.cfg"
cp "$build/leanos-preemption.elf" "$preemption_iso_root/boot/leanos.elf"
cp boot/grub.cfg "$preemption_iso_root/boot/grub/grub.cfg"
cp "$build/leanos-frame-budget.elf" "$frame_budget_iso_root/boot/leanos.elf"
cp boot/grub.cfg "$frame_budget_iso_root/boot/grub/grub.cfg"
cp "$build/leanos-fault-containment.elf" \
  "$fault_containment_iso_root/boot/leanos.elf"
cp boot/grub.cfg "$fault_containment_iso_root/boot/grub/grub.cfg"
cp "$build/leanos-fault-readonly-write.elf" \
  "$fault_readonly_write_iso_root/boot/leanos.elf"
cp boot/grub.cfg "$fault_readonly_write_iso_root/boot/grub/grub.cfg"
cp "$build/leanos-fault-nx-execute.elf" \
  "$fault_nx_execute_iso_root/boot/leanos.elf"
cp boot/grub.cfg "$fault_nx_execute_iso_root/boot/grub/grub.cfg"
for probe in "${fault_image_probes[@]}"; do
  cp "$build/leanos-fault-${probe}.elf" \
    "$build/iso-fault-${probe}/boot/leanos.elf"
  cp boot/grub.cfg "$build/iso-fault-${probe}/boot/grub/grub.cfg"
done
cp "$build/leanos-extended-state.elf" "$extended_state_iso_root/boot/leanos.elf"
cp boot/grub.cfg "$extended_state_iso_root/boot/grub/grub.cfg"
cp "$build/leanos-extended-state-mmx.elf" \
  "$extended_state_mmx_iso_root/boot/leanos.elf"
cp boot/grub.cfg "$extended_state_mmx_iso_root/boot/grub/grub.cfg"
cp "$build/leanos-extended-state-sse.elf" \
  "$extended_state_sse_iso_root/boot/leanos.elf"
cp boot/grub.cfg "$extended_state_sse_iso_root/boot/grub/grub.cfg"
cp "$build/leanos-extended-state-sse2.elf" \
  "$extended_state_sse2_iso_root/boot/leanos.elf"
cp boot/grub.cfg "$extended_state_sse2_iso_root/boot/grub/grub.cfg"
cp "$build/leanos-extended-state-avx.elf" \
  "$extended_state_avx_iso_root/boot/leanos.elf"
cp boot/grub.cfg "$extended_state_avx_iso_root/boot/grub/grub.cfg"
cp "$build/leanos-extended-state-peer-pke.elf" \
  "$extended_state_peer_pke_iso_root/boot/leanos.elf"
cp boot/grub.cfg "$extended_state_peer_pke_iso_root/boot/grub/grub.cfg"
for mechanism in syscall sysenter; do
  fixture_root="$build/iso-fast-entry-${mechanism}"
  cp "$build/leanos-fast-entry-${mechanism}.elf" "$fixture_root/boot/leanos.elf"
  cp boot/grub.cfg "$fixture_root/boot/grub/grub.cfg"
done
cp "$build/leanos-double-fault.elf" "$df_iso_root/boot/leanos.elf"
cp boot/grub-double-fault.cfg "$df_iso_root/boot/grub/grub.cfg"
cp "$build/leanos-double-fault-guard-mapped.elf" \
  "$df_negative_iso_root/boot/leanos.elf"
cp boot/grub-double-fault.cfg "$df_negative_iso_root/boot/grub/grub.cfg"
cp "$build/leanos-entry-stack-overflow.elf" "$entry_overflow_iso_root/boot/leanos.elf"
cp boot/grub-double-fault.cfg "$entry_overflow_iso_root/boot/grub/grub.cfg"
cp "$build/leanos-entry-adversarial.elf" "$entry_adversarial_iso_root/boot/leanos.elf"
cp boot/grub.cfg "$entry_adversarial_iso_root/boot/grub/grub.cfg"
cp "$build/leanos-nmi.elf" "$nmi_iso_root/boot/leanos.elf"
cp boot/grub.cfg "$nmi_iso_root/boot/grub/grub.cfg"
cp "$build/leanos-nmi-cpl3.elf" "$nmi_cpl3_iso_root/boot/leanos.elf"
cp boot/grub-nmi-cpl3.cfg "$nmi_cpl3_iso_root/boot/grub/grub.cfg"
cp "$build/leanos-bootstrap32-ud.elf" "$bootstrap32_ud_iso_root/boot/leanos.elf"
cp boot/grub.cfg "$bootstrap32_ud_iso_root/boot/grub/grub.cfg"
cp "$build/leanos-bootstrap64-nmi.elf" "$bootstrap64_nmi_iso_root/boot/leanos.elf"
cp boot/grub.cfg "$bootstrap64_nmi_iso_root/boot/grub/grub.cfg"
for probe in "${direct_port_probes[@]}"; do
  cp "$build/leanos-direct-port-${probe}.elf" \
    "$build/iso-direct-port-${probe}/boot/leanos.elf"
  cp boot/grub.cfg "$build/iso-direct-port-${probe}/boot/grub/grub.cfg"
done
for probe in "${integer_fault_probes[@]}"; do
  cp "$build/leanos-${probe}.elf" "$build/iso-${probe}/boot/leanos.elf"
  cp boot/grub.cfg "$build/iso-${probe}/boot/grub/grub.cfg"
done
printf '%s\n' "$source_revision" | tee "$build/SOURCE_REVISION" \
  > "$iso_root/boot/SOURCE_REVISION"
cp "$build/SOURCE_REVISION" "$df_iso_root/boot/SOURCE_REVISION"
cp "$build/SOURCE_REVISION" "$preemption_iso_root/boot/SOURCE_REVISION"
cp "$build/SOURCE_REVISION" "$frame_budget_iso_root/boot/SOURCE_REVISION"
cp "$build/SOURCE_REVISION" "$fault_containment_iso_root/boot/SOURCE_REVISION"
cp "$build/SOURCE_REVISION" \
  "$fault_readonly_write_iso_root/boot/SOURCE_REVISION"
cp "$build/SOURCE_REVISION" "$fault_nx_execute_iso_root/boot/SOURCE_REVISION"
for probe in "${fault_image_probes[@]}"; do
  cp "$build/SOURCE_REVISION" \
    "$build/iso-fault-${probe}/boot/SOURCE_REVISION"
done
cp "$build/SOURCE_REVISION" "$extended_state_iso_root/boot/SOURCE_REVISION"
cp "$build/SOURCE_REVISION" "$extended_state_mmx_iso_root/boot/SOURCE_REVISION"
cp "$build/SOURCE_REVISION" "$extended_state_sse_iso_root/boot/SOURCE_REVISION"
cp "$build/SOURCE_REVISION" "$extended_state_sse2_iso_root/boot/SOURCE_REVISION"
cp "$build/SOURCE_REVISION" "$extended_state_avx_iso_root/boot/SOURCE_REVISION"
cp "$build/SOURCE_REVISION" \
  "$extended_state_peer_pke_iso_root/boot/SOURCE_REVISION"
cp "$build/SOURCE_REVISION" "$fast_entry_syscall_iso_root/boot/SOURCE_REVISION"
cp "$build/SOURCE_REVISION" "$fast_entry_sysenter_iso_root/boot/SOURCE_REVISION"
cp "$build/SOURCE_REVISION" "$df_negative_iso_root/boot/SOURCE_REVISION"
cp "$build/SOURCE_REVISION" "$entry_overflow_iso_root/boot/SOURCE_REVISION"
cp "$build/SOURCE_REVISION" "$entry_adversarial_iso_root/boot/SOURCE_REVISION"
cp "$build/SOURCE_REVISION" "$nmi_iso_root/boot/SOURCE_REVISION"
cp "$build/SOURCE_REVISION" "$nmi_cpl3_iso_root/boot/SOURCE_REVISION"
cp "$build/SOURCE_REVISION" "$bootstrap32_ud_iso_root/boot/SOURCE_REVISION"
cp "$build/SOURCE_REVISION" "$bootstrap64_nmi_iso_root/boot/SOURCE_REVISION"
cp "$build/SOURCE_REVISION" "$malformed_handoff_iso_root/boot/SOURCE_REVISION"
cp "$build/SOURCE_REVISION" \
  "$projection_authority_iso_root/boot/SOURCE_REVISION"
cp "$build/SOURCE_REVISION" \
  "$raw_selection_authority_iso_root/boot/SOURCE_REVISION"
for probe in "${direct_port_probes[@]}"; do
  cp "$build/SOURCE_REVISION" \
    "$build/iso-direct-port-${probe}/boot/SOURCE_REVISION"
done
for probe in "${integer_fault_probes[@]}"; do
  cp "$build/SOURCE_REVISION" "$build/iso-${probe}/boot/SOURCE_REVISION"
done
for spec in "${return_corruptions[@]}"; do
  IFS=: read -r fixture _mode _reason <<<"$spec"
  fixture_root="$build/iso-return-${fixture}"
  mkdir -p "$fixture_root/boot/grub"
  cp "$build/leanos-return-${fixture}.elf" "$fixture_root/boot/leanos.elf"
  cp boot/grub.cfg "$fixture_root/boot/grub/grub.cfg"
  cp "$build/SOURCE_REVISION" "$fixture_root/boot/SOURCE_REVISION"
done
# BIOS-only output avoids GRUB's nondeterministic FAT/EFI image. A fixed ISO
# UUID and file dates make repeated builds independent of wall-clock time.
grub-mkrescue -d /usr/lib/grub/i386-pc \
  -o "$build/leanos-${version}-x86_64.iso" "$iso_root" -- \
  -volume_date uuid 2000010100000000 \
  -volume_date all_file_dates 2000010100000000 >/dev/null
grub-mkrescue -d /usr/lib/grub/i386-pc \
  -o "$build/leanos-${version}-x86_64-malformed-handoff.iso" \
  "$malformed_handoff_iso_root" -- -volume_date uuid 2000010100000000 \
  -volume_date all_file_dates 2000010100000000 >/dev/null
grub-mkrescue -d /usr/lib/grub/i386-pc \
  -o "$build/leanos-${version}-x86_64-projection-authority-mutation.iso" \
  "$projection_authority_iso_root" -- -volume_date uuid 2000010100000000 \
  -volume_date all_file_dates 2000010100000000 >/dev/null
grub-mkrescue -d /usr/lib/grub/i386-pc \
  -o "$build/leanos-${version}-x86_64-raw-selection-authority-mutation.iso" \
  "$raw_selection_authority_iso_root" -- -volume_date uuid 2000010100000000 \
  -volume_date all_file_dates 2000010100000000 >/dev/null
grub-mkrescue -d /usr/lib/grub/i386-pc \
  -o "$build/leanos-${version}-x86_64-preemption.iso" "$preemption_iso_root" -- \
  -volume_date uuid 2000010100000000 \
  -volume_date all_file_dates 2000010100000000 >/dev/null
grub-mkrescue -d /usr/lib/grub/i386-pc \
  -o "$build/leanos-${version}-x86_64-frame-budget.iso" "$frame_budget_iso_root" -- \
  -volume_date uuid 2000010100000000 \
  -volume_date all_file_dates 2000010100000000 >/dev/null
grub-mkrescue -d /usr/lib/grub/i386-pc \
  -o "$build/leanos-${version}-x86_64-fault-containment.iso" \
  "$fault_containment_iso_root" -- -volume_date uuid 2000010100000000 \
  -volume_date all_file_dates 2000010100000000 >/dev/null
grub-mkrescue -d /usr/lib/grub/i386-pc \
  -o "$build/leanos-${version}-x86_64-fault-readonly-write.iso" \
  "$fault_readonly_write_iso_root" -- -volume_date uuid 2000010100000000 \
  -volume_date all_file_dates 2000010100000000 >/dev/null
grub-mkrescue -d /usr/lib/grub/i386-pc \
  -o "$build/leanos-${version}-x86_64-fault-nx-execute.iso" \
  "$fault_nx_execute_iso_root" -- -volume_date uuid 2000010100000000 \
  -volume_date all_file_dates 2000010100000000 >/dev/null
for probe in "${fault_image_probes[@]}"; do
  grub-mkrescue -d /usr/lib/grub/i386-pc \
    -o "$build/leanos-${version}-x86_64-fault-${probe}.iso" \
    "$build/iso-fault-${probe}" -- -volume_date uuid 2000010100000000 \
    -volume_date all_file_dates 2000010100000000 >/dev/null
done
grub-mkrescue -d /usr/lib/grub/i386-pc \
  -o "$build/leanos-${version}-x86_64-extended-state.iso" \
  "$extended_state_iso_root" -- -volume_date uuid 2000010100000000 \
  -volume_date all_file_dates 2000010100000000 >/dev/null
grub-mkrescue -d /usr/lib/grub/i386-pc \
  -o "$build/leanos-${version}-x86_64-extended-state-mmx.iso" \
  "$extended_state_mmx_iso_root" -- -volume_date uuid 2000010100000000 \
  -volume_date all_file_dates 2000010100000000 >/dev/null
grub-mkrescue -d /usr/lib/grub/i386-pc \
  -o "$build/leanos-${version}-x86_64-extended-state-sse.iso" \
  "$extended_state_sse_iso_root" -- -volume_date uuid 2000010100000000 \
  -volume_date all_file_dates 2000010100000000 >/dev/null
grub-mkrescue -d /usr/lib/grub/i386-pc \
  -o "$build/leanos-${version}-x86_64-extended-state-sse2.iso" \
  "$extended_state_sse2_iso_root" -- -volume_date uuid 2000010100000000 \
  -volume_date all_file_dates 2000010100000000 >/dev/null
grub-mkrescue -d /usr/lib/grub/i386-pc \
  -o "$build/leanos-${version}-x86_64-extended-state-avx.iso" \
  "$extended_state_avx_iso_root" -- -volume_date uuid 2000010100000000 \
  -volume_date all_file_dates 2000010100000000 >/dev/null
grub-mkrescue -d /usr/lib/grub/i386-pc \
  -o "$build/leanos-${version}-x86_64-extended-state-peer-pke.iso" \
  "$extended_state_peer_pke_iso_root" -- -volume_date uuid 2000010100000000 \
  -volume_date all_file_dates 2000010100000000 >/dev/null
for mechanism in syscall sysenter; do
  grub-mkrescue -d /usr/lib/grub/i386-pc \
    -o "$build/leanos-${version}-x86_64-fast-entry-${mechanism}.iso" \
    "$build/iso-fast-entry-${mechanism}" -- -volume_date uuid 2000010100000000 \
    -volume_date all_file_dates 2000010100000000 >/dev/null
done
grub-mkrescue -d /usr/lib/grub/i386-pc \
  -o "$build/leanos-${version}-x86_64-double-fault.iso" "$df_iso_root" -- \
  -volume_date uuid 2000010100000000 \
  -volume_date all_file_dates 2000010100000000 >/dev/null
grub-mkrescue -d /usr/lib/grub/i386-pc \
  -o "$build/leanos-${version}-x86_64-double-fault-guard-mapped.iso" \
  "$df_negative_iso_root" -- -volume_date uuid 2000010100000000 \
  -volume_date all_file_dates 2000010100000000 >/dev/null
grub-mkrescue -d /usr/lib/grub/i386-pc \
  -o "$build/leanos-${version}-x86_64-entry-stack-overflow.iso" \
  "$entry_overflow_iso_root" -- -volume_date uuid 2000010100000000 \
  -volume_date all_file_dates 2000010100000000 >/dev/null
grub-mkrescue -d /usr/lib/grub/i386-pc \
  -o "$build/leanos-${version}-x86_64-entry-adversarial.iso" \
  "$entry_adversarial_iso_root" -- -volume_date uuid 2000010100000000 \
  -volume_date all_file_dates 2000010100000000 >/dev/null
grub-mkrescue -d /usr/lib/grub/i386-pc \
  -o "$build/leanos-${version}-x86_64-nmi.iso" "$nmi_iso_root" -- \
  -volume_date uuid 2000010100000000 \
  -volume_date all_file_dates 2000010100000000 >/dev/null
grub-mkrescue -d /usr/lib/grub/i386-pc \
  -o "$build/leanos-${version}-x86_64-nmi-cpl3.iso" "$nmi_cpl3_iso_root" -- \
  -volume_date uuid 2000010100000000 \
  -volume_date all_file_dates 2000010100000000 >/dev/null
grub-mkrescue -d /usr/lib/grub/i386-pc \
  -o "$build/leanos-${version}-x86_64-bootstrap32-ud.iso" \
  "$bootstrap32_ud_iso_root" -- -volume_date uuid 2000010100000000 \
  -volume_date all_file_dates 2000010100000000 >/dev/null
grub-mkrescue -d /usr/lib/grub/i386-pc \
  -o "$build/leanos-${version}-x86_64-bootstrap64-nmi.iso" \
  "$bootstrap64_nmi_iso_root" -- -volume_date uuid 2000010100000000 \
  -volume_date all_file_dates 2000010100000000 >/dev/null
for probe in "${direct_port_probes[@]}"; do
  grub-mkrescue -d /usr/lib/grub/i386-pc \
    -o "$build/leanos-${version}-x86_64-direct-port-${probe}.iso" \
    "$build/iso-direct-port-${probe}" -- -volume_date uuid 2000010100000000 \
    -volume_date all_file_dates 2000010100000000 >/dev/null
done
for probe in "${integer_fault_probes[@]}"; do
  grub-mkrescue -d /usr/lib/grub/i386-pc \
    -o "$build/leanos-${version}-x86_64-${probe}.iso" \
    "$build/iso-${probe}" -- -volume_date uuid 2000010100000000 \
    -volume_date all_file_dates 2000010100000000 >/dev/null
done
for spec in "${return_corruptions[@]}"; do
  IFS=: read -r fixture _mode _reason <<<"$spec"
  grub-mkrescue -d /usr/lib/grub/i386-pc \
    -o "$build/leanos-${version}-x86_64-return-${fixture}.iso" \
    "$build/iso-return-${fixture}" -- \
    -volume_date uuid 2000010100000000 \
    -volume_date all_file_dates 2000010100000000 >/dev/null
done
sha256sum "$build/leanos-${version}-x86_64.iso" \
  "$build/leanos-${version}-x86_64-malformed-handoff.iso" \
  "$build/leanos-malformed-handoff.elf" \
  "$build/leanos-malformed-handoff.map" \
  "$build/leanos-${version}-x86_64-projection-authority-mutation.iso" \
  "$build/leanos-projection-authority-mutation.elf" \
  "$build/leanos-projection-authority-mutation.map" \
  "$build/leanos-${version}-x86_64-raw-selection-authority-mutation.iso" \
  "$build/leanos-raw-selection-authority-mutation.elf" \
  "$build/leanos-raw-selection-authority-mutation.map" \
  "$build/leanos-${version}-x86_64-preemption.iso" \
  "$build/leanos-${version}-x86_64-frame-budget.iso" \
  "$build/leanos-${version}-x86_64-fault-containment.iso" \
  "$build/leanos-${version}-x86_64-fault-readonly-write.iso" \
  "$build/leanos-${version}-x86_64-fault-nx-execute.iso" \
  "$build/leanos-${version}-x86_64-fault-reserved-bit.iso" \
  "$build/leanos-${version}-x86_64-fault-walk-mismatch.iso" \
  "$build/leanos-${version}-x86_64-extended-state.iso" \
  "$build/leanos-${version}-x86_64-extended-state-mmx.iso" \
  "$build/leanos-${version}-x86_64-extended-state-sse.iso" \
  "$build/leanos-${version}-x86_64-extended-state-sse2.iso" \
  "$build/leanos-${version}-x86_64-extended-state-avx.iso" \
  "$build/leanos-${version}-x86_64-extended-state-peer-pke.iso" \
  "$build/leanos-${version}-x86_64-double-fault.iso" "$build/leanos.elf" \
  "$build/leanos-preemption.elf" "$build/leanos-preemption.map" \
  "$build/leanos-frame-budget.elf" "$build/leanos-frame-budget.map" \
  "$build/leanos-fault-containment.elf" \
  "$build/leanos-fault-containment.map" \
  "$build/leanos-fault-readonly-write.elf" \
  "$build/leanos-fault-readonly-write.map" \
  "$build/leanos-fault-nx-execute.elf" \
  "$build/leanos-fault-nx-execute.map" \
  "$build/leanos-fault-reserved-bit.elf" \
  "$build/leanos-fault-reserved-bit.map" \
  "$build/leanos-fault-walk-mismatch.elf" \
  "$build/leanos-fault-walk-mismatch.map" \
  "$build/leanos-extended-state.elf" "$build/leanos-extended-state.map" \
  "$build/leanos-extended-state-mmx.elf" \
  "$build/leanos-extended-state-mmx.map" \
  "$build/leanos-extended-state-sse.elf" \
  "$build/leanos-extended-state-sse.map" \
  "$build/leanos-extended-state-sse2.elf" \
  "$build/leanos-extended-state-sse2.map" \
  "$build/leanos-extended-state-avx.elf" \
  "$build/leanos-extended-state-avx.map" \
  "$build/leanos-extended-state-peer-pke.elf" \
  "$build/leanos-extended-state-peer-pke.map" \
  "$build/leanos-${version}-x86_64-fast-entry-syscall.iso" \
  "$build/leanos-fast-entry-syscall.elf" \
  "$build/leanos-fast-entry-syscall.map" \
  "$build/leanos-${version}-x86_64-fast-entry-sysenter.iso" \
  "$build/leanos-fast-entry-sysenter.elf" \
  "$build/leanos-fast-entry-sysenter.map" \
  "$build/leanos-double-fault.elf" \
  "$build/leanos-${version}-x86_64-double-fault-guard-mapped.iso" \
  "$build/leanos-double-fault-guard-mapped.elf" \
  "$build/leanos-${version}-x86_64-entry-stack-overflow.iso" \
  "$build/leanos-entry-stack-overflow.elf" \
  "$build/leanos-${version}-x86_64-entry-adversarial.iso" \
  "$build/leanos-entry-adversarial.elf" \
  "$build/leanos-${version}-x86_64-nmi.iso" \
  "$build/leanos-nmi.elf" "$build/leanos-nmi.map" \
  "$build/leanos-${version}-x86_64-nmi-cpl3.iso" \
  "$build/leanos-nmi-cpl3.elf" "$build/leanos-nmi-cpl3.map" \
  "$build/leanos-${version}-x86_64-bootstrap32-ud.iso" \
  "$build/leanos-bootstrap32-ud.elf" "$build/leanos-bootstrap32-ud.map" \
  "$build/leanos-${version}-x86_64-bootstrap64-nmi.iso" \
  "$build/leanos-bootstrap64-nmi.elf" "$build/leanos-bootstrap64-nmi.map" \
  > "$build/SHA256SUMS"
for probe in "${direct_port_probes[@]}"; do
  sha256sum "$build/leanos-${version}-x86_64-direct-port-${probe}.iso" \
    "$build/leanos-direct-port-${probe}.elf" \
    "$build/leanos-direct-port-${probe}.map" >> "$build/SHA256SUMS"
done
for probe in "${integer_fault_probes[@]}"; do
  sha256sum "$build/leanos-${version}-x86_64-${probe}.iso" \
    "$build/leanos-${probe}.elf" \
    "$build/leanos-${probe}.map" >> "$build/SHA256SUMS"
done
for spec in "${return_corruptions[@]}"; do
  IFS=: read -r fixture _mode _reason <<<"$spec"
  sha256sum "$build/leanos-${version}-x86_64-return-${fixture}.iso" \
    "$build/leanos-return-${fixture}.elf" >> "$build/SHA256SUMS"
done
echo "built build/boot/leanos-${version}-x86_64.iso at $source_revision"
echo "symbols: build/boot/leanos.map; debug ELF: build/boot/leanos.elf"
