#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

build_profile_started_at="$SECONDS"
build_profile_phase_started_at="$SECONDS"
if [[ -n "${LEANOS_BUILD_TIMING_FILE:-}" ]]; then
  mkdir -p "$(dirname -- "$LEANOS_BUILD_TIMING_FILE")"
  printf 'phase\tphase_seconds\ttotal_seconds\n' > "$LEANOS_BUILD_TIMING_FILE"
fi
record_build_phase() {
  local phase="$1"
  local now="$SECONDS"
  local phase_seconds="$((now - build_profile_phase_started_at))"
  local total_seconds="$((now - build_profile_started_at))"
  printf 'build-phase\t%s\tphase_seconds=%s\ttotal_seconds=%s\n' \
    "$phase" "$phase_seconds" "$total_seconds"
  if [[ -n "${LEANOS_BUILD_TIMING_FILE:-}" ]]; then
    printf '%s\t%s\t%s\n' "$phase" "$phase_seconds" "$total_seconds" \
      >> "$LEANOS_BUILD_TIMING_FILE"
  fi
  build_profile_phase_started_at="$now"
}

require_tool() {
  if ! command -v "$1" >/dev/null 2>&1; then
    echo "error: missing required tool '$1'; $2" >&2
    exit 1
  fi
}

compute_graph_signature() {
  local object_graph="$1"
  local compiler="$2"
  local compiler_path
  local linker_path
  compiler_path="$(command -v -- "$compiler")"
  linker_path="$(command -v -- ld)"
  {
    sha256sum "$object_graph" "$compiler_path" "$linker_path"
    LC_ALL=C "$compiler" --version
    LC_ALL=C ld --version
  } | sha256sum | awk '{print $1}'
}

compute_lean_c_signature() {
  local root="$1"
  local input
  local lean_path
  lean_path="$(lake env sh -c 'command -v lean')"
  {
    while IFS= read -r -d '' input; do
      sha256sum "$input"
    done < <(find "$root/LeanOS" -type f -name '*.lean' -print0 | sort -z)
    for input in lakefile.toml lean-toolchain lake-manifest.json; do
      [[ -f "$root/$input" ]] && sha256sum "$root/$input"
    done
    sha256sum "$lean_path"
    LC_ALL=C lake env lean --version
  } | sha256sum | awk '{print $1}'
}

require_tool lake "install Elan from https://elan.lean-lang.org/"
cc="${LEANOS_CC:-gcc}"
require_tool "$cc" "install Ubuntu package gcc=4:13.2.0-7ubuntu1"
require_tool make "install Ubuntu package make=4.3-4.1build2"
require_tool sha256sum "install Ubuntu package coreutils=9.4-3ubuntu6.1"
require_tool ld "install Ubuntu package binutils=2.42-4ubuntu2.10"
require_tool nm "install Ubuntu package binutils=2.42-4ubuntu2.10"
require_tool grub-file "install Ubuntu package grub-common=2.12-1ubuntu7.3"
require_tool grub-mkrescue "install Ubuntu package grub-common=2.12-1ubuntu7.3"
require_tool grub-mkimage "install Ubuntu package grub-common=2.12-1ubuntu7.3"
require_tool grub-mkstandalone "install Ubuntu package grub-common=2.12-1ubuntu7.3"
require_tool mformat "install Ubuntu package mtools=4.0.43-1build1"
require_tool xorriso "install Ubuntu package xorriso=1:1.5.6-1.1ubuntu3"
if [[ ! -d /usr/lib/grub/i386-pc ]]; then
  echo "error: missing GRUB BIOS modules; install Ubuntu package grub-pc-bin=2.12-1ubuntu7.3" >&2
  exit 1
fi
grub_mkrescue_path="$(command -v grub-mkrescue)"
xorriso_path="$(command -v xorriso)"
mformat_path="$(command -v mformat)"
grub_mkimage_path="$(command -v grub-mkimage)"
grub_mkstandalone_path="$(command -v grub-mkstandalone)"
grub_module_root=/usr/lib/grub/i386-pc

compute_iso_packaging_signature() {
  local input
  {
    sha256sum \
      "$grub_mkrescue_path" \
      "$xorriso_path" \
      "$mformat_path" \
      "$grub_mkimage_path" \
      "$grub_mkstandalone_path"
    LC_ALL=C "$grub_mkrescue_path" --version
    while IFS= read -r -d '' input; do
      printf '%s\0' "${input#"$grub_module_root"/}"
      sha256sum "$input"
    done < <(find "$grub_module_root" -type f -print0 | sort -z)
  } | sha256sum | awk '{print $1}'
}
iso_packaging_signature="$(compute_iso_packaging_signature)"

compute_validation_tool_signature() {
  local input
  local tool
  local tool_path
  {
    while IFS= read -r -d '' input; do
      printf '%s\0' "${input#"$repo_root"/}"
      sha256sum "$input"
    done < <(find "$repo_root/scripts" -type f -print0 | sort -z)
    for tool in bash python3 awk grep sed nm objdump readelf; do
      tool_path="$(command -v -- "$tool")"
      sha256sum "$tool_path"
    done
  } | sha256sum | awk '{print $1}'
}
validation_tool_signature="$(compute_validation_tool_signature)"
export validation_tool_signature

compute_check_signature() {
  local input
  {
    printf 'validation-tools:%s\0' "$validation_tool_signature"
    for input in "$@"; do
      if [[ -f "$input" ]]; then
        printf 'file:%s\0' "$input"
        sha256sum "$input"
      else
        printf 'value:%s\0' "$input"
      fi
    done
  } | sha256sum | awk '{print $1}'
}

cached_check_is_current() {
  local output="$1"
  local signature="$2"
  local signature_file="${output}.inputs.sha256"
  [[ -f "$output" && -f "$signature_file" ]] &&
    [[ "$(<"$signature_file")" == "$signature" ]]
}

record_check_signature() {
  local output="$1"
  local signature="$2"
  printf '%s\n' "$signature" > "${output}.inputs.sha256"
}
export -f compute_check_signature cached_check_is_current record_check_signature

run_cached_fixture_check() {
  local output="$1"
  shift
  local signature
  local staged="${output}.tmp.$$"
  signature="$(compute_check_signature fixture-check "$@")"
  if cached_check_is_current "$output" "$signature"; then
    cat "$output"
    return 0
  fi
  if ! "$@" > "$staged" 2>&1; then
    cat "$staged" >&2
    rm -f "$staged"
    return 1
  fi
  mv "$staged" "$output"
  record_check_signature "$output" "$signature"
  cat "$output"
}

compute_iso_signature() {
  local staging_root="$1"
  shift
  local input
  {
    while IFS= read -r -d '' input; do
      printf '%s\0' "${input#"$staging_root"/}"
      sha256sum "$input"
    done < <(find "$staging_root" -type f -print0 | sort -z)
    printf '%s\0' "$iso_packaging_signature"
    printf '%s\0' "$@"
  } | sha256sum | awk '{print $1}'
}

# Preserve a deterministic ISO when neither its staged bytes, its command line,
# nor the packaging tool changed.  The wrapper still refreshes every staging
# input, so changed ELFs and configuration invalidate only their own images.
grub-mkrescue() {
  local -a arguments=("$@")
  local output=""
  local staging_root=""
  local index
  for ((index = 0; index < ${#arguments[@]}; index += 1)); do
    if [[ "${arguments[$index]}" == -o ]]; then
      output="${arguments[$((index + 1))]:-}"
      staging_root="${arguments[$((index + 2))]:-}"
      break
    fi
  done
  [[ -n "$output" && -d "$staging_root" ]] || {
    echo "error: unsupported grub-mkrescue invocation" >&2
    return 1
  }

  local signature_file="${output}.inputs.sha256"
  local current_signature
  current_signature="$(compute_iso_signature "$staging_root" "$@")"
  if [[ -f "$output" && -f "$signature_file" ]] &&
      [[ "$(<"$signature_file")" == "$current_signature" ]]; then
    echo "reusing unchanged ISO ${output#"$repo_root"/}"
    return 0
  fi

  if ! "$grub_mkrescue_path" "$@"; then
    rm -f "$output" "$signature_file"
    return 1
  fi
  printf '%s\n' "$current_signature" > "$signature_file"
}

run_iso_packaging() {
  local output="$1"
  local staging_root="$2"
  grub-mkrescue -d /usr/lib/grub/i386-pc -o "$output" "$staging_root" -- \
    -volume_date uuid 2000010100000000 \
    -volume_date all_file_dates 2000010100000000 >/dev/null
}
export repo_root iso_packaging_signature grub_mkrescue_path
export -f compute_iso_signature grub-mkrescue run_iso_packaging

run_image_policy_check() {
  local key="$1"
  local elf="$2"
  local environment_name="$3"
  local environment_value="$4"
  local log="$build/image-policy-logs/$key.log"
  local signature
  signature="$(compute_check_signature image-policy "$elf" \
    "$environment_name" "$environment_value")"
  if cached_check_is_current "$log" "$signature"; then
    return 0
  fi
  : > "$log"
  if [[ -n "$environment_name" ]]; then
    env "$environment_name=$environment_value" \
      ./scripts/check-image-policy.sh "$elf" >"$log" 2>&1
  else
    ./scripts/check-image-policy.sh "$elf" >"$log" 2>&1
  fi
  record_check_signature "$log" "$signature"
}
export -f run_image_policy_check

run_entry_policy_check() {
  local key="$1"
  local elf="$2"
  local report="$3"
  local environment_name="$4"
  local environment_value="$5"
  local status=0
  local signature
  signature="$(compute_check_signature entry-policy "$elf" \
    "$environment_name" "$environment_value")"
  if cached_check_is_current "$report" "$signature"; then
    return 0
  fi
  : > "$report"
  if [[ -n "$environment_name" ]]; then
    env "$environment_name=$environment_value" \
      ./scripts/check-entry-policy.sh "$elf" >"$report" 2>&1 || status=$?
  else
    ./scripts/check-entry-policy.sh "$elf" >"$report" 2>&1 || status=$?
  fi
  if ((status != 0)); then
    printf 'error: entry policy check failed: %s\n' "$key" >> "$report"
    return "$status"
  fi
  record_check_signature "$report" "$signature"
}
export -f run_entry_policy_check

run_direct_port_check() {
  local key="$1"
  local elf="$2"
  local manifest="$3"
  local assigned_edu="$4"
  local log="$5"
  local -a arguments=()
  local raw_log="${log}.raw"
  local status=0
  local signature
  signature="$(compute_check_signature direct-port "$elf" "$manifest" \
    "$assigned_edu")"
  if cached_check_is_current "$log" "$signature"; then
    return 0
  fi
  [[ "$assigned_edu" != 1 ]] || arguments+=(--assigned-edu)
  ./scripts/check-direct-port-sites.py "$elf" "$manifest" \
    "${arguments[@]}" > "$raw_log" 2>&1 || status=$?
  if ! sed "s/^/elf=$key /" "$raw_log" > "$log"; then
    rm -f "$raw_log"
    return 1
  fi
  rm -f "$raw_log"
  if ((status == 0)); then
    record_check_signature "$log" "$signature"
  fi
  return "$status"
}
export -f run_direct_port_check

run_return_fixture_check() {
  local key="$1"
  local elf="$2"
  local expected="$3"
  local log="$4"
  local status=0
  local signature
  signature="$(compute_check_signature return-fixture "$elf" "$expected")"
  if cached_check_is_current "$log" "$signature"; then
    return 0
  fi
  ./scripts/check-image-policy.sh "$elf" > "$log" 2>&1 || status=$?
  if ((status == 0)); then
    printf 'error: user-return %s negative fixture unexpectedly passed\n' \
      "$key" >> "$log"
    return 1
  fi
  if ! grep -Fq "$expected" "$log"; then
    printf 'error: %s negative fixture lacked expected diagnostic\n' \
      "$key" >> "$log"
    return 1
  fi
  record_check_signature "$log" "$signature"
}
export -f run_return_fixture_check

run_return_corruption_policy_check() {
  local key="$1"
  local elf="$2"
  local expected="$3"
  local log="$4"
  local status=0
  local signature
  signature="$(compute_check_signature return-corruption-policy "$elf" \
    "$expected")"
  if cached_check_is_current "$log" "$signature"; then
    [[ -n "$expected" ]] || cat "$log"
    return 0
  fi
  ./scripts/check-image-policy.sh "$elf" > "$log" 2>&1 || status=$?
  if [[ -z "$expected" ]]; then
    if ((status != 0)); then
      printf 'error: return-corruption policy check failed: %s\n' "$key" \
        >> "$log"
      cat "$log" >&2
      return "$status"
    fi
    record_check_signature "$log" "$signature"
    cat "$log"
    return 0
  fi
  if ((status == 0)); then
    printf 'error: %s policy fixture unexpectedly passed\n' "$key" >> "$log"
    cat "$log" >&2
    return 1
  fi
  if ! grep -Fq "$expected" "$log"; then
    printf 'error: %s policy fixture lacked expected diagnostic\n' "$key" \
      >> "$log"
    cat "$log" >&2
    return 1
  fi
  record_check_signature "$log" "$signature"
}
export -f run_return_corruption_policy_check

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
evidence_tier="${LEANOS_EVIDENCE_TIER:-all}"
evidence_shard_index="${LEANOS_EVIDENCE_SHARD_INDEX:-}"
evidence_shard_count="${LEANOS_EVIDENCE_SHARD_COUNT:-}"
[[ -f "$matrix" ]] || { echo "error: evidence matrix '$matrix' not found" >&2; exit 1; }
return_corruptions=()
while IFS=$'\t' read -r _id runner _class _timeout _image _elf _log \
    fixture mode reason _tier; do
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
mkdir -p "$build"
build_plan_args=(
  build-plan
  --matrix "$matrix"
  --version "$version"
  --tier "$evidence_tier"
)
if [[ -n "$evidence_shard_index" || -n "$evidence_shard_count" ]]; then
  [[ -n "$evidence_shard_index" && -n "$evidence_shard_count" ]] || {
    echo "error: evidence shard index and count must be specified together" >&2
    exit 1
  }
  build_plan_args+=(
    --shard-index "$evidence_shard_index"
    --shard-count "$evidence_shard_count"
  )
fi
python3 scripts/run-emulator-evidence.py "${build_plan_args[@]}" \
  > "$build/evidence-build-plan.tsv"
declare -a selected_prelink_targets=()
declare -a selected_final_targets=()
declare -A selected_prelink_lookup=()
declare -A selected_final_lookup=()
{
  IFS=$'\t' read -r plan_id plan_runner plan_image plan_prelink plan_final
  [[ "$plan_id" == id && "$plan_runner" == runner && \
      "$plan_image" == image && "$plan_prelink" == prelink_elf && \
      "$plan_final" == final_elf ]] || {
    echo "error: evidence build plan header is invalid" >&2
    exit 1
  }
  while IFS=$'\t' read -r plan_id plan_runner plan_image plan_prelink plan_final; do
    [[ -n "$plan_id" && -n "$plan_runner" && -n "$plan_image" && \
        -n "$plan_prelink" && -n "$plan_final" ]] || {
      echo "error: evidence build plan contains an incomplete row" >&2
      exit 1
    }
    selected_prelink_targets+=("$build/$plan_prelink")
    selected_final_targets+=("$build/$plan_final")
    selected_prelink_lookup["$build/$plan_prelink"]=1
    selected_final_lookup["$build/$plan_final"]=1
    # A few families use a graph-owned object as the selected Make target and
    # perform their final link below. Index the resulting scenario ELF too so
    # validation, staging, packaging, and checksums share one selection gate.
    case "$plan_id" in
      assigned-edu-inventory)
        selected_final_lookup["$build/leanos-assigned-edu.elf"]=1
        ;;
      double-fault)
        selected_final_lookup["$build/leanos-double-fault.elf"]=1
        ;;
      entry-stack-overflow)
        selected_final_lookup["$build/leanos-entry-stack-overflow.elf"]=1
        ;;
      double-fault-guard-mapped)
        selected_final_lookup["$build/leanos-double-fault-guard-mapped.elf"]=1
        ;;
    esac
  done
} < "$build/evidence-build-plan.tsv"
[[ ${#selected_prelink_targets[@]} -gt 0 ]] || {
  echo "error: evidence build plan selected no image targets" >&2
  exit 1
}

selected_final_enabled() {
  local elf_path="$1"
  [[ "$evidence_tier" == all || -n "${selected_final_lookup[$elf_path]:-}" ]]
}
# Preserve graph-owned objects, dependency files, and ISO staging trees across
# invocations. Re-copying the three deterministic staging inputs below keeps
# their contents current while allowing unchanged packaged images to be reused.
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
current_lean_c_signature="$(compute_lean_c_signature "$repo_root")"
LEANOS_ORACLE_TOOL_SIGNATURE="$current_lean_c_signature" \
  ./scripts/generate-oracle.sh "$build"
ensure_boot_plan_stub() {
  [[ -f "$1" ]] || ./scripts/generate-boot-page-plan.sh --stub "$1"
}
ensure_boot_plan_stub "$build/boot-page-plan.h"
ensure_boot_plan_stub "$build/boot-page-plan-malformed-handoff.h"
ensure_boot_plan_stub "$build/boot-page-plan-projection-authority-mutation.h"
ensure_boot_plan_stub "$build/boot-page-plan-raw-selection-authority-mutation.h"
ensure_boot_plan_stub "$build/boot-page-plan-preemption.h"
ensure_boot_plan_stub "$build/boot-page-plan-frame-budget.h"
ensure_boot_plan_stub "$build/boot-page-plan-fault-containment.h"
ensure_boot_plan_stub "$build/boot-page-plan-fault-nx-execute.h"
for probe in "${fault_image_probes[@]}"; do
  ensure_boot_plan_stub "$build/boot-page-plan-fault-${probe}.h"
done
ensure_boot_plan_stub "$build/boot-page-plan-extended-state.h"
ensure_boot_plan_stub "$build/boot-page-plan-extended-state-peer-pke.h"
ensure_boot_plan_stub "$build/boot-page-plan-double-fault.h"
ensure_boot_plan_stub "$build/boot-page-plan-entry-overflow.h"
ensure_boot_plan_stub "$build/boot-page-plan-guard.h"
ensure_boot_plan_stub "$build/boot-page-plan-entry-adversarial.h"
ensure_boot_plan_stub "$build/boot-page-plan-nmi.h"
ensure_boot_plan_stub "$build/boot-page-plan-bootstrap32-ud.h"
ensure_boot_plan_stub "$build/boot-page-plan-bootstrap64-nmi.h"
ensure_boot_plan_stub "$build/boot-page-plan-direct-port.h"
ensure_boot_plan_stub "$build/boot-page-plan-integer-fault.h"

# C generation resolves project imports through Lake's compiled module path.
# Build them here because image jobs and clean checkouts cannot rely on a
# previous proof-check job's workspace.
lake build
generate_lean_c() {
  local source="$1"
  local output="$2"
  local staged="$lean_c_stage/${output##*/}"
  lake env lean --c="$staged" "$source"
  if [[ -f "$output" ]] && cmp -s "$staged" "$output"; then
    rm "$staged"
  else
    mv "$staged" "$output"
  fi
}
lean_c_modules=(
  KernelTransition Syscall IPCSyscall Preemption BootAllocation
  BootMemoryMapStreaming BootMemoryMapStreamAuthority BootTopology Interrupt
  InterruptEntry BlockingIPC CapabilityReuse ExtendedState
  PrivilegeEntryControl FaultDispatch DirectPortIO StaleTranslation
  FrameBudgetScenario CompositeDispatcher VTdBootPlan IOTLB
)
lean_c_signature="$build/generated-lean-c.sha256"
export LEANOS_BOOT_PLAN_TOOL_SIGNATURE="$current_lean_c_signature"
reuse_lean_c=1
if [[ ! -f "$lean_c_signature" ]] || \
    [[ "$(<"$lean_c_signature")" != "$current_lean_c_signature" ]]; then
  reuse_lean_c=0
fi
for module in "${lean_c_modules[@]}"; do
  [[ -f "$build/$module.c" ]] || reuse_lean_c=0
done
if ((reuse_lean_c == 0)); then
  lean_c_stage="$(mktemp -d "$build/.lean-c.XXXXXX")"
  trap 'rm -rf "$lean_c_stage"' EXIT
  for module in "${lean_c_modules[@]}"; do
    generate_lean_c "LeanOS/$module.lean" "$build/$module.c"
  done
  printf '%s\n' "$current_lean_c_signature" > "$lean_c_signature"
  rm -rf "$lean_c_stage"
  trap - EXIT
fi
record_build_phase bootstrap-and-lean-generation
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
# All existing image variants link BootAllocation.o.  Combine the generated
# stream transport and allocation-free topology scalar boundary into that
# reviewed object so no variant can omit either machine-enforcement edge.
# Section GC retains only the called BootTopology closure; the hosted
# ByteArray/list topology query and its Lean runtime dependencies stay absent.
# Keep the existing bounded link inventory compact while retaining the
# independently generated model adapters in every image variant.
object_graph="$build/generated-image-objects.mk"
kernel_source_signature="$build/kernel-source.inputs.sha256"
current_kernel_source_signature="$(sha256sum boot/kernel.c | awk '{print $1}')"
kernel_source_make_args=()
if [[ -f "$kernel_source_signature" ]] &&
    [[ "$(<"$kernel_source_signature")" == "$current_kernel_source_signature" ]]; then
  # GNU Make normally recompiles every kernel variant after a timestamp-only
  # source touch. The retained content signature proves the source bytes are
  # unchanged, so preserve the cached objects and continue tracking headers
  # through their generated dependency files.
  # The generated graph records the source as an absolute prerequisite. Match
  # that exact name so Make cannot miss the timestamp-only override when the
  # wrapper is invoked through a different spelling of the repository path.
  kernel_source_make_args=(-o "$repo_root/boot/kernel.c")
fi
graph_args=(
  --output "$object_graph"
  --build-dir "$build"
  --cc "$cc"
  --lean-prefix "$lean_prefix"
  --source-root "$repo_root"
)
for flag in "${cflags[@]}"; do
  graph_args+=("--cflag=$flag")
done
for spec in "${return_corruptions[@]}"; do
  IFS=: read -r fixture mode _reason <<<"$spec"
  graph_args+=(--return-corruption "${fixture}:${mode}")
done
python3 scripts/generate-image-object-graph.py "${graph_args[@]}"
# Make does not track recipe text or tool binary identity.  Invalidate only
# graph-owned products when the compiler/linker, flags, variant definitions,
# or linker inventories change, while retaining them for an identical graph
# and toolchain.
graph_signature="$build/generated-image-objects.sha256"
current_graph_signature="$(compute_graph_signature "$object_graph" "$cc")"
if [[ ! -f "$graph_signature" ]] || \
    [[ "$(<"$graph_signature")" != "$current_graph_signature" ]]; then
  find "$build" -maxdepth 1 -type f \
    \( -name '*.o' -o -name '*.o.d' -o -name '*.elf' -o -name '*.map' \
    -o -name '*.su' \) -delete
  printf '%s\n' "$current_graph_signature" > "$graph_signature"
fi

# Parsing this generated graph dominates an otherwise unchanged warm build.
# Bypass Make only when the complete repository/build input set, compiler and
# linker identity, and every retained graph output are byte-current.  The
# manifest is written only after the full wrapper succeeds below, so an
# interrupted or partially rebuilt graph always falls back to Make.
compute_graph_make_input_signature() {
  local graph_tool_signature="$1"
  {
    printf 'graph-tools:%s\0' "$graph_tool_signature"
    find "$repo_root/boot" "$repo_root/include" -type f -print0 | sort -z |
      while IFS= read -r -d '' input; do
        sha256sum "$input"
      done
    find "$build" -maxdepth 1 -type f \
      \( -name '*.c' -o \
      \( -name 'boot-page-plan*.h' ! -name '*.final.h' \) \) \
      -print0 | sort -z |
      while IFS= read -r -d '' input; do
        sha256sum "$input"
      done
  } | sha256sum | awk '{print $1}'
}

graph_make_cache_signature="$build/generated-make.inputs.sha256"
graph_make_cache_manifest="$build/generated-make.outputs.sha256"
current_graph_make_signature="$(
  compute_graph_make_input_signature "$current_graph_signature"
)"
graph_make_cache_current=false
if [[ -s "$graph_make_cache_signature" &&
    -s "$graph_make_cache_manifest" ]] &&
    [[ "$(<"$graph_make_cache_signature")" == \
      "$current_graph_make_signature" ]] &&
    sha256sum -c --status "$graph_make_cache_manifest"; then
  graph_make_cache_current=true
fi
# A cache recorded for a different PR shard can be internally valid without
# containing this shard's selected prelinks.  Treat those missing outputs as a
# cache miss so Make follows the reviewed graph for the current selection.
if [[ "$evidence_tier" != all && "$graph_make_cache_current" == true ]]; then
  for prelink in "${selected_prelink_targets[@]}"; do
    if [[ ! -f "$prelink" ]]; then
      graph_make_cache_current=false
      break
    fi
  done
fi
# The generated graph owns the migrated prelinks.  It retains their reviewed
# linker input order while scheduling independent links concurrently with the
# remaining object work.
if [[ "$graph_make_cache_current" != true ]]; then
  if [[ "$evidence_tier" == all ]]; then
    # Keep complete-evidence object compilation in its own Make invocation.
    # The generated rules preserve byte-identical outputs between invocations.
    make -f "$object_graph" "${kernel_source_make_args[@]}" \
      -j "${LEANOS_BUILD_JOBS:-$(nproc)}" \
      shared-generated-objects variant-kernel-objects variant-assembly-objects
    make -f "$object_graph" -j "${LEANOS_BUILD_JOBS:-$(nproc)}" \
      prelink-images policy-fixture-images return-corruption-prelinks
  else
    # A PR shard asks Make for only the ELF prelinks declared by its reviewed
    # matrix plan. Make follows their exact object prerequisites and does not
    # compile the unrelated complete-evidence variant family.
    make -f "$object_graph" "${kernel_source_make_args[@]}" \
      -j "${LEANOS_BUILD_JOBS:-$(nproc)}" \
      "${selected_prelink_targets[@]}"
  fi
fi
record_build_phase object-graph-prelinks

# Build the two shared Lean plan generators once before fan-out.  Concurrent
# `lake exe` invocations race while replacing the same `.lake/build` metadata
# and executable, which can expose missing/partial artifacts to sibling tasks.
# The plan computations themselves remain parallel below; only their common
# executable publication is serialized here.
lake build leanos-boot-plan leanos-vtd-plan
export LEANOS_BOOT_PLAN_EXECUTABLES_READY=1

cp scripts/entry-stack-callgraph.tsv "$build/entry-stack-callgraph.tsv"
cp scripts/entry-stack-extended-callgraph.tsv \
  "$build/entry-stack-extended-callgraph.tsv"
./scripts/check-entry-stack-budget.sh | tee "$build/entry-stack-budget.txt"
run_boot_plan_batch() {
  local task_file="$build/boot-page-plan-tasks.nul"
  : > "$task_file"
  while (($#)); do
    printf '%s\0%s\0' "$1" "$2" >> "$task_file"
    shift 2
  done
  xargs -0 -r -n 2 -P "${LEANOS_BUILD_JOBS:-$(nproc)}" \
    ./scripts/generate-boot-page-plan.sh < "$task_file"
}

boot_plan_batch_args=(
  "$build/leanos-prelink.elf" "$build/boot-page-plan.h"
  "$build/leanos-malformed-handoff-prelink.elf"
  "$build/boot-page-plan-malformed-handoff.h"
  "$build/leanos-projection-authority-mutation-prelink.elf"
  "$build/boot-page-plan-projection-authority-mutation.h"
  "$build/leanos-raw-selection-authority-mutation-prelink.elf"
  "$build/boot-page-plan-raw-selection-authority-mutation.h"
  "$build/leanos-preemption-prelink.elf" "$build/boot-page-plan-preemption.h"
  "$build/leanos-frame-budget-prelink.elf"
  "$build/boot-page-plan-frame-budget.h"
  "$build/leanos-fault-containment-prelink.elf"
  "$build/boot-page-plan-fault-containment.h"
  "$build/leanos-fault-readonly-write-prelink.elf"
  "$build/boot-page-plan-fault-readonly-write.h"
  "$build/leanos-fault-nx-execute-prelink.elf"
  "$build/boot-page-plan-fault-nx-execute.h"
)
for probe in "${fault_image_probes[@]}"; do
  boot_plan_batch_args+=(
    "$build/leanos-fault-${probe}-prelink.elf"
    "$build/boot-page-plan-fault-${probe}.h"
  )
done
for suffix in "" -mmx -sse -sse2 -avx -peer-pke; do
  boot_plan_batch_args+=(
    "$build/leanos-extended-state${suffix}-prelink.elf"
    "$build/boot-page-plan-extended-state${suffix}.h"
  )
done
for mechanism in syscall sysenter; do
  boot_plan_batch_args+=(
    "$build/leanos-fast-entry-${mechanism}-prelink.elf"
    "$build/boot-page-plan-fast-entry-${mechanism}.h"
  )
done
boot_plan_batch_args+=(
  "$build/leanos-double-fault-prelink.elf"
  "$build/boot-page-plan-double-fault.h"
  "$build/leanos-entry-stack-overflow-prelink.elf"
  "$build/boot-page-plan-entry-overflow.h"
  "$build/leanos-guard-prelink.elf" "$build/boot-page-plan-guard.h"
  "$build/leanos-entry-adversarial-prelink.elf"
  "$build/boot-page-plan-entry-adversarial.h"
  "$build/leanos-direct-port-serial-prelink.elf"
  "$build/boot-page-plan-direct-port.h"
  "$build/leanos-divide-error-prelink.elf"
  "$build/boot-page-plan-integer-fault.h"
  "$build/leanos-breakpoint-prelink.elf"
  "$build/boot-page-plan-breakpoint.h"
  "$build/leanos-nmi-prelink.elf" "$build/boot-page-plan-nmi.h"
  "$build/leanos-bootstrap32-ud-prelink.elf"
  "$build/boot-page-plan-bootstrap32-ud.h"
  "$build/leanos-bootstrap64-nmi-prelink.elf"
  "$build/boot-page-plan-bootstrap64-nmi.h"
)
for probe in debug in pic; do
  boot_plan_batch_args+=(
    "$build/leanos-direct-port-${probe}-prelink.elf"
    "$build/boot-page-plan-direct-port-${probe}.h"
  )
done
for spec in "${return_corruptions[@]}"; do
  IFS=: read -r fixture _mode _reason <<<"$spec"
  boot_plan_batch_args+=(
    "$build/leanos-return-${fixture}-prelink.elf"
    "$build/boot-page-plan-return-${fixture}.h"
  )
done
if [[ "$evidence_tier" != all ]]; then
  filtered_boot_plan_batch_args=()
  for ((index = 0; index < ${#boot_plan_batch_args[@]}; index += 2)); do
    prelink="${boot_plan_batch_args[$index]}"
    if [[ -n "${selected_prelink_lookup[$prelink]:-}" ]]; then
      filtered_boot_plan_batch_args+=(
        "$prelink" "${boot_plan_batch_args[$((index + 1))]}"
      )
    fi
  done
  boot_plan_batch_args=("${filtered_boot_plan_batch_args[@]}")
fi
run_boot_plan_batch "${boot_plan_batch_args[@]}"

if [[ "$evidence_tier" == all ]]; then
  cmp "$build/boot-page-plan-fault-containment.h" \
  "$build/boot-page-plan-fault-readonly-write.h" || {
  echo "error: read-only-write probe changed shared fault page-table plan" >&2
  exit 1
}
cmp "$build/boot-page-plan-fault-containment.h" \
  "$build/boot-page-plan-fault-nx-execute.h" || {
  echo "error: NX-execute probe changed shared fault page-table plan" >&2
  exit 1
}
for probe in "${fault_image_probes[@]}"; do
  if [[ "$probe" != stale-translation ]]; then
    cmp "$build/boot-page-plan-fault-containment.h" \
      "$build/boot-page-plan-fault-${probe}.h" || {
      echo "error: $probe probe changed shared fault page-table plan" >&2
      exit 1
    }
  fi
done
cmp "$build/boot-page-plan-extended-state.h" \
  "$build/boot-page-plan-extended-state-mmx.h" || {
  echo "error: MMX probe changed the shared extended-state page-table plan" >&2
  exit 1
}
cmp "$build/boot-page-plan-extended-state.h" \
  "$build/boot-page-plan-extended-state-sse.h" || {
  echo "error: SSE probe changed the shared extended-state page-table plan" >&2
  exit 1
}
cmp "$build/boot-page-plan-extended-state.h" \
  "$build/boot-page-plan-extended-state-sse2.h" || {
  echo "error: SSE2 probe changed the shared extended-state page-table plan" >&2
  exit 1
}
cmp "$build/boot-page-plan-extended-state.h" \
  "$build/boot-page-plan-extended-state-avx.h" || {
  echo "error: AVX probe changed the shared extended-state page-table plan" >&2
  exit 1
}
for mechanism in syscall sysenter; do
  cmp "$build/boot-page-plan-extended-state.h" \
    "$build/boot-page-plan-fast-entry-${mechanism}.h" || {
    echo "error: fast-entry $mechanism probe changed the shared page-table plan" >&2
    exit 1
  }
done
for probe in debug in pic; do
  cmp "$build/boot-page-plan-direct-port.h" \
    "$build/boot-page-plan-direct-port-${probe}.h" || {
    echo "error: direct-port $probe probe changed the shared page-table plan" >&2
    exit 1
  }
done
cmp "$build/boot-page-plan-integer-fault.h" \
  "$build/boot-page-plan-breakpoint.h" || {
  echo "error: breakpoint probe changed the shared integer-fault page-table plan" >&2
  exit 1
}
fi
# Re-enter the same graph after replacing every stub boot-page plan.  The
# generated dependency files select only affected kernel variants, and Make
# recompiles those final-plan objects concurrently instead of serially.
current_graph_make_signature="$(
  compute_graph_make_input_signature "$current_graph_signature"
)"
if [[ "$graph_make_cache_current" == true ]] &&
    [[ "$(<"$graph_make_cache_signature")" != \
      "$current_graph_make_signature" ]]; then
  graph_make_cache_current=false
fi
if [[ "$graph_make_cache_current" != true ]]; then
  if [[ "$evidence_tier" == all ]]; then
    make -f "$object_graph" "${kernel_source_make_args[@]}" \
      -j "${LEANOS_BUILD_JOBS:-$(nproc)}" \
      final-kernel-objects
  fi
fi

if [[ "$evidence_tier" == all ]] && nm "$build/kernel.o" | grep -Eq \
    'return_corruption_mode|return_corruption_name|inject_return_corruption'; then
  echo "error: normal kernel object contains return-corruption fixture code" >&2
  exit 1
fi
# Link the independent final-image family in parallel after generated page-plan
# dependencies have rebuilt the affected kernel objects.
if [[ "$graph_make_cache_current" != true ]]; then
  if [[ "$evidence_tier" == all ]]; then
    make -f "$object_graph" "${kernel_source_make_args[@]}" \
      -j "${LEANOS_BUILD_JOBS:-$(nproc)}" \
      final-image-links return-corruption-final-images
  else
    make -f "$object_graph" "${kernel_source_make_args[@]}" \
      -j "${LEANOS_BUILD_JOBS:-$(nproc)}" \
      "${selected_final_targets[@]}"
  fi
fi
record_build_phase boot-plans-and-final-links

for spec in "${return_corruptions[@]}"; do
  IFS=: read -r fixture mode _reason <<<"$spec"
  return_elf="$build/leanos-return-${fixture}.elf"
  selected_final_enabled "$return_elf" || continue
  ./scripts/generate-boot-page-plan.sh "$return_elf" \
    "$build/boot-page-plan-return-${fixture}.final.h"
  cmp "$build/boot-page-plan-return-${fixture}.h" \
    "$build/boot-page-plan-return-${fixture}.final.h" || {
    echo "error: ${fixture} boot page-table plan drifted after final link" >&2
    exit 1
  }
  expected_policy_diagnostic=""
  if [[ "$fixture" == post-validation-mutation ]]; then
    expected_policy_diagnostic='mutation or control flow added after user-return validation'
  elif [[ "$fixture" == fast-entry-sce-relaxation ||
      "$fixture" == fast-entry-lstar-relaxation ||
      "$fixture" == fast-entry-sysenter-eip-relaxation ||
      "$fixture" == fast-entry-star-relaxation ||
      "$fixture" == fast-entry-cstar-relaxation ||
      "$fixture" == fast-entry-sfmask-relaxation ||
      "$fixture" == fast-entry-sysenter-cs-relaxation ||
      "$fixture" == fast-entry-sysenter-esp-relaxation ]]; then
    expected_policy_diagnostic='fast-entry final-ELF write inventory drifted'
  fi
  run_return_corruption_policy_check "$fixture" \
    "$return_elf" "$expected_policy_diagnostic" \
    "$build/return-${fixture}-policy.log"
done

validate_selected_final_plan() {
  local elf_path="$1"
  local expected_plan="$2"
  local final_plan="$3"
  local description="$4"
  selected_final_enabled "$elf_path" || return 0
  ./scripts/generate-boot-page-plan.sh "$elf_path" "$final_plan"
  cmp "$expected_plan" "$final_plan" || {
    echo "error: $description page-table plan drifted after final link" >&2
    exit 1
  }
}

validate_selected_final_plan "$build/leanos.elf" \
  "$build/boot-page-plan.h" "$build/boot-page-plan.final.h" \
  linker-resolved
validate_selected_final_plan "$build/leanos-malformed-handoff.elf" \
  "$build/boot-page-plan-malformed-handoff.h" \
  "$build/boot-page-plan-malformed-handoff.final.h" malformed-handoff
validate_selected_final_plan "$build/leanos-projection-authority-mutation.elf" \
  "$build/boot-page-plan-projection-authority-mutation.h" \
  "$build/boot-page-plan-projection-authority-mutation.final.h" \
  "projection-authority mutation"
validate_selected_final_plan "$build/leanos-raw-selection-authority-mutation.elf" \
  "$build/boot-page-plan-raw-selection-authority-mutation.h" \
  "$build/boot-page-plan-raw-selection-authority-mutation.final.h" \
  "raw-selection authority mutation"
validate_selected_final_plan "$build/leanos-nmi.elf" \
  "$build/boot-page-plan-nmi.h" "$build/boot-page-plan-nmi.final.h" \
  "NMI probe"
validate_selected_final_plan "$build/leanos-bootstrap32-ud.elf" \
  "$build/boot-page-plan-bootstrap32-ud.h" \
  "$build/boot-page-plan-bootstrap32-ud.final.h" "bootstrap32-ud probe"
validate_selected_final_plan "$build/leanos-bootstrap64-nmi.elf" \
  "$build/boot-page-plan-bootstrap64-nmi.h" \
  "$build/boot-page-plan-bootstrap64-nmi.final.h" "bootstrap64-nmi probe"
validate_selected_final_plan "$build/leanos-preemption.elf" \
  "$build/boot-page-plan-preemption.h" \
  "$build/boot-page-plan-preemption.final.h" preemption
if selected_final_enabled "$build/leanos-frame-budget.elf"; then
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
fi
validate_selected_final_plan "$build/leanos-fault-containment.elf" \
  "$build/boot-page-plan-fault-containment.h" \
  "$build/boot-page-plan-fault-containment.final.h" fault-containment
validate_selected_final_plan "$build/leanos-fault-readonly-write.elf" \
  "$build/boot-page-plan-fault-containment.h" \
  "$build/boot-page-plan-fault-readonly-write.final.h" read-only-write
validate_selected_final_plan "$build/leanos-fault-nx-execute.elf" \
  "$build/boot-page-plan-fault-containment.h" \
  "$build/boot-page-plan-fault-nx-execute.final.h" NX-execute
for probe in "${fault_image_probes[@]}"; do
  selected_final_enabled "$build/leanos-fault-${probe}.elf" || continue
  ./scripts/generate-boot-page-plan.sh "$build/leanos-fault-${probe}.elf" \
    "$build/boot-page-plan-fault-${probe}.final.h"
  # A PR shard may select this probe without selecting fault-containment, whose
  # plan header is then only a stub.  Compare the probe's generated prelink plan
  # to its final plan in that case; full evidence retains the stronger
  # cross-variant containment-plan equality below.
  expected_fault_plan="$build/boot-page-plan-fault-${probe}.h"
  if [[ "$evidence_tier" == all && "$probe" != stale-translation ]]; then
    expected_fault_plan="$build/boot-page-plan-fault-containment.h"
  fi
  if [[ "$probe" == stale-translation ]]; then
    for pass in 1 2 3; do
      cmp -s "$expected_fault_plan" \
        "$build/boot-page-plan-fault-${probe}.final.h" && break
      cp "$build/boot-page-plan-fault-${probe}.final.h" \
        "$expected_fault_plan"
      "$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
        -DLEANOS_FAULT_CONTAINMENT_SCENARIO=1 \
        "${fault_fatal_probe_flags[$probe]}" \
        -DLEANOS_BOOT_PAGE_PLAN_HEADER='"boot-page-plan-fault-stale-translation.h"' \
        -c boot/kernel.c -o "$build/kernel-fault-${probe}.o"
      ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
        -T boot/linker.ld -Map "$build/leanos-fault-${probe}.map" \
        -o "$build/leanos-fault-${probe}.elf" \
        "$build/boot-fault-${probe}.o" "$build/kernel-fault-${probe}.o" \
        "$build/KernelTransition.o" "$build/Syscall.o" \
        "$build/IPCSyscall.o" "$build/Preemption.o" \
        "$build/BootAllocation.o" "$build/Interrupt.o" \
        "$build/InterruptEntry.o" "$build/BlockingIPC.o" \
        "$build/CapabilityReuse.o" "$build/ExtendedState.o" \
        "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
      ./scripts/generate-boot-page-plan.sh \
        "$build/leanos-fault-${probe}.elf" \
        "$build/boot-page-plan-fault-${probe}.final.h"
    done
  fi
  cmp "$expected_fault_plan" \
    "$build/boot-page-plan-fault-${probe}.final.h" || {
    echo "error: $probe page-table plan drifted after final link" >&2
    exit 1
  }
done
validate_selected_final_plan "$build/leanos-extended-state.elf" \
  "$build/boot-page-plan-extended-state.h" \
  "$build/boot-page-plan-extended-state.final.h" extended-state
validate_selected_final_plan "$build/leanos-extended-state-peer-pke.elf" \
  "$build/boot-page-plan-extended-state-peer-pke.h" \
  "$build/boot-page-plan-extended-state-peer-pke.final.h" peer-PKE
for mechanism in syscall sysenter; do
  validate_selected_final_plan \
    "$build/leanos-fast-entry-${mechanism}.elf" \
    "$build/boot-page-plan-extended-state.h" \
    "$build/boot-page-plan-fast-entry-${mechanism}.final.h" \
    "fast-entry $mechanism"
done
for extended_state_variant in mmx sse sse2 avx; do
  validate_selected_final_plan \
    "$build/leanos-extended-state-${extended_state_variant}.elf" \
    "$build/boot-page-plan-extended-state.h" \
    "$build/boot-page-plan-extended-state-${extended_state_variant}.final.h" \
    "${extended_state_variant^^} extended-state"
done
if selected_final_enabled "$build/leanos-double-fault.elf"; then
  ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
    -T boot/linker.ld -Map build/boot/leanos-double-fault.map \
    -o build/boot/leanos-double-fault.elf build/boot/boot.o \
    build/boot/kernel-double-fault.o build/boot/KernelTransition.o \
    build/boot/Syscall.o build/boot/IPCSyscall.o build/boot/Preemption.o \
    build/boot/BootAllocation.o build/boot/Interrupt.o build/boot/InterruptEntry.o \
    build/boot/BlockingIPC.o build/boot/CapabilityReuse.o build/boot/ExtendedState.o build/boot/PrivilegeEntryControl.o build/boot/FaultDispatch.o
  ./scripts/generate-boot-page-plan.sh "$build/leanos-double-fault.elf" \
    "$build/boot-page-plan-double-fault.final.h"
  cmp "$build/boot-page-plan-double-fault.h" \
    "$build/boot-page-plan-double-fault.final.h" || {
    echo "error: double-fault boot page-table plan drifted after final link" >&2
    exit 1
  }
fi
if selected_final_enabled "$build/leanos-entry-stack-overflow.elf"; then
  ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
    -T boot/linker.ld -Map "$build/leanos-entry-stack-overflow.map" \
    -o "$build/leanos-entry-stack-overflow.elf" \
    "$build/boot-entry-stack-overflow.o" "$build/kernel-entry-stack-overflow.o" \
    "$build/KernelTransition.o" "$build/Syscall.o" "$build/IPCSyscall.o" \
    "$build/Preemption.o" "$build/BootAllocation.o" "$build/Interrupt.o" \
    "$build/InterruptEntry.o" "$build/BlockingIPC.o" "$build/CapabilityReuse.o" \
    "$build/ExtendedState.o" "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
  ./scripts/generate-boot-page-plan.sh "$build/leanos-entry-stack-overflow.elf" \
    "$build/boot-page-plan-entry-overflow.final.h"
  cmp "$build/boot-page-plan-entry-overflow.h" \
    "$build/boot-page-plan-entry-overflow.final.h" || {
    echo "error: entry-stack overflow page-table plan drifted after final link" >&2
    exit 1
  }
fi
if selected_final_enabled "$build/leanos-double-fault-guard-mapped.elf"; then
  ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
    -T boot/linker.ld -Map build/boot/leanos-double-fault-guard-mapped.map \
    -o build/boot/leanos-double-fault-guard-mapped.elf \
    build/boot/boot-df-guard-mapped.o \
    build/boot/kernel-double-fault-guard-mapped.o \
    build/boot/KernelTransition.o build/boot/Syscall.o build/boot/IPCSyscall.o \
    build/boot/Preemption.o build/boot/BootAllocation.o build/boot/Interrupt.o build/boot/InterruptEntry.o \
    build/boot/BlockingIPC.o build/boot/CapabilityReuse.o build/boot/ExtendedState.o build/boot/PrivilegeEntryControl.o build/boot/FaultDispatch.o
  ./scripts/generate-boot-page-plan.sh "$build/leanos-double-fault-guard-mapped.elf" \
    "$build/boot-page-plan-guard.final.h"
  cmp "$build/boot-page-plan-guard.h" "$build/boot-page-plan-guard.final.h" || {
    echo "error: guard-mapped boot page-table plan drifted after final link" >&2
    exit 1
  }
fi
validate_selected_final_plan "$build/leanos-entry-adversarial.elf" \
  "$build/boot-page-plan-entry-adversarial.h" \
  "$build/boot-page-plan-entry-adversarial.final.h" entry-adversarial
for probe in "${direct_port_probes[@]}"; do
  selected_final_enabled "$build/leanos-direct-port-${probe}.elf" || continue
  ./scripts/generate-boot-page-plan.sh "$build/leanos-direct-port-${probe}.elf" \
    "$build/boot-page-plan-direct-port-${probe}.final.h"
  cmp "$build/boot-page-plan-direct-port.h" \
    "$build/boot-page-plan-direct-port-${probe}.final.h" || {
    echo "error: direct-port $probe boot page-table plan drifted after final link" >&2
    exit 1
  }
done
for probe in "${integer_fault_probes[@]}"; do
  selected_final_enabled "$build/leanos-${probe}.elf" || continue
  ./scripts/generate-boot-page-plan.sh "$build/leanos-${probe}.elf" \
    "$build/boot-page-plan-${probe}.final.h"
  cmp "$build/boot-page-plan-integer-fault.h" \
    "$build/boot-page-plan-${probe}.final.h" || {
    echo "error: integer-fault $probe boot page-table plan drifted after final link" >&2
    exit 1
  }
done

if selected_final_enabled "$build/leanos.elf"; then
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
fi
if selected_final_enabled "$build/leanos-extended-state.elf"; then
LEANOS_ENTRY_STACK_MANIFEST=scripts/entry-stack-extended-callgraph.tsv \
  LEANOS_ENTRY_STACK_OPTIMIZER_OPTIONAL=scripts/entry-stack-extended-optimizer-optional.tsv \
  LEANOS_ENTRY_STACK_ELF_EDGES_OUTPUT="$build/entry-stack-extended-final-elf-edges.tsv" \
  ./scripts/check-entry-stack-budget.sh "$build/leanos-extended-state.elf" \
  | tee "$build/entry-stack-extended-final-elf.txt"
fi
if selected_final_enabled "$build/leanos-extended-state-peer-pke.elf"; then
LEANOS_ENTRY_STACK_MANIFEST=scripts/entry-stack-extended-callgraph.tsv \
  LEANOS_ENTRY_STACK_OPTIMIZER_OPTIONAL=scripts/entry-stack-extended-optimizer-optional.tsv \
  LEANOS_ENTRY_STACK_ELF_EDGES_OUTPUT="$build/entry-stack-extended-state-peer-pke-final-elf-edges.tsv" \
  ./scripts/check-entry-stack-budget.sh "$build/leanos-extended-state-peer-pke.elf" \
  | tee "$build/entry-stack-extended-state-peer-pke-final-elf.txt"
fi
policy_jobs="${LEANOS_BUILD_JOBS:-$(nproc)}"
[[ "$policy_jobs" =~ ^[1-9][0-9]*$ ]] || {
  echo "error: LEANOS_BUILD_JOBS must be a positive integer" >&2
  exit 1
}
policy_task_file="$build/image-policy-tasks.nul"
policy_log_dir="$build/image-policy-logs"
mkdir -p "$policy_log_dir"
: > "$policy_task_file"
policy_keys=()
queue_image_policy() {
  local key="$1"
  local elf="$2"
  local environment_name="${3:-}"
  local environment_value="${4:-}"
  selected_final_enabled "$elf" || return 0
  policy_keys+=("$key")
  printf '%s\0%s\0%s\0%s\0' \
    "$key" "$elf" "$environment_name" "$environment_value" \
    >> "$policy_task_file"
}

queue_image_policy canonical "$build/leanos.elf"
queue_image_policy malformed-handoff "$build/leanos-malformed-handoff.elf"
queue_image_policy projection-authority-mutation \
  "$build/leanos-projection-authority-mutation.elf"
queue_image_policy raw-selection-authority-mutation \
  "$build/leanos-raw-selection-authority-mutation.elf"
queue_image_policy preemption "$build/leanos-preemption.elf"
queue_image_policy frame-budget "$build/leanos-frame-budget.elf"
queue_image_policy fault-containment "$build/leanos-fault-containment.elf"
queue_image_policy fault-readonly-write "$build/leanos-fault-readonly-write.elf"
queue_image_policy fault-nx-execute "$build/leanos-fault-nx-execute.elf"
for probe in "${fault_fatal_probes[@]}"; do
  queue_image_policy "fault-$probe" "$build/leanos-fault-${probe}.elf" \
    LEANOS_PAGE_FAULT_FATAL_PROBE "$probe"
done
queue_image_policy fault-stale-translation \
  "$build/leanos-fault-stale-translation.elf"
queue_image_policy extended-state "$build/leanos-extended-state.elf"
queue_image_policy extended-state-mmx "$build/leanos-extended-state-mmx.elf"
queue_image_policy extended-state-sse "$build/leanos-extended-state-sse.elf"
queue_image_policy extended-state-sse2 "$build/leanos-extended-state-sse2.elf"
queue_image_policy extended-state-avx "$build/leanos-extended-state-avx.elf"
for mechanism in syscall sysenter; do
  queue_image_policy "fast-entry-$mechanism" \
    "$build/leanos-fast-entry-${mechanism}.elf" LEANOS_FAST_ENTRY_PROBE \
    "$mechanism"
done
queue_image_policy double-fault "$build/leanos-double-fault.elf"
queue_image_policy entry-stack-overflow "$build/leanos-entry-stack-overflow.elf"
queue_image_policy entry-adversarial "$build/leanos-entry-adversarial.elf"
for probe in "${direct_port_probes[@]}"; do
  queue_image_policy "direct-port-$probe" \
    "$build/leanos-direct-port-${probe}.elf"
done
for probe in "${integer_fault_probes[@]}"; do
  queue_image_policy "$probe" "$build/leanos-${probe}.elf"
done
queue_image_policy bootstrap32-ud "$build/leanos-bootstrap32-ud.elf"
queue_image_policy bootstrap64-nmi "$build/leanos-bootstrap64-nmi.elf"

export build
if ! xargs -0 -r -n 4 -P "$policy_jobs" bash -c \
    'run_image_policy_check "$@"' _ < "$policy_task_file"; then
  for key in "${policy_keys[@]}"; do
    [[ -f "$policy_log_dir/$key.log" ]] && cat "$policy_log_dir/$key.log"
  done
  echo "error: one or more image policy checks failed" >&2
  exit 1
fi
for key in "${policy_keys[@]}"; do
  cat "$policy_log_dir/$key.log"
done

if selected_final_enabled "$build/leanos-frame-budget.elf"; then
  ./scripts/check-frame-budget-machine.sh "$build/leanos-frame-budget.elf"
fi
if selected_final_enabled "$build/leanos-nmi.elf"; then
  ./scripts/check-nmi-image-policy.sh "$build/leanos-nmi.elf"
  objdump -d --no-show-raw-insn "$build/leanos-nmi.elf" \
    > "$build/nmi.disassembly.txt"
fi
if [[ "$evidence_tier" == all ]]; then
  cp "$build/leanos-nmi.elf" "$build/leanos-nmi-cpl3.elf"
  cp "$build/leanos-nmi.map" "$build/leanos-nmi-cpl3.map"
  cp "$build/nmi.disassembly.txt" "$build/nmi-cpl3.disassembly.txt"
fi
if selected_final_enabled "$build/leanos-bootstrap32-ud.elf"; then
  ./scripts/check-early-probe-policy.py "$build/leanos-bootstrap32-ud.elf" \
    bootstrap32-ud | tee "$build/bootstrap32-ud-early-probe-policy.txt"
fi
if selected_final_enabled "$build/leanos-bootstrap64-nmi.elf"; then
  ./scripts/check-early-probe-policy.py "$build/leanos-bootstrap64-nmi.elf" \
    bootstrap64-nmi | tee "$build/bootstrap64-nmi-early-probe-policy.txt"
fi
write_selected_disassembly() {
  local elf="$1"
  local output="$2"
  selected_final_enabled "$elf" || return 0
  objdump -d --no-show-raw-insn "$elf" > "$output"
}
write_selected_disassembly "$build/leanos-bootstrap32-ud.elf" \
  "$build/bootstrap32-ud.disassembly.txt"
write_selected_disassembly "$build/leanos-bootstrap64-nmi.elf" \
  "$build/bootstrap64-nmi.disassembly.txt"
write_selected_disassembly "$build/leanos-fault-containment.elf" \
  "$build/fault-containment.disassembly.txt"
write_selected_disassembly "$build/leanos-fault-readonly-write.elf" \
  "$build/fault-readonly-write.disassembly.txt"
write_selected_disassembly "$build/leanos-fault-nx-execute.elf" \
  "$build/fault-nx-execute.disassembly.txt"
for probe in "${fault_image_probes[@]}"; do
  write_selected_disassembly "$build/leanos-fault-${probe}.elf" \
    "$build/fault-${probe}.disassembly.txt"
done
write_selected_disassembly "$build/leanos-extended-state.elf" \
  "$build/extended-state.disassembly.txt"
for variant in mmx sse sse2 avx; do
  write_selected_disassembly "$build/leanos-extended-state-${variant}.elf" \
    "$build/extended-state-${variant}.disassembly.txt"
done
for probe in "${direct_port_probes[@]}"; do
  write_selected_disassembly "$build/leanos-direct-port-${probe}.elf" \
    "$build/direct-port-${probe}.disassembly.txt"
done
for probe in "${integer_fault_probes[@]}"; do
  write_selected_disassembly "$build/leanos-${probe}.elf" \
    "$build/${probe}.disassembly.txt"
done
run_selected_extended_state_policy() {
  local variant="$1"
  local elf="$2"
  local report="$3"
  selected_final_enabled "$elf" || return 0
  ./scripts/check-extended-state-policy.sh "$elf" "$variant" | tee "$report"
}
run_selected_extended_state_policy x87 "$build/leanos-extended-state.elf" \
  "$build/extended-state-policy-report.txt"
for variant in mmx sse sse2 avx; do
  run_selected_extended_state_policy "$variant" \
    "$build/leanos-extended-state-${variant}.elf" \
    "$build/extended-state-${variant}-policy-report.txt"
done
if [[ "$evidence_tier" == all ]]; then
  ./scripts/test-extended-state-policy.sh "$build/leanos-extended-state.elf" \
    "$build/leanos-extended-state-mmx.elf" \
    "$build/leanos-extended-state-sse.elf" \
    "$build/leanos-extended-state-sse2.elf" \
    "$build/leanos-extended-state-avx.elf"
fi

entry_policy_task_file="$build/entry-policy-tasks.nul"
: > "$entry_policy_task_file"
entry_policy_reports=()
queue_entry_policy() {
  local key="$1"
  local elf="$2"
  local report="$3"
  local environment_name="${4:-}"
  local environment_value="${5:-}"
  selected_final_enabled "$elf" || return 0
  entry_policy_reports+=("$report")
  printf '%s\0%s\0%s\0%s\0%s\0' \
    "$key" "$elf" "$report" "$environment_name" "$environment_value" \
    >> "$entry_policy_task_file"
}

queue_entry_policy canonical "$build/leanos.elf" \
  "$build/entry-policy-report.txt"
for mechanism in syscall sysenter; do
  queue_entry_policy "fast-entry-$mechanism" \
    "$build/leanos-fast-entry-${mechanism}.elf" \
    "$build/fast-entry-${mechanism}-policy-report.txt" \
    LEANOS_FAST_ENTRY_PROBE "$mechanism"
done
queue_entry_policy fault-containment "$build/leanos-fault-containment.elf" \
  "$build/fault-containment-policy-report.txt" LEANOS_PAGE_FAULT_PROBE \
  supervisor-read
queue_entry_policy fault-readonly-write \
  "$build/leanos-fault-readonly-write.elf" \
  "$build/fault-readonly-write-policy-report.txt" LEANOS_PAGE_FAULT_PROBE \
  readonly-write
queue_entry_policy fault-nx-execute "$build/leanos-fault-nx-execute.elf" \
  "$build/fault-nx-execute-policy-report.txt" LEANOS_PAGE_FAULT_PROBE \
  nx-execute
for probe in "${fault_fatal_probes[@]}"; do
  queue_entry_policy "fault-$probe" "$build/leanos-fault-${probe}.elf" \
    "$build/fault-${probe}-policy-report.txt" LEANOS_PAGE_FAULT_FATAL_PROBE \
    "$probe"
done
queue_entry_policy fault-stale-translation \
  "$build/leanos-fault-stale-translation.elf" \
  "$build/fault-stale-translation-policy-report.txt"

if ! xargs -0 -r -n 5 -P "$policy_jobs" bash -c \
    'run_entry_policy_check "$@"' _ < "$entry_policy_task_file"; then
  for report in "${entry_policy_reports[@]}"; do
    [[ -f "$report" ]] && cat "$report"
  done
  echo "error: one or more entry policy checks failed" >&2
  exit 1
fi
for report in "${entry_policy_reports[@]}"; do
  cat "$report"
done
if [[ "$evidence_tier" == all ]]; then
  run_cached_fixture_check "$build/entry-policy-fixtures.log" \
    ./scripts/test-entry-policy.sh "$build/leanos.elf" \
    "$build/leanos-fault-nx-execute.elf"
  run_cached_fixture_check "$build/runtime-invalidation-policy-fixtures.log" \
    ./scripts/test-runtime-invalidation-policy.sh "$build/leanos.elf"
  run_cached_fixture_check "$build/vtd-mmio-policy-fixtures.log" \
    ./scripts/test-vtd-mmio-policy.sh "$build/leanos.elf"
  run_cached_fixture_check "$build/frame-budget-invalidation-policy-fixtures.log" \
    ./scripts/test-frame-budget-invalidation-policy.sh \
    "$build/leanos-frame-budget.elf"
fi
if selected_final_enabled "$build/leanos-assigned-edu.elf"; then
  source ./scripts/build-assigned-edu-image.sh
fi
direct_port_report="$build/direct-port-sites-report.txt"
: > "$direct_port_report"
direct_port_images=0
direct_port_task_file="$build/direct-port-tasks.nul"
direct_port_log_dir="$build/direct-port-logs"
mkdir -p "$direct_port_log_dir"
: > "$direct_port_task_file"
direct_port_logs=()
declare -A direct_port_seen=()
while IFS=$'\t' read -r _id _runner _class _timeout _image elf_name \
    _log _scenario _mode _reason _tier; do
  [[ "$elf_name" == *.elf ]] || continue
  elf_path="$build/$elf_name"
  if [[ "$evidence_tier" != all &&
      -z "${selected_final_lookup[$elf_path]:-}" ]]; then
    continue
  fi
  if [[ "$evidence_tier" != all &&
      -n "${direct_port_seen[$elf_path]:-}" ]]; then
    continue
  fi
  direct_port_seen["$elf_path"]=1
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
    leanos-assigned-edu.elf)
      direct_port_args+=(--assigned-edu)
      ;;
  esac
  direct_port_log="$direct_port_log_dir/$elf_name.log"
  direct_port_logs+=("$direct_port_log")
  assigned_edu=0
  ((${#direct_port_args[@]} == 0)) || assigned_edu=1
  printf '%s\0%s\0%s\0%s\0%s\0' "$elf_name" "$elf_path" \
    "$manifest" "$assigned_edu" "$direct_port_log" >> "$direct_port_task_file"
  ((direct_port_images += 1))
done < "$matrix"
expected_evidence_images="$(
  awk -F $'\t' '$1 == "# mandatory-count" { print $2 }' \
    scripts/emulator-evidence-matrix.tsv
)"
if [[ "$evidence_tier" == all ]]; then
  [[ "$expected_evidence_images" =~ ^[0-9]+$ &&
     "$direct_port_images" -eq "$expected_evidence_images" ]] || {
    echo "error: direct-port evidence ELF count drifted: $direct_port_images" >&2
    exit 1
  }
elif ((direct_port_images == 0)); then
  echo "error: selected evidence has no direct-port ELF coverage" >&2
  exit 1
fi
if ! xargs -0 -r -n 5 -P "$policy_jobs" bash -c \
    'run_direct_port_check "$@"' _ < "$direct_port_task_file"; then
  for log in "${direct_port_logs[@]}"; do
    [[ -f "$log" ]] && cat "$log"
  done
  echo "error: one or more direct-port evidence checks failed" >&2
  exit 1
fi
for log in "${direct_port_logs[@]}"; do
  cat "$log" >> "$direct_port_report"
done
cat "$direct_port_report"
if [[ "$evidence_tier" == all ]]; then
  ./scripts/test-direct-port-sites.sh "$build/leanos.elf" \
    | tee "$build/direct-port-sites-fixtures.log"
  ./scripts/test-direct-port-sites.sh "$build/leanos-entry-adversarial.elf" \
    scripts/direct-port-sites-entry-adversarial.tsv \
    | tee -a "$build/direct-port-sites-fixtures.log"
fi

return_fixture_task_file="$build/return-fixture-tasks.nul"
: > "$return_fixture_task_file"
return_fixture_logs=()
queue_return_fixture() {
  local key="$1"
  local expected="$2"
  local log="$build/return-${key}-fixture.log"
  return_fixture_logs+=("$log")
  printf '%s\0%s\0%s\0%s\0' "$key" \
    "$build/leanos-return-${key}-fixture.elf" "$expected" "$log" \
    >> "$return_fixture_task_file"
}
if [[ "$evidence_tier" == all ]]; then
  queue_return_fixture restore 'error: unexpected exact user-return restore sequence'
  queue_return_fixture branch 'enters post-validation restore interval'
  queue_return_fixture indirect 'indirect control-flow instruction'
  queue_return_fixture initial-indirect 'indirect control-flow instruction'
fi
if ! xargs -0 -r -n 4 -P "$policy_jobs" bash -c \
    'run_return_fixture_check "$@"' _ < "$return_fixture_task_file"; then
  for log in "${return_fixture_logs[@]}"; do
    [[ -f "$log" ]] && cat "$log"
  done
  echo "error: one or more return-policy negative fixtures failed" >&2
  exit 1
fi
record_build_phase policy-and-fixture-validation

printf '%s\n' "$source_revision" > "$build/SOURCE_REVISION"
declare -A selected_iso_root_lookup=()
stage_selected_image() {
  local elf="$1"
  local staging_root="$2"
  local grub_config="$3"
  selected_final_enabled "$elf" || return 0
  selected_iso_root_lookup["$staging_root"]="$elf"
  cp "$elf" "$staging_root/boot/leanos.elf"
  cp "$grub_config" "$staging_root/boot/grub/grub.cfg"
  cp "$build/SOURCE_REVISION" "$staging_root/boot/SOURCE_REVISION"
}
stage_selected_image "$build/leanos.elf" "$iso_root" boot/grub.cfg
stage_selected_image "$build/leanos-malformed-handoff.elf" \
  "$malformed_handoff_iso_root" boot/grub.cfg
stage_selected_image "$build/leanos-projection-authority-mutation.elf" \
  "$projection_authority_iso_root" boot/grub.cfg
stage_selected_image "$build/leanos-raw-selection-authority-mutation.elf" \
  "$raw_selection_authority_iso_root" boot/grub.cfg
stage_selected_image "$build/leanos-preemption.elf" "$preemption_iso_root" boot/grub.cfg
stage_selected_image "$build/leanos-frame-budget.elf" "$frame_budget_iso_root" boot/grub.cfg
stage_selected_image "$build/leanos-fault-containment.elf" \
  "$fault_containment_iso_root" boot/grub.cfg
stage_selected_image "$build/leanos-fault-readonly-write.elf" \
  "$fault_readonly_write_iso_root" boot/grub.cfg
stage_selected_image "$build/leanos-fault-nx-execute.elf" \
  "$fault_nx_execute_iso_root" boot/grub.cfg
for probe in "${fault_image_probes[@]}"; do
  stage_selected_image "$build/leanos-fault-${probe}.elf" \
    "$build/iso-fault-${probe}" boot/grub.cfg
done
stage_selected_image "$build/leanos-extended-state.elf" \
  "$extended_state_iso_root" boot/grub.cfg
for variant in mmx sse sse2 avx; do
  stage_selected_image "$build/leanos-extended-state-${variant}.elf" \
    "$build/iso-extended-state-${variant}" boot/grub.cfg
done
stage_selected_image "$build/leanos-extended-state-peer-pke.elf" \
  "$extended_state_peer_pke_iso_root" boot/grub.cfg
for mechanism in syscall sysenter; do
  stage_selected_image "$build/leanos-fast-entry-${mechanism}.elf" \
    "$build/iso-fast-entry-${mechanism}" boot/grub.cfg
done
stage_selected_image "$build/leanos-double-fault.elf" "$df_iso_root" \
  boot/grub-double-fault.cfg
stage_selected_image "$build/leanos-double-fault-guard-mapped.elf" \
  "$df_negative_iso_root" boot/grub-double-fault.cfg
stage_selected_image "$build/leanos-entry-stack-overflow.elf" \
  "$entry_overflow_iso_root" boot/grub-double-fault.cfg
stage_selected_image "$build/leanos-entry-adversarial.elf" \
  "$entry_adversarial_iso_root" boot/grub.cfg
stage_selected_image "$build/leanos-nmi.elf" "$nmi_iso_root" boot/grub.cfg
stage_selected_image "$build/leanos-nmi-cpl3.elf" "$nmi_cpl3_iso_root" \
  boot/grub-nmi-cpl3.cfg
stage_selected_image "$build/leanos-bootstrap32-ud.elf" \
  "$bootstrap32_ud_iso_root" boot/grub.cfg
stage_selected_image "$build/leanos-bootstrap64-nmi.elf" \
  "$bootstrap64_nmi_iso_root" boot/grub.cfg
for probe in "${direct_port_probes[@]}"; do
  stage_selected_image "$build/leanos-direct-port-${probe}.elf" \
    "$build/iso-direct-port-${probe}" boot/grub.cfg
done
for probe in "${integer_fault_probes[@]}"; do
  stage_selected_image "$build/leanos-${probe}.elf" "$build/iso-${probe}" \
    boot/grub.cfg
done
for spec in "${return_corruptions[@]}"; do
  IFS=: read -r fixture _mode _reason <<<"$spec"
  fixture_root="$build/iso-return-${fixture}"
  return_elf="$build/leanos-return-${fixture}.elf"
  selected_final_enabled "$return_elf" || continue
  mkdir -p "$fixture_root/boot/grub"
  cp "$return_elf" "$fixture_root/boot/leanos.elf"
  cp boot/grub.cfg "$fixture_root/boot/grub/grub.cfg"
  cp "$build/SOURCE_REVISION" "$fixture_root/boot/SOURCE_REVISION"
  selected_iso_root_lookup["$fixture_root"]="$return_elf"
done
# BIOS-only output avoids GRUB's nondeterministic FAT/EFI image. A fixed ISO
# UUID and file dates make repeated builds independent of wall-clock time. The
# staging roots and outputs are disjoint, so package the image family with the
# same bounded worker count used by the independent validation batches.
iso_task_file="$build/iso-packaging-tasks.nul"
: > "$iso_task_file"
selected_checksum_paths=()
queue_iso() {
  local output="$1"
  local staging_root="$2"
  local elf="${selected_iso_root_lookup[$staging_root]:-}"
  local map
  [[ -n "$elf" ]] || return 0
  printf '%s\0%s\0' "$output" "$staging_root" >> "$iso_task_file"
  selected_checksum_paths+=("$output" "$elf")
  map="${elf%.elf}.map"
  [[ ! -f "$map" ]] || selected_checksum_paths+=("$map")
}
queue_iso "$build/leanos-${version}-x86_64.iso" "$iso_root"
queue_iso "$build/leanos-${version}-x86_64-malformed-handoff.iso" \
  "$malformed_handoff_iso_root"
queue_iso "$build/leanos-${version}-x86_64-projection-authority-mutation.iso" \
  "$projection_authority_iso_root"
queue_iso "$build/leanos-${version}-x86_64-raw-selection-authority-mutation.iso" \
  "$raw_selection_authority_iso_root"
queue_iso "$build/leanos-${version}-x86_64-preemption.iso" \
  "$preemption_iso_root"
queue_iso "$build/leanos-${version}-x86_64-frame-budget.iso" \
  "$frame_budget_iso_root"
queue_iso "$build/leanos-${version}-x86_64-fault-containment.iso" \
  "$fault_containment_iso_root"
queue_iso "$build/leanos-${version}-x86_64-fault-readonly-write.iso" \
  "$fault_readonly_write_iso_root"
queue_iso "$build/leanos-${version}-x86_64-fault-nx-execute.iso" \
  "$fault_nx_execute_iso_root"
for probe in "${fault_image_probes[@]}"; do
  queue_iso "$build/leanos-${version}-x86_64-fault-${probe}.iso" \
    "$build/iso-fault-${probe}"
done
queue_iso "$build/leanos-${version}-x86_64-extended-state.iso" \
  "$extended_state_iso_root"
queue_iso "$build/leanos-${version}-x86_64-extended-state-mmx.iso" \
  "$extended_state_mmx_iso_root"
queue_iso "$build/leanos-${version}-x86_64-extended-state-sse.iso" \
  "$extended_state_sse_iso_root"
queue_iso "$build/leanos-${version}-x86_64-extended-state-sse2.iso" \
  "$extended_state_sse2_iso_root"
queue_iso "$build/leanos-${version}-x86_64-extended-state-avx.iso" \
  "$extended_state_avx_iso_root"
queue_iso "$build/leanos-${version}-x86_64-extended-state-peer-pke.iso" \
  "$extended_state_peer_pke_iso_root"
for mechanism in syscall sysenter; do
  queue_iso "$build/leanos-${version}-x86_64-fast-entry-${mechanism}.iso" \
    "$build/iso-fast-entry-${mechanism}"
done
queue_iso "$build/leanos-${version}-x86_64-double-fault.iso" "$df_iso_root"
queue_iso "$build/leanos-${version}-x86_64-double-fault-guard-mapped.iso" \
  "$df_negative_iso_root"
queue_iso "$build/leanos-${version}-x86_64-entry-stack-overflow.iso" \
  "$entry_overflow_iso_root"
queue_iso "$build/leanos-${version}-x86_64-entry-adversarial.iso" \
  "$entry_adversarial_iso_root"
queue_iso "$build/leanos-${version}-x86_64-nmi.iso" "$nmi_iso_root"
queue_iso "$build/leanos-${version}-x86_64-nmi-cpl3.iso" \
  "$nmi_cpl3_iso_root"
queue_iso "$build/leanos-${version}-x86_64-bootstrap32-ud.iso" \
  "$bootstrap32_ud_iso_root"
queue_iso "$build/leanos-${version}-x86_64-bootstrap64-nmi.iso" \
  "$bootstrap64_nmi_iso_root"
for probe in "${direct_port_probes[@]}"; do
  queue_iso "$build/leanos-${version}-x86_64-direct-port-${probe}.iso" \
    "$build/iso-direct-port-${probe}"
done
for probe in "${integer_fault_probes[@]}"; do
  queue_iso "$build/leanos-${version}-x86_64-${probe}.iso" \
    "$build/iso-${probe}"
done
for spec in "${return_corruptions[@]}"; do
  IFS=: read -r fixture _mode _reason <<<"$spec"
  queue_iso "$build/leanos-${version}-x86_64-return-${fixture}.iso" \
    "$build/iso-return-${fixture}"
done
if ! xargs -0 -r -n 2 -P "$policy_jobs" bash -c \
    'run_iso_packaging "$@"' _ < "$iso_task_file"; then
  echo "error: one or more deterministic ISO packages failed" >&2
  exit 1
fi
record_build_phase iso-packaging
# The multi-vCPU policy run intentionally exercises the ordinary reviewed
# image and ELF. Materialize distinct evidence identities only after that
# canonical pair is complete so the matrix remains one-to-one without a
# second build or a divergent guest binary.
if grep -q $'^multivcpu-rejection\t' "$build/evidence-build-plan.tsv"; then
  cp "$build/leanos-${version}-x86_64.iso" \
    "$build/leanos-${version}-x86_64-multivcpu-rejection.iso"
  cp "$build/leanos.elf" "$build/leanos-multivcpu-rejection.elf"
  selected_checksum_paths+=(
    "$build/leanos-${version}-x86_64-multivcpu-rejection.iso"
    "$build/leanos-multivcpu-rejection.elf"
  )
fi
if [[ "$evidence_tier" == all ]]; then
  sha256sum "$build/leanos-${version}-x86_64.iso" \
  "$build/leanos-${version}-x86_64-multivcpu-rejection.iso" \
  "$build/leanos-multivcpu-rejection.elf" \
  "$build/leanos-${version}-x86_64-assigned-edu.iso" \
  "$build/leanos-assigned-edu.elf" \
  "$build/leanos-assigned-edu.map" \
  "$build/boot-page-plan-assigned-edu.final.h" \
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
else
  if selected_final_enabled "$build/leanos-assigned-edu.elf"; then
    selected_checksum_paths+=(
      "$build/leanos-${version}-x86_64-assigned-edu.iso"
      "$build/leanos-assigned-edu.elf"
      "$build/leanos-assigned-edu.map"
      "$build/boot-page-plan-assigned-edu.final.h"
    )
  fi
  ((${#selected_checksum_paths[@]} > 0)) || {
    echo "error: selected evidence produced no checksum inputs" >&2
    exit 1
  }
  printf '%s\0' "${selected_checksum_paths[@]}" | sort -zu | \
    xargs -0 sha256sum > "$build/SHA256SUMS"
fi
if [[ "$graph_make_cache_current" != true ]]; then
  graph_make_manifest_tmp="${graph_make_cache_manifest}.tmp"
  find "$build" -maxdepth 1 -type f \
    \( -name '*.o' -o -name '*.o.d' -o -name '*.elf' -o -name '*.map' \) \
    -print0 | sort -z | xargs -0 -r sha256sum > "$graph_make_manifest_tmp"
  [[ -s "$graph_make_manifest_tmp" ]] || {
    echo "error: generated Make output manifest is empty" >&2
    exit 1
  }
  mv "$graph_make_manifest_tmp" "$graph_make_cache_manifest"
  current_graph_make_signature="$(
    compute_graph_make_input_signature "$current_graph_signature"
  )"
  printf '%s\n' "$current_graph_make_signature" > \
    "$graph_make_cache_signature"
fi

printf '%s\n' "$current_kernel_source_signature" > "$kernel_source_signature"
record_build_phase manifests-and-completion
echo "built build/boot/leanos-${version}-x86_64.iso at $source_revision"
echo "symbols: build/boot/leanos.map; debug ELF: build/boot/leanos.elf"
