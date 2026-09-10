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
bootstrap_timing_file=""
bootstrap_phase_started_at="$build_profile_started_at"
if [[ -n "${LEANOS_BUILD_TIMING_FILE:-}" ]]; then
  bootstrap_timing_file="${LEANOS_BUILD_TIMING_FILE%.tsv}-bootstrap.tsv"
  printf 'phase\tphase_seconds\ttotal_seconds\tmode\n' > "$bootstrap_timing_file"
fi
record_bootstrap_phase() {
  local phase="$1"
  local mode="${2:-measured}"
  local now="$SECONDS"
  local phase_seconds="$((now - bootstrap_phase_started_at))"
  local total_seconds="$((now - build_profile_started_at))"
  printf 'build-bootstrap\t%s\tphase_seconds=%s\ttotal_seconds=%s\tmode=%s\n' \
    "$phase" "$phase_seconds" "$total_seconds" "$mode"
  if [[ -n "$bootstrap_timing_file" ]]; then
    printf '%s\t%s\t%s\t%s\n' "$phase" "$phase_seconds" "$total_seconds" "$mode" \
      >> "$bootstrap_timing_file"
  fi
  bootstrap_phase_started_at="$now"
}
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
  local evidence_build_plan="$3"
  local compiler_path
  local linker_path
  compiler_path="$(command -v -- "$compiler")"
  linker_path="$(command -v -- ld)"
  {
    # The generated graph describes every variant, while the build plan
    # selects the evidence tier and shard that must be present in this
    # checkout. Bind both so a warm PR-shard cache cannot satisfy a later
    # all-evidence request with a valid but partial object set.
    sha256sum "$object_graph" "$evidence_build_plan" \
      "$compiler_path" "$linker_path"
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
require_tool python3 "install Python 3"
toolchain_profile="${LEANOS_TOOLCHAIN_PROFILE:-gcc-reference}"
IFS=$'\t' read -r toolchain_profile toolchain_status toolchain_claim \
    lean_c_interface elf_layout_profile toolchain_manifest_sha256 \
    _profile_compiler _profile_compiler_version < <(
  ./scripts/toolchain-profile.py resolve \
    --profile "$toolchain_profile" --compiler "$cc" --format tsv
)
export LEANOS_TOOLCHAIN_PROFILE="$toolchain_profile"
export LEANOS_ELF_LAYOUT_PROFILE="$elf_layout_profile"
require_tool make "install Ubuntu package make=4.3-4.1build2"
require_tool sha256sum "install Ubuntu package coreutils=9.4-3ubuntu6.3"
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
  local status=0
  signature="$(compute_check_signature image-policy "$elf" \
    "$environment_name" "$environment_value")"
  if cached_check_is_current "$log" "$signature"; then
    return 0
  fi
  : > "$log"
  if [[ -n "$environment_name" ]]; then
    env "$environment_name=$environment_value" \
      ./scripts/check-image-policy.sh "$elf" >"$log" 2>&1 || status=$?
  else
    ./scripts/check-image-policy.sh "$elf" >"$log" 2>&1 || status=$?
  fi
  if ((status != 0)); then
    rm -f "${log}.inputs.sha256"
    return "$status"
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
  local layout_profile="$6"
  local -a arguments=()
  local raw_log="${log}.raw"
  local status=0
  local signature
  signature="$(compute_check_signature direct-port "$elf" "$manifest" \
    "$assigned_edu" "$layout_profile")"
  if cached_check_is_current "$log" "$signature"; then
    return 0
  fi
  [[ "$assigned_edu" != 1 ]] || arguments+=(--assigned-edu)
  arguments+=(--layout-profile "$layout_profile")
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
version="${LEANOS_VERSION:-0.1.0}"
source_revision="${LEANOS_SOURCE_REVISION:-$(git rev-parse HEAD)}"
matrix="${LEANOS_EVIDENCE_MATRIX:-scripts/emulator-evidence-matrix.tsv}"
if [[ "$matrix" == scripts/emulator-evidence-matrix.tsv ]]; then
  python3 scripts/generate-evidence-matrix.py --output "$matrix"
fi
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
# The packaged image family (ISO, GRUB configuration, and final-ELF policy per
# final ELF) and the page-plan stub set come from scripts/scenario-manifest.json;
# nothing below names one by hand.
# Check complete query results before building or selecting policy work. Bash
# process substitutions do not propagate a failed manifest producer.
query_build_manifest() {
  local rows
  rows="$(./scripts/scenario-manifest.py "$@")" || return "$?"
  [[ -n "$rows" ]] || {
    echo "error: scenario manifest query $1 returned no rows" >&2
    return 1
  }
  printf '%s\n' "$rows"
}
packaged_rows="$(query_build_manifest packaged-images --version "$version")"
mapfile -t packaged_images <<< "$packaged_rows"
page_plan_rows="$(query_build_manifest page-plans)"
mapfile -t page_plan_stubs <<< "$page_plan_rows"
disassembly_rows="$(query_build_manifest disassemblies)"
extended_state_rows="$(query_build_manifest extended-state-policies)"
entry_rows="$(query_build_manifest entry-policies)"
declare -A port_sites_lookup=()
while IFS=$'\t' read -r packaged_stem _ _ _ _ _ _ packaged_port_sites; do
  [[ "$packaged_port_sites" == - ]] || port_sites_lookup["$packaged_stem"]="$packaged_port_sites"
done < <(printf '%s\n' "${packaged_images[@]}")
if [[ ! "$source_revision" =~ ^[0-9a-f]{40}$ ]]; then
  echo "error: LEANOS_SOURCE_REVISION must be a full lowercase Git commit" >&2
  exit 1
fi
mkdir -p "$build"
./scripts/toolchain-profile.py resolve \
  --profile "$toolchain_profile" --compiler "$cc" \
  --output "$build/TOOLCHAIN_PROFILE.json"
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
while IFS=$'\t' read -r _ _ packaged_root _ _ _ _; do
  mkdir -p "$build/$packaged_root/boot/grub"
done < <(printf '%s\n' "${packaged_images[@]}")
current_lean_c_signature="$(compute_lean_c_signature "$repo_root")"
record_bootstrap_phase setup-and-signatures
LEANOS_ORACLE_TOOL_SIGNATURE="$current_lean_c_signature" \
  ./scripts/generate-oracle.sh "$build"
record_bootstrap_phase oracle-generation
ensure_boot_plan_stub() {
  [[ -f "$1" ]] || ./scripts/generate-boot-page-plan.sh --stub "$1"
}
for stub in "${page_plan_stubs[@]}"; do
  ensure_boot_plan_stub "$build/$stub"
done
record_bootstrap_phase boot-plan-stubs

# C generation resolves project imports through Lake's compiled module path.
# Build them here because image jobs and clean checkouts cannot rely on a
# previous proof-check job's workspace.
lake build
record_bootstrap_phase lake-build
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
  PrivilegeEntryControl J1900CpuProfile J1900MsrReadback BootTextConsole FaultDispatch DirectPortIO StaleTranslation
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
record_bootstrap_phase lean-c-cache-check
if ((reuse_lean_c == 0)); then
  lean_c_stage="$(mktemp -d "$build/.lean-c.XXXXXX")"
  trap 'rm -rf "$lean_c_stage"' EXIT
  for module in "${lean_c_modules[@]}"; do
    generate_lean_c "LeanOS/$module.lean" "$build/$module.c"
    record_bootstrap_phase "lean-c-$module" generated
  done
  printf '%s\n' "$current_lean_c_signature" > "$lean_c_signature"
  rm -rf "$lean_c_stage"
  trap - EXIT
else
  for module in "${lean_c_modules[@]}"; do
    record_bootstrap_phase "lean-c-$module" reused
  done
fi
record_bootstrap_phase complete
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
  printf 'toolchain-profile\t%s\n' "$toolchain_profile"
  printf 'toolchain-status\t%s\n' "$toolchain_status"
  printf 'toolchain-claim\t%s\n' "$toolchain_claim"
  printf 'toolchain-manifest-sha256\t%s\n' "$toolchain_manifest_sha256"
  printf 'lean-c-interface\t%s\n' "$lean_c_interface"
  printf 'direct-port-elf-normalization\t%s\n' "$elf_layout_profile"
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
current_graph_signature="$(
  compute_graph_signature \
    "$object_graph" "$cc" "$build/evidence-build-plan.tsv"
)"
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
      \( -name '*.c' -o -name 'composite-tokens.h' -o -name 'boundary-abi.h' -o \
      -name 'serial-protocol.h' -o \
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

# Validate the complete query before reading rows; a failing producer must not
# be hidden by process substitution or leave a partially accepted task list.
./scripts/scenario-manifest.py prelink-plans > "$build/prelink-plan-producers.tsv"
boot_plan_batch_args=()
while IFS=$'\t' read -r prelink header; do
  boot_plan_batch_args+=("$build/$prelink" "$build/$header")
done < "$build/prelink-plan-producers.tsv"
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
  ./scripts/scenario-manifest.py plan-comparisons > "$build/prelink-plan-comparisons.tsv"
  while IFS=$'\t' read -r expected actual; do
    cmp "$build/$expected" "$build/$actual" || {
      echo "error: shared page-table plan changed: $actual differs from $expected" >&2
      exit 1
    }
  done < "$build/prelink-plan-comparisons.tsv"
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

converge_selected_graph_plan() {
  local elf_path="$1"
  local expected_plan="$2"
  local final_plan="$3"
  local description="$4"
  shift 4
  local -a relink_targets=("$@")
  local converged=false
  local pass

  selected_final_enabled "$elf_path" || return 0
  ((${#relink_targets[@]} > 0)) || {
    echo "error: $description page-table convergence has no graph relink targets" >&2
    exit 1
  }
  for pass in 1 2 3 4; do
    ./scripts/generate-boot-page-plan.sh "$elf_path" "$final_plan"
    if cmp -s "$expected_plan" "$final_plan"; then
      converged=true
      break
    fi
    [[ "$pass" -lt 4 ]] || break

    # A generated common object can move the final image across a page
    # boundary even when this variant's kernel source did not change. Feed the
    # linker-resolved plan back through every selected graph-owned sibling that
    # shares this plan/header. Some evidence ELFs are copied or linked outside
    # the graph and must never be passed to this Makefile.
    cp "$final_plan" "$expected_plan"
    make -f "$object_graph" "${kernel_source_make_args[@]}" \
      -j "${LEANOS_BUILD_JOBS:-$(nproc)}" "${relink_targets[@]}"
  done
  [[ "$converged" == true ]] || {
    echo "error: $description page-table plan drifted after final link" >&2
    exit 1
  }
}

for spec in "${return_corruptions[@]}"; do
  IFS=: read -r fixture mode _reason <<<"$spec"
  return_elf="$build/leanos-return-${fixture}.elf"
  selected_final_enabled "$return_elf" || continue
  converge_selected_graph_plan "$return_elf" \
    "$build/boot-page-plan-return-${fixture}.h" \
    "$build/boot-page-plan-return-${fixture}.final.h" "$fixture" \
    "$return_elf"
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


# Final-ELF page-plan checks come from the scenario manifest in build order:
# a validate compares the linker-resolved plan with the expected header; a
# converge feeds the resolved plan back through the listed graph targets.
./scripts/scenario-manifest.py plan-checks --tier "$evidence_tier" > "$build/final-plan-checks.tsv"
while IFS=$'\t' read -r plan_image plan_check plan_expected plan_final plan_description plan_targets; do
  if [[ "$plan_check" == converge ]]; then
    plan_target_paths=()
    IFS=, read -ra plan_target_names <<<"$plan_targets"
    for plan_target in "${plan_target_names[@]}"; do
      plan_target_paths+=("$build/$plan_target.elf")
    done
    converge_selected_graph_plan "$build/$plan_image.elf" "$build/$plan_expected" \
      "$build/$plan_final" "$plan_description" "${plan_target_paths[@]}"
  else
    validate_selected_final_plan "$build/$plan_image.elf" "$build/$plan_expected" \
      "$build/$plan_final" "$plan_description"
  fi
done < "$build/final-plan-checks.tsv"
if selected_final_enabled "$build/leanos-double-fault.elf"; then
  ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
    -T boot/linker.ld -Map build/boot/leanos-double-fault.map \
    -o build/boot/leanos-double-fault.elf build/boot/boot.o \
    build/boot/kernel-double-fault.o build/boot/KernelTransition.o \
    build/boot/Syscall.o build/boot/IPCSyscall.o build/boot/Preemption.o \
    build/boot/BootAllocation.o build/boot/Interrupt.o build/boot/InterruptEntry.o \
    build/boot/BlockingIPC.o build/boot/CapabilityReuse.o build/boot/ExtendedState.o build/boot/PrivilegeEntryControl.o build/boot/J1900CpuProfile.o build/boot/J1900MsrReadback.o build/boot/BootTextConsole.o build/boot/FaultDispatch.o
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
    "$build/ExtendedState.o" "$build/PrivilegeEntryControl.o" "$build/J1900CpuProfile.o" "$build/J1900MsrReadback.o" "$build/BootTextConsole.o" "$build/FaultDispatch.o"
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
    build/boot/BlockingIPC.o build/boot/CapabilityReuse.o build/boot/ExtendedState.o build/boot/PrivilegeEntryControl.o build/boot/J1900CpuProfile.o build/boot/J1900MsrReadback.o build/boot/BootTextConsole.o build/boot/FaultDispatch.o
  ./scripts/generate-boot-page-plan.sh "$build/leanos-double-fault-guard-mapped.elf" \
    "$build/boot-page-plan-guard.final.h"
  cmp "$build/boot-page-plan-guard.h" "$build/boot-page-plan-guard.final.h" || {
    echo "error: guard-mapped boot page-table plan drifted after final link" >&2
    exit 1
  }
fi

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

while IFS=$'\t' read -r packaged_stem _ _ _ policy_key policy_env_name policy_env_value _; do
  [[ "$policy_key" != - ]] || continue
  if [[ "$policy_env_name" != - ]]; then
    queue_image_policy "$policy_key" "$build/$packaged_stem.elf" \
      "$policy_env_name" "$policy_env_value"
  else
    queue_image_policy "$policy_key" "$build/$packaged_stem.elf"
  fi
done < <(printf '%s\n' "${packaged_images[@]}")

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
if selected_final_enabled "$build/leanos-capability-transfer.elf"; then
  ./scripts/test-capability-transfer-machine.sh \
    "$build/leanos-capability-transfer.elf"
fi
if selected_final_enabled "$build/leanos-inflight-revocation.elf"; then
  ./scripts/test-inflight-revocation-machine.sh \
    "$build/leanos-inflight-revocation.elf"
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
  LEANOS_SERIAL_PROTOCOL_TSV="$build/serial-protocol.tsv" \
  ./scripts/check-early-probe-policy.py "$build/leanos-bootstrap32-ud.elf" \
    bootstrap32-ud | tee "$build/bootstrap32-ud-early-probe-policy.txt"
fi
if selected_final_enabled "$build/leanos-bootstrap64-nmi.elf"; then
  LEANOS_SERIAL_PROTOCOL_TSV="$build/serial-protocol.tsv" \
  ./scripts/check-early-probe-policy.py "$build/leanos-bootstrap64-nmi.elf" \
    bootstrap64-nmi | tee "$build/bootstrap64-nmi-early-probe-policy.txt"
fi
write_selected_disassembly() {
  local elf="$1"
  local output="$2"
  selected_final_enabled "$elf" || return 0
  objdump -d --no-show-raw-insn "$elf" > "$output"
}
while IFS=$'\t' read -r disassembly_image disassembly_output; do
  write_selected_disassembly "$build/$disassembly_image.elf" \
    "$build/$disassembly_output"
done <<< "$disassembly_rows"
run_selected_extended_state_policy() {
  local variant="$1"
  local elf="$2"
  local report="$3"
  selected_final_enabled "$elf" || return 0
  ./scripts/check-extended-state-policy.sh "$elf" "$variant" | tee "$report"
}
extended_state_policy_images=()
while IFS=$'\t' read -r policy_image policy_variant policy_report; do
  run_selected_extended_state_policy "$policy_variant" \
    "$build/$policy_image.elf" "$build/$policy_report"
  extended_state_policy_images+=("$build/$policy_image.elf")
done <<< "$extended_state_rows"
if [[ "$evidence_tier" == all ]]; then
  ./scripts/test-extended-state-policy.sh "${extended_state_policy_images[@]}"
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
while IFS=$'\t' read -r entry_image entry_key entry_report entry_env_name entry_env_value; do
  if [[ "$entry_env_name" != - ]]; then
    queue_entry_policy "$entry_key" "$build/$entry_image.elf" \
      "$build/$entry_report" "$entry_env_name" "$entry_env_value"
  else
    queue_entry_policy "$entry_key" "$build/$entry_image.elf" \
      "$build/$entry_report"
  fi
done <<< "$entry_rows"


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
  # The multi-vCPU evidence identity is a late alias of the canonical ELF.
  # Policy checks run before ISO packaging creates that alias, so check the
  # reviewed canonical binary that the build plan and guest both use.
  if [[ "$elf_name" == leanos-multivcpu-rejection.elf ]]; then
    elf_path="$build/leanos.elf"
  fi
  if [[ "$evidence_tier" != all &&
      -z "${selected_final_lookup[$elf_path]:-}" ]]; then
    continue
  fi
  if [[ "$evidence_tier" != all &&
      -n "${direct_port_seen[$elf_path]:-}" ]]; then
    continue
  fi
  direct_port_seen["$elf_path"]=1
  manifest="scripts/${port_sites_lookup[${elf_name%.elf}]:-direct-port-sites.tsv}"
  direct_port_args=()
  if [[ "$elf_name" == leanos-assigned-edu.elf ]]; then
    direct_port_args+=(--assigned-edu)
  fi
  direct_port_log="$direct_port_log_dir/$elf_name.log"
  direct_port_logs+=("$direct_port_log")
  assigned_edu=0
  ((${#direct_port_args[@]} == 0)) || assigned_edu=1
  printf '%s\0%s\0%s\0%s\0%s\0%s\0' "$elf_name" "$elf_path" \
    "$manifest" "$assigned_edu" "$direct_port_log" "$elf_layout_profile" \
    >> "$direct_port_task_file"
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
if ! xargs -0 -r -n 6 -P "$policy_jobs" bash -c \
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
    "scripts/${port_sites_lookup[leanos-entry-adversarial]}" \
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
  cp "$build/TOOLCHAIN_PROFILE.json" \
    "$staging_root/boot/TOOLCHAIN_PROFILE.json"
}
while IFS=$'\t' read -r packaged_stem _ packaged_root packaged_grub _ _ _; do
  stage_selected_image "$build/$packaged_stem.elf" "$build/$packaged_root" \
    "$packaged_grub"
done < <(printf '%s\n' "${packaged_images[@]}")
for spec in "${return_corruptions[@]}"; do
  IFS=: read -r fixture _mode _reason <<<"$spec"
  fixture_root="$build/iso-return-${fixture}"
  return_elf="$build/leanos-return-${fixture}.elf"
  selected_final_enabled "$return_elf" || continue
  mkdir -p "$fixture_root/boot/grub"
  cp "$return_elf" "$fixture_root/boot/leanos.elf"
  cp boot/grub.cfg "$fixture_root/boot/grub/grub.cfg"
  cp "$build/SOURCE_REVISION" "$fixture_root/boot/SOURCE_REVISION"
  cp "$build/TOOLCHAIN_PROFILE.json" \
    "$fixture_root/boot/TOOLCHAIN_PROFILE.json"
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
while IFS=$'\t' read -r _ packaged_iso packaged_root _ _ _ _; do
  queue_iso "$build/$packaged_iso" "$build/$packaged_root"
done < <(printf '%s\n' "${packaged_images[@]}")
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
# Hash the artifacts selected by the manifest-driven packaging queue for both
# full builds and shards. Never maintain a second full-build filename list.
selected_checksum_paths+=("$build/TOOLCHAIN_PROFILE.json")
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
if [[ -n "${LEANOS_BUILD_TIMING_FILE:-}" ]]; then
  ./scripts/check-build-timing.py "$LEANOS_BUILD_TIMING_FILE"
fi
echo "built build/boot/leanos-${version}-x86_64.iso at $source_revision"
echo "symbols: build/boot/leanos.map; debug ELF: build/boot/leanos.elf"
