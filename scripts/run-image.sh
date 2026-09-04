#!/usr/bin/env bash
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$repo_root"
serial_protocol="${LEANOS_SERIAL_PROTOCOL:-$(dirname "${LEANOS_ORACLE_CORPUS:-build/boot/corpus.tsv}")/serial-protocol.sh}"
# shellcheck source=/dev/null
source "$serial_protocol"
export LEANOS_SERIAL_PROTOCOL_TSV="${serial_protocol%.sh}.tsv"
source "$repo_root/scripts/q35-platform.sh"
qemu="${LEANOS_QEMU:-qemu-system-x86_64}"
limit="${LEANOS_QEMU_TIMEOUT_SECONDS:-30}"
version="${LEANOS_VERSION:-0.1.0}"
scenario="${LEANOS_BOOT_SCENARIO:-blocking-ipc}"
fault_scenario=0
stale_translation_scenario=0
extended_instruction=x87
extended_vector=7
if [[ "$scenario" == fast-entry-syscall ]]; then
  extended_instruction=syscall
  extended_vector=6
  default_image="build/boot/leanos-${version}-x86_64-fast-entry-syscall.iso"
elif [[ "$scenario" == fast-entry-sysenter ]]; then
  extended_instruction=sysenter
  extended_vector=6
  default_image="build/boot/leanos-${version}-x86_64-fast-entry-sysenter.iso"
elif [[ "$scenario" == extended-state-avx ]]; then
  extended_instruction=avx
  extended_vector=6
  default_image="build/boot/leanos-${version}-x86_64-extended-state-avx.iso"
elif [[ "$scenario" == extended-state-sse2 ]]; then
  extended_instruction=sse2
  extended_vector=6
  default_image="build/boot/leanos-${version}-x86_64-extended-state-sse2.iso"
elif [[ "$scenario" == extended-state-sse ]]; then
  extended_instruction=sse
  extended_vector=6
  default_image="build/boot/leanos-${version}-x86_64-extended-state-sse.iso"
elif [[ "$scenario" == extended-state-mmx ]]; then
  extended_instruction=mmx
  default_image="build/boot/leanos-${version}-x86_64-extended-state-mmx.iso"
elif [[ "$scenario" == extended-state ]]; then
  default_image="build/boot/leanos-${version}-x86_64-extended-state.iso"
elif [[ "$scenario" == preemption ]]; then
  default_image="build/boot/leanos-${version}-x86_64-preemption.iso"
elif [[ "$scenario" == stale-translation-denial ]]; then
  stale_translation_scenario=1
  default_image="build/boot/leanos-${version}-x86_64-fault-stale-translation.iso"
  stale_translation_elf="build/boot/leanos-fault-stale-translation.elf"
elif [[ "$scenario" == frame-budget ]]; then
  default_image="build/boot/leanos-${version}-x86_64-frame-budget.iso"
elif [[ "$scenario" == capability-transfer ]]; then
  default_image="build/boot/leanos-${version}-x86_64-capability-transfer.iso"
elif [[ "$scenario" == inflight-revocation ]]; then
  default_image="build/boot/leanos-${version}-x86_64-inflight-revocation.iso"
elif [[ "$scenario" == fault-containment ]]; then
  fault_scenario=1
  fault_probe=supervisor-read
  default_image="build/boot/leanos-${version}-x86_64-fault-containment.iso"
elif [[ "$scenario" == fault-readonly-write ]]; then
  fault_scenario=1
  fault_probe=readonly-write
  default_image="build/boot/leanos-${version}-x86_64-fault-readonly-write.iso"
elif [[ "$scenario" == fault-nx-execute ]]; then
  fault_scenario=1
  fault_probe=nx-execute
  default_image="build/boot/leanos-${version}-x86_64-fault-nx-execute.iso"
elif [[ "$scenario" == entry-adversarial ]]; then
  default_image="build/boot/leanos-${version}-x86_64-entry-adversarial.iso"
elif [[ "$scenario" == direct-port-serial ]]; then
  direct_port_probe_name=serial-out; direct_port_port=1016; direct_port_dir=out
  default_image="build/boot/leanos-${version}-x86_64-direct-port-serial.iso"
elif [[ "$scenario" == direct-port-debug ]]; then
  direct_port_probe_name=debug-exit; direct_port_port=244; direct_port_dir=out
  default_image="build/boot/leanos-${version}-x86_64-direct-port-debug.iso"
elif [[ "$scenario" == direct-port-in ]]; then
  direct_port_probe_name=serial-in; direct_port_port=1021; direct_port_dir=in
  default_image="build/boot/leanos-${version}-x86_64-direct-port-in.iso"
elif [[ "$scenario" == direct-port-pic ]]; then
  direct_port_probe_name=pic-mask; direct_port_port=33; direct_port_dir=out
  default_image="build/boot/leanos-${version}-x86_64-direct-port-pic.iso"
elif [[ "$scenario" == divide-error ]]; then
  integer_fault_kind=divide-error; integer_fault_vector=0
  integer_fault_saved_rip=faulting-instruction; integer_fault_upper=DIVIDE-ERROR
  default_image="build/boot/leanos-${version}-x86_64-divide-error.iso"
elif [[ "$scenario" == breakpoint ]]; then
  integer_fault_kind=breakpoint; integer_fault_vector=3
  integer_fault_saved_rip=post-instruction; integer_fault_upper=BREAKPOINT
  default_image="build/boot/leanos-${version}-x86_64-breakpoint.iso"
else
  default_image="build/boot/leanos-${version}-x86_64.iso"
fi
image="${1:-$default_image}"
log="${LEANOS_SERIAL_LOG:-build/boot/serial.log}"
dma_snapshot="${LEANOS_DMA_SNAPSHOT:-build/boot/dma-quarantine-snapshot-${scenario}.tsv}"
vtd_snapshot="${LEANOS_VTD_SNAPSHOT:-build/boot/vtd-activation-snapshot-${scenario}.tsv}"
source_revision_file="${LEANOS_SOURCE_REVISION_FILE:-build/boot/SOURCE_REVISION}"
high_water_artifact="${LEANOS_ENTRY_HIGH_WATER_ARTIFACT:-build/boot/entry-stack-high-water-${scenario}.txt}"
fault_snapshot_artifact="${LEANOS_FAULT_SNAPSHOT_ARTIFACT:-build/boot/${scenario}-snapshot.txt}"
fault_elf="${LEANOS_FAULT_CONTAINMENT_ELF:-${stale_translation_elf:-build/boot/leanos-${scenario}.elf}}"
memory_mib="${LEANOS_QEMU_MEMORY_MIB:-128}"
for tool in "$qemu" timeout; do command -v "$tool" >/dev/null 2>&1 || { echo "error: missing required tool '$tool'; install qemu-system-x86=1:8.2.2+ds-0ubuntu1.18 and coreutils=9.4-3ubuntu6.2" >&2; exit 1; }; done
[[ "$limit" =~ ^[1-9][0-9]*$ ]] || { echo "error: timeout must be a positive integer" >&2; exit 1; }
[[ "$memory_mib" =~ ^(64|128)$ ]] || { echo "error: memory must be one of the checked configurations: 64 or 128 MiB" >&2; exit 1; }
reported_top_mib=$((memory_mib - 1))
[[ -f "$image" ]] || { echo "error: image '$image' not found; run ./scripts/build-image.sh first" >&2; exit 1; }
if (( fault_scenario || stale_translation_scenario )); then
  [[ -f "$fault_elf" ]] || {
    echo "error: fault final ELF '$fault_elf' not found; run ./scripts/build-image.sh first" >&2
    exit 1
  }
  symbol_value() {
    local symbol="$1" address
    address="$(nm -n "$fault_elf" | awk -v wanted="$symbol" '$3 == wanted { print $1 }')"
    [[ "$address" =~ ^[[:xdigit:]]+$ ]] || return 1
    printf '%u' "$((16#$address))"
  }
fi
if (( fault_scenario )); then
  fault_cr3="$(symbol_value page_map_level_4_a)" &&
    fault_rsp="$(symbol_value user_a_stack_top)" || {
    echo "error: required fault final-ELF symbol missing" >&2
    exit 1
  }
  if [[ "$fault_probe" == nx-execute ]]; then
    fault_error=21
    fault_access=execute
    fault_access_code=2
    fault_rip_label=user-a-nx-fault-instruction
    fault_rip="$(symbol_value user_a_nx_fault_instruction)"
    fault_address="$fault_rip"
    fault_page=$((fault_address / 4096))
    printf -v fault_leaf '%u' \
      "$(( (1 << 63) + fault_page * 4096 + 7 ))"
    fault_cause=no-execute
    fault_canary=' payload-canary=armed'
  elif [[ "$fault_probe" == readonly-write ]]; then
    fault_error=7
    fault_access=write
    fault_access_code=1
    fault_rip_label=user-a-write-fault-instruction
    fault_rip="$(symbol_value user_a_write_fault_instruction)"
    fault_address="$(symbol_value user_a_write_target)"
    fault_page=$((fault_address / 4096))
    fault_leaf=$((fault_page * 4096 + 5))
    fault_cause=not-writable
    fault_canary=' write-canary=unchanged'
  else
    fault_error=5
    fault_access=read
    fault_access_code=0
    fault_rip_label=user-a-fault-instruction
    fault_rip="$(symbol_value user_a_fault_instruction)"
    fault_address=0
    fault_page=0
    fault_leaf=9223372036854775811
    fault_cause=supervisor
    fault_canary=
  fi
elif (( stale_translation_scenario )); then
  stale_translation_cr3="$(symbol_value page_map_level_4_b)" &&
    stale_translation_rip="$(
      symbol_value user_b_stale_translation_fault_instruction
    )" &&
    stale_translation_rsp="$(symbol_value user_b_stack_top)" || {
    echo "error: required stale-translation final-ELF symbol missing" >&2
    exit 1
  }
fi
mkdir -p "$(dirname "$log")"; : > "$log"
command=()
leanos_q35_command command "$qemu" "$memory_mib" "$log" "$image"
qemu_version="$($qemu --version 2>&1 | head -n 1 || true)"
printf 'QEMU version: %s\nQEMU command:' "${qemu_version:-unknown}" >&2; printf ' %q' "${command[@]}" >&2; printf '\nSerial log: %s\n' "$log" >&2
set +e; timeout --signal=TERM --kill-after=2s "${limit}s" "${command[@]}"; status=$?; set -e
expected="$(mktemp)"; without_allocation="$(mktemp)"
trap 'rm -f "$expected" "$without_allocation"' EXIT
corpus="${LEANOS_ORACLE_CORPUS:-build/boot/corpus.tsv}"
[[ -f "$corpus" ]] || { echo "error: oracle corpus '$corpus' not found" >&2; exit 1; }
# The expected transcript is rendered from the scenario's template through the
# shared renderer, after the runner has learned the values it substitutes.
source "$repo_root/scripts/expectation-template.sh"
if [[ "$scenario" == frame-budget ]]; then
  frame_budget_boot_physical="$(
    sed -n "s|^${LEANOS_SERIAL_7_ALLOC} frame=\\([0-9][0-9]*\\) .*|\\1|p" "$log"
  )"
  frame_budget_physical="$(
    sed -n "s|^${LEANOS_SERIAL_20_FRAME} physical-frame=\\([0-9][0-9]*\\) .*|\\1|p" "$log"
  )"
  [[ "$frame_budget_boot_physical" =~ ^[0-9]+$ &&
     "$frame_budget_physical" =~ ^[0-9]+$ ]] || {
    echo "failure_class=serial-protocol: missing unique boot/scenario physical-frame binding" >&2
    exit 1
  }
  if [[ "$frame_budget_physical" == "$frame_budget_boot_physical" ]]; then
    echo "failure_class=serial-protocol: frame-budget scenario double-published live boot frame" >&2
    exit 1
  fi
fi
expectation_template="scripts/expectations/${scenario}.transcript"
[[ -f "$expectation_template" ]] || {
  echo "failure_class=runner-template: no expectation template for scenario $scenario" >&2
  exit 1
}
render_expectation "$expectation_template" > "$expected"
if [[ $status -eq 124 || $status -eq 137 ]]; then echo "failure_class=timeout: QEMU exceeded ${limit}s wall limit" >&2; exit 1; fi
if [[ $status -eq 35 ]]; then echo "failure_class=guest-error: guest emitted failure signal" >&2; exit 1; fi
if [[ $status -ne 33 ]]; then echo "failure_class=qemu-error: QEMU exit status $status (expected 33)" >&2; exit 1; fi
allocation_trace="$(awk "/^$(leanos_serial_family_re 7) /" "$log")"
mapfile -t allocation_lines <<<"$allocation_trace"
if [[ ${#allocation_lines[@]} -ne 6 ]] ||
   [[ ! "${allocation_lines[0]}" =~ ^${LEANOS_SERIAL_7_HANDOFF}\ magic=valid\ info-bytes=[1-9][0-9]*\ mmap-entries=[1-9][0-9]*\ result=PASS$ ]] ||
   [[ "${allocation_lines[1]}" != "${LEANOS_SERIAL_7_MAP} boot-pages=4096 reported-top-mib=${reported_top_mib} precedence=reserved result=PASS" ]] ||
   [[ ! "${allocation_lines[2]}" =~ ^${LEANOS_SERIAL_7_ALLOC}\ frame=[0-9]+\ firmware-usable=1\ boot-accessible=1\ reserved=0\ projection=scalar-checked\ result=PASS$ ]] ||
   [[ "${allocation_lines[3]}" != "${LEANOS_SERIAL_7_SCRUB} bytes=4096 zero=1 result=PASS" ]] ||
   [[ "${allocation_lines[4]}" != "${LEANOS_SERIAL_7_PUBLISH} object=1 owner=1 stale-object=denied result=PASS" ]] ||
   [[ "${allocation_lines[5]}" != "${LEANOS_SERIAL_7_BOOTALLOC} status=PASS" ]]; then
  echo "failure_class=boot-allocation-trace: exact ordered allocation protocol not observed" >&2
  exit 1
fi
mapfile -t paging_fixtures < <(grep "^${LEANOS_SERIAL_8_PAGING} fixture=" "$log")
paging_specs=(
  'flip-present B pt' 'flip-user B pt' 'flip-writable B pt'
  'flip-nx B pt' 'wrong-frame B pt' 'ancestor-pointer B pml4'
  'ancestor-flags B pdpt' 'swapped-user-leaves B pt'
  'extra-mapping B pt' 'nmi-guard-mapping B pt' 'entry-guard-mapping B pt'
  'omitted-mapping B pt' 'mmio-wrong-frame B pt' 'mmio-flip-user B pt'
  'mutable-wrong-frame B pt'
  'mutable-publish-before-invalidation B pt' 'mutable-unknown-state B pt'
  'wrong-cr3 A cr3'
)
if [[ ${#paging_fixtures[@]} -ne ${#paging_specs[@]} ]]; then
  echo "failure_class=page-table-fixtures: complete live-mutation matrix not observed" >&2
  exit 1
fi
for ((i = 0; i < ${#paging_specs[@]}; ++i)); do
  read -r name root_name level <<< "${paging_specs[i]}"
  if [[ ! "${paging_fixtures[i]}" =~ ^${LEANOS_SERIAL_8_PAGING}\ fixture=${name}\ root=${root_name}\ level=${level}\ page=[0-9]+\ expected=[0-9]+\ actual=[0-9]+\ result=REJECTED$ ]]; then
    echo "failure_class=page-table-fixtures: invalid or reordered fixture '${paging_fixtures[i]}'" >&2
    exit 1
  fi
done
vtd_trace="$(awk "/^$(leanos_serial_family_re 21) /" "$log")"
mapfile -t vtd_lines <<<"$vtd_trace"
vtd_root_frame=0
vtd_context_frame=0
if [[ ${#vtd_lines[@]} -ne 4 ]] ||
   [[ "${vtd_lines[0]}" != "${LEANOS_SERIAL_21_VTD} unit=0 mmio=4275634176 version=16 cap=59110346977575430 ecap=3842 gsts=0 fsts=0 rtaddr=0 stage=pre-activation result=PASS" ]]; then
  echo "failure_class=vtd-evidence: exact quiescent VT-d unit evidence not observed" >&2
  exit 1
fi
if [[ "${vtd_lines[1]}" =~ ^${LEANOS_SERIAL_21_VTD_PLAN}\ root-frame=([1-9][0-9]*)\ context-frame=([1-9][0-9]*)\ root-words=512\ context-words=512\ present-root-entries=1\ present-context-entries=0\ translation=disabled\ deny-all=1\ result=PASS$ ]]; then
  vtd_root_frame="${BASH_REMATCH[1]}"
  vtd_context_frame="${BASH_REMATCH[2]}"
else
  echo "failure_class=vtd-evidence: exact deny-all VT-d plan evidence not observed" >&2
  exit 1
fi
if [[ "$vtd_context_frame" -ne $((vtd_root_frame + 1)) ]] ||
   [[ "${vtd_lines[2]}" != "${LEANOS_SERIAL_21_VTD_TABLES} root-frame=${vtd_root_frame} context-frame=${vtd_context_frame} scrub=verified construct=verified root-words=512 context-words=512 result=PASS" ]] ||
   [[ "${vtd_lines[3]}" != "${LEANOS_SERIAL_21_VTD_ACTIVATE} order=validate,scrub,construct,publish,invalidate-context,invalidate-iotlb,enable,verify journal=2271560481 gsts=3221225472 fsts=0 rtaddr=$((vtd_root_frame * 4096)) generated-result=0 stage=pre-cpl3 result=PASS" ]]; then
  echo "failure_class=vtd-evidence: exact fail-closed VT-d activation evidence not observed" >&2
  exit 1
fi
sed -e "/^$(leanos_serial_family_re 7) /d" -e "/^$(leanos_serial_re 8 PAGING) fixture=/d" \
  -e "/^$(leanos_serial_re 15 DMA-FUNCTION) /d" -e "/^$(leanos_serial_family_re 21) /d" \
  "$log" > "$without_allocation"
if (( fault_scenario )); then
  mkdir -p "$(dirname "$fault_snapshot_artifact")"
  grep "^${LEANOS_SERIAL_14_PF_SNAPSHOT} " "$log" > "$fault_snapshot_artifact" || {
    echo "failure_class=page-fault-snapshot: canonical snapshot missing" >&2
    exit 1
  }
  mapfile -t fault_snapshot_lines < "$fault_snapshot_artifact"
  if [[ ${#fault_snapshot_lines[@]} -ne 1 ]]; then
    echo "failure_class=page-fault-snapshot: snapshot missing or duplicated" >&2
    exit 1
  fi
  snapshot_line="${fault_snapshot_lines[0]}"
  if [[ ! "$snapshot_line" =~ ^${LEANOS_SERIAL_14_PF_SNAPSHOT}\ codec=1\ width=19\ words=([0-9]+(,[0-9]+){18})\ authorization=1\ route=72057598316249602\ result=PASS$ ]]; then
    echo "failure_class=page-fault-snapshot: malformed codec or generated replay result" >&2
    exit 1
  fi
  IFS=, read -r -a snapshot_words <<< "${BASH_REMATCH[1]}"
  expected_snapshot_words=(
    1 14 "$fault_error" "$fault_address" "$fault_page"
    "$fault_access_code"
    1 1 1 1 "$fault_cr3" 15 "$fault_rip"
    35 534 "$fault_rsp" 27 1 0
  )
  for ((i = 0; i < 19; ++i)); do
    if [[ "${snapshot_words[i]}" != "${expected_snapshot_words[i]}" ]]; then
      echo "failure_class=page-fault-snapshot: word $i disagrees with canonical production snapshot" >&2
      exit 1
    fi
  done
  snapshot_line_number="$(grep -n "^${LEANOS_SERIAL_14_PF_SNAPSHOT} " "$log" | cut -d: -f1 || true)"
  entry_line_number="$(grep -n "^${LEANOS_SERIAL_14_FAULT_ENTRY} " "$log" | cut -d: -f1 || true)"
  if [[ "$entry_line_number" =~ ^[0-9]+$ &&
        "$snapshot_line_number" -ge "$entry_line_number" ]]; then
    echo "failure_class=page-fault-snapshot: snapshot/replay record reordered" >&2
    exit 1
  fi
  sed -i "/^$(leanos_serial_re 14 PF-SNAPSHOT) /d" "$without_allocation"
fi
if [[ "$scenario" == blocking-ipc || "$scenario" == preemption ]]; then
  final_high_water_path="syscall"
  [[ "$scenario" == preemption ]] && final_high_water_path="timer-context-switch"
  mkdir -p "$(dirname "$high_water_artifact")"
  grep "^${LEANOS_SERIAL_11_ENTRY_HIGH_WATER} " "$log" > "$high_water_artifact" || {
    echo "failure_class=entry-stack-high-water: observation missing" >&2; exit 1;
  }
  mapfile -t high_water_lines < "$high_water_artifact"
  if [[ ${#high_water_lines[@]} -ne 2 ]]; then
    echo "failure_class=entry-stack-high-water: missing or duplicate observation" >&2
    exit 1
  fi
  expected_high_water_paths=(user-page-fault "$final_high_water_path")
  for ((i = 0; i < 2; ++i)); do
    if [[ ! "${high_water_lines[i]}" =~ ^${LEANOS_SERIAL_11_ENTRY_HIGH_WATER}\ path=${expected_high_water_paths[i]}\ observed-bytes=([0-9]+)\ usable-bytes=16384\ margin-bytes=([0-9]+)\ authority=diagnostic\ result=PASS$ ]]; then
      echo "failure_class=entry-stack-high-water: malformed or reordered observation" >&2
      exit 1
    fi
    observed="${BASH_REMATCH[1]}"; margin="${BASH_REMATCH[2]}"
    if (( observed < 176 || observed + margin != 16384 || margin < 4096 )); then
      echo "failure_class=entry-stack-high-water: invalid observed bound" >&2
      exit 1
    fi
  done
  sed -i "/^$(leanos_serial_re 11 ENTRY-HIGH-WATER) /d" "$without_allocation"
fi
# Retain the composed expectation when asked, so the per-scenario transcript
# templates can be checked against exactly what this runner expected.
if [[ -n "${LEANOS_DUMP_EXPECTED_DIR:-}" ]]; then
  mkdir -p "$LEANOS_DUMP_EXPECTED_DIR"
  cp "$expected" "$LEANOS_DUMP_EXPECTED_DIR/$scenario.expected"
fi
if ! cmp -s "$expected" "$without_allocation"; then echo "failure_class=serial-protocol: complete expected protocol not observed" >&2; diff -u "$expected" "$without_allocation" >&2 || true; exit 1; fi
if ! ./scripts/write-dma-snapshot.py \
    --serial-log "$log" \
    --source-revision "$source_revision_file" \
    --qemu-version "${qemu_version:-unknown}" \
    --output "$dma_snapshot"; then
  echo "failure_class=dma-snapshot: canonical per-function snapshot rejected" >&2
  exit 1
fi
if ! ./scripts/write-vtd-snapshot.py \
    --serial-log "$log" \
    --source-revision "$source_revision_file" \
    --qemu-version "${qemu_version:-unknown}" \
    --output "$vtd_snapshot"; then
  echo "failure_class=vtd-snapshot: canonical activation snapshot rejected" >&2
  exit 1
fi
if [[ "$scenario" == extended-state || "$scenario" == extended-state-mmx ||
      "$scenario" == extended-state-sse || "$scenario" == extended-state-sse2 ||
      "$scenario" == extended-state-avx ]]; then
  default_snapshot="build/boot/extended-state-control-snapshot.txt"
  if [[ "$extended_instruction" == mmx ]]; then
    default_snapshot="build/boot/extended-state-mmx-control-snapshot.txt"
  elif [[ "$extended_instruction" == sse ]]; then
    default_snapshot="build/boot/extended-state-sse-control-snapshot.txt"
  elif [[ "$extended_instruction" == sse2 ]]; then
    default_snapshot="build/boot/extended-state-sse2-control-snapshot.txt"
  elif [[ "$extended_instruction" == avx ]]; then
    default_snapshot="build/boot/extended-state-avx-control-snapshot.txt"
  fi
  snapshot="${LEANOS_EXTENDED_STATE_SNAPSHOT:-$default_snapshot}"
  mkdir -p "$(dirname "$snapshot")"
  grep -E '^LEANOS/(13 EXTENDED-STATE cpuid\.1\.|6 CONTROL )' "$log" > "$snapshot"
  [[ $(wc -l < "$snapshot") -eq 2 ]] || {
    echo "failure_class=extended-state-snapshot: decoded CPUID/control snapshot incomplete" >&2
    exit 1
  }
elif [[ "$scenario" == fast-entry-syscall || "$scenario" == fast-entry-sysenter ]]; then
  snapshot="${LEANOS_FAST_ENTRY_SNAPSHOT:-build/boot/fast-entry-control-snapshot-${extended_instruction}.txt}"
  mkdir -p "$(dirname "$snapshot")"
  grep -E '^LEANOS/(14 FAST-ENTRY cpu\.|13 EXTENDED-STATE cpuid\.1\.|6 CONTROL )' \
    "$log" > "$snapshot"
  [[ $(wc -l < "$snapshot") -eq 3 ]] || {
    echo "failure_class=fast-entry-snapshot: decoded CPUID/MSR/control snapshot incomplete" >&2
    exit 1
  }
fi
echo "LeanOS boot smoke test passed; guest success and complete protocol observed; serial log: $log"
