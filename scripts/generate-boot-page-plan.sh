#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

install_if_changed() {
  local staged="$1" destination="$2"
  if [[ -f "$destination" ]] && cmp -s "$staged" "$destination"; then
    rm "$staged"
  else
    mv "$staged" "$destination"
  fi
}

if [[ "${1:-}" == --stub ]]; then
  destination="${2:?usage: $0 --stub OUTPUT}"
  mkdir -p "$(dirname "$destination")"
  output="$(mktemp "${destination}.tmp.XXXXXX")"
  trap 'rm -f "$output"' EXIT
  {
    echo '/* Fixed-size prelink placeholder; replaced by the accepted Lean plan. */'
    echo 'static const unsigned long long leanos_boot_plan_a[4096] = {'
    for ((page = 0; page < 4096; ++page)); do
      echo "  (0x8000000000000003ULL + $((page * 4096))ULL),"
    done
    echo '};'
    echo 'static const unsigned long long leanos_boot_plan_b[4096] = {'
    for ((page = 0; page < 4096; ++page)); do
      echo "  (0x8000000000000013ULL + $((page * 4096))ULL),"
    done
    echo '};'
    # VT-d placeholder: the pinned register/topology constants are
    # layout-independent and final; only the linker-derived table values are
    # placeholders, chosen in the same immediate-encoding class as real ones.
    echo '#define LEANOS_VTD_MMIO_BASE 4275634176ULL'
    echo '#define LEANOS_VTD_PLAN_VERSION 1ULL'
    echo '#define LEANOS_VTD_EXPECTED_VERSION 16ULL'
    echo '#define LEANOS_VTD_EXPECTED_CAP 59110346977575430ULL'
    echo '#define LEANOS_VTD_EXPECTED_ECAP 3842ULL'
    echo '#define LEANOS_VTD_ENABLED_GSTS 3221225472ULL'
    echo '#define LEANOS_VTD_TOPOLOGY 281509336580098ULL'
    echo '#define LEANOS_VTD_ASSIGNED_TOPOLOGY 281509336580099ULL'
    echo '#define LEANOS_VTD_ROOT_TABLE_FRAME 1ULL'
    echo '#define LEANOS_VTD_CONTEXT_TABLE_FRAME 2ULL'
    echo '#define LEANOS_VTD_SECOND_LEVEL_ROOT_FRAME 3ULL'
    echo '#define LEANOS_VTD_SECOND_LEVEL_DIRECTORY_FRAME 4ULL'
    echo '#define LEANOS_VTD_SECOND_LEVEL_TABLE_FRAME 5ULL'
    echo '#define LEANOS_VTD_ASSIGNED_DEVICE 0ULL'
    echo '#define LEANOS_VTD_ASSIGNED_SOURCE 0ULL'
    echo '#define LEANOS_VTD_ASSIGNED_HANDLE 0ULL'
    echo '#define LEANOS_VTD_ASSIGNED_GENERATION 1ULL'
    echo '#define LEANOS_VTD_ASSIGNED_DOMAIN 0ULL'
    echo '#define LEANOS_VTD_ASSIGNED_DOMAIN_GENERATION 1ULL'
    echo '#define LEANOS_VTD_ASSIGNED_OWNER 0ULL'
    echo '#define LEANOS_VTD_ASSIGNED_REQUESTER 16ULL'
    echo '#define LEANOS_VTD_ASSIGNED_READ_BUFFER_FRAME 6ULL'
    echo '#define LEANOS_VTD_ASSIGNED_WRITE_BUFFER_FRAME 7ULL'
    echo '#define LEANOS_VTD_MODEL_READ_IOVA 0ULL'
    echo '#define LEANOS_VTD_MODEL_READ_MAPPING 0ULL'
    echo '#define LEANOS_VTD_MODEL_READ_MAPPING_GENERATION 1ULL'
    echo '#define LEANOS_VTD_HARDWARE_READ_IOVA 0ULL'
    echo '#define LEANOS_VTD_MODEL_READ_LENGTH 16ULL'
    echo '#define LEANOS_VTD_MODEL_READ_FRAME 0ULL'
    echo '#define LEANOS_VTD_MODEL_READ_FRAME_GENERATION 1ULL'
    echo '#define LEANOS_VTD_MODEL_READ_FRAME_OFFSET 0ULL'
    echo '#define LEANOS_VTD_MODEL_READ_PERMISSION 1ULL'
    echo '#define LEANOS_VTD_MODEL_WRITE_IOVA 16ULL'
    echo '#define LEANOS_VTD_MODEL_WRITE_LENGTH 16ULL'
    echo '#define LEANOS_VTD_MODEL_WRITE_FRAME 0ULL'
    echo '#define LEANOS_VTD_MODEL_WRITE_FRAME_GENERATION 1ULL'
    echo '#define LEANOS_VTD_MODEL_WRITE_FRAME_OFFSET 16ULL'
    echo '#define LEANOS_VTD_MODEL_WRITE_PERMISSION 2ULL'
    echo '#define LEANOS_VTD_ROOT_TABLE_ADDRESS 4096ULL'
    echo '#define LEANOS_VTD_CANONICAL_JOURNAL 2271560481ULL'
    echo 'static const unsigned long long leanos_vtd_root_table[512] = {'
    echo '  8193ULL,'
    for ((word = 1; word < 512; ++word)); do echo '  0ULL,'; done
    echo '};'
    echo 'static const unsigned long long leanos_vtd_context_table[512] = {'
    for ((word = 0; word < 512; ++word)); do echo '  0ULL,'; done
    echo '};'
    echo 'static const unsigned long long leanos_vtd_assigned_context_table[512] = {'
    for ((word = 0; word < 512; ++word)); do
      if ((word == 32)); then echo '  12289ULL,'
      elif ((word == 33)); then echo '  1ULL,'
      else echo '  0ULL,'; fi
    done
    echo '};'
    echo 'static const unsigned long long leanos_vtd_assigned_second_level_root[512] = {'
    echo '  16387ULL,'
    for ((word = 1; word < 512; ++word)); do echo '  0ULL,'; done
    echo '};'
    echo 'static const unsigned long long leanos_vtd_assigned_second_level_directory[512] = {'
    echo '  20483ULL,'
    for ((word = 1; word < 512; ++word)); do echo '  0ULL,'; done
    echo '};'
    echo 'static const unsigned long long leanos_vtd_assigned_second_level_table[512] = {'
    echo '  24577ULL,'
    echo '  28674ULL,'
    for ((word = 2; word < 512; ++word)); do echo '  0ULL,'; done
    echo '};'
  } > "$output"
  install_if_changed "$output" "$destination"
  trap - EXIT
  exit 0
fi

assigned_edu=0
if [[ "${1:-}" == --assigned-edu ]]; then
  assigned_edu=1
  shift
fi
elf="${1:?usage: $0 [--assigned-edu] ELF OUTPUT}"
destination="${2:?usage: $0 [--assigned-edu] ELF OUTPUT}"
mkdir -p "$(dirname "$destination")"
output="$(mktemp "${destination}.tmp.XXXXXX")"
trap 'rm -f "$output"' EXIT
[[ -f "$elf" ]] || { echo "error: missing prelinked ELF '$elf'" >&2; exit 1; }

# The image wrapper invokes this generator for every image variant. Avoid
# replaying both Lean executables when neither the ELF nor the generator/tool
# identity changed. The wrapper supplies the content signature it already
# computes over all Lean sources, Lake inputs, and the resolved Lean binary.
tool_signature="${LEANOS_BOOT_PLAN_TOOL_SIGNATURE:-}"
if [[ -n "$tool_signature" ]]; then
  stage_key="$(printf '%s\0%s\0' "$elf" "$assigned_edu" | sha256sum | awk '{print $1}')"
  signature="$({
    sha256sum "$elf" "$root/scripts/generate-boot-page-plan.sh"
    printf '%s\n' "$assigned_edu" "$tool_signature"
  } | sha256sum | awk '{print $1}')"
  signature_file="${destination}.inputs.${stage_key}.sha256"
  if [[ -f "$destination" && -f "$signature_file" ]] &&
      read -r stored_signature stored_output_hash < "$signature_file" &&
      [[ "$stored_signature" == "$signature" ]]; then
    current_output_hash="$(sha256sum "$destination" | awk '{print $1}')"
    if [[ "$current_output_hash" == "$stored_output_hash" ]]; then
      rm "$output"
      trap - EXIT
      exit 0
    fi
  fi
fi

symbol_decimal() {
  local name="$1" hex
  hex="$(nm -n "$elf" | awk -v wanted="$name" '$3 == wanted { print $1; exit }')"
  [[ -n "$hex" ]] || { echo "error: ELF lacks plan symbol '$name'" >&2; exit 1; }
  printf '%d' "0x$hex"
}

symbols=(
  __boot_image_start __boot_image_end
  __kernel_text_start __kernel_text_end
  __df_ist_guard_start __df_ist_guard_end
  __df_ist_stack_start __df_ist_stack_end
  __nmi_ist_guard_start __nmi_ist_guard_end
  __nmi_ist_stack_start __nmi_ist_stack_end
  __entry_stack_guard_start __entry_stack_guard_end
  __entry_stack_start __entry_stack_end
  page_map_level_4_a page_directory_pointer_a page_directory_a page_table_a
  page_map_level_4_b page_directory_pointer_b page_directory_b page_table_b
  page_table_b_end boot_stack boot_stack_top
  __user_a_text_start __user_a_text_end
  __user_a_stack_start __user_a_stack_end
  __user_b_text_start __user_b_text_end
  __user_b_stack_start __user_b_stack_end
  __vtd_mmio_window_start __vtd_mmio_window_end
  __edu_mmio_window_start __edu_mmio_window_end
)
args=()
for name in "${symbols[@]}"; do args+=("$(symbol_decimal "$name")"); done
args+=("$assigned_edu")
args+=("$(symbol_decimal vtd_root_table)" "$(symbol_decimal vtd_remapping_table_end)")

vtd_symbols=(
  vtd_root_table vtd_context_table vtd_second_level_root
  vtd_second_level_directory vtd_second_level_table vtd_remapping_table_end
  page_map_level_4_a page_table_b_end
  vtd_assigned_guard_before vtd_assigned_read_buffer
  vtd_assigned_write_buffer vtd_assigned_guard_after
)
vtd_args=()
for name in "${vtd_symbols[@]}"; do vtd_args+=("$(symbol_decimal "$name")"); done

if [[ "${LEANOS_BOOT_PLAN_EXECUTABLES_READY:-}" == 1 ]]; then
  # `scripts/build-image.sh` publishes these executables before parallel plan
  # generation. Execute the immutable published paths directly so sibling
  # tasks never ask Lake to rewrite shared build metadata concurrently.
  "$root/.lake/build/bin/leanos-boot-plan" "${args[@]}" > "$output"
  "$root/.lake/build/bin/leanos-vtd-plan" "${vtd_args[@]}" >> "$output"
else
  # Standalone callers retain the ordinary Lake build-and-run path.
  lake exe leanos-boot-plan "${args[@]}" > "$output"
  lake exe leanos-vtd-plan "${vtd_args[@]}" >> "$output"
fi
install_if_changed "$output" "$destination"
if [[ -n "$tool_signature" ]]; then
  output_hash="$(sha256sum "$destination" | awk '{print $1}')"
  printf '%s %s\n' "$signature" "$output_hash" > "$signature_file"
fi
trap - EXIT
