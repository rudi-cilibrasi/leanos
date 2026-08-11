#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

if [[ "${1:-}" == --stub ]]; then
  output="${2:?usage: $0 --stub OUTPUT}"
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
    echo '#define LEANOS_VTD_ROOT_TABLE_FRAME 1ULL'
    echo '#define LEANOS_VTD_CONTEXT_TABLE_FRAME 2ULL'
    echo '#define LEANOS_VTD_ROOT_TABLE_ADDRESS 4096ULL'
    echo '#define LEANOS_VTD_CANONICAL_JOURNAL 2271560481ULL'
    echo 'static const unsigned long long leanos_vtd_root_table[512] = {'
    echo '  8193ULL,'
    for ((word = 1; word < 512; ++word)); do echo '  0ULL,'; done
    echo '};'
    echo 'static const unsigned long long leanos_vtd_context_table[512] = {'
    for ((word = 0; word < 512; ++word)); do echo '  0ULL,'; done
    echo '};'
  } > "$output"
  exit 0
fi

elf="${1:?usage: $0 ELF OUTPUT}"
output="${2:?usage: $0 ELF OUTPUT}"
[[ -f "$elf" ]] || { echo "error: missing prelinked ELF '$elf'" >&2; exit 1; }

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
  vtd_root_table vtd_remapping_table_end
)
args=()
for name in "${symbols[@]}"; do args+=("$(symbol_decimal "$name")"); done

vtd_symbols=(
  vtd_root_table vtd_context_table vtd_remapping_table_end
  page_map_level_4_a page_table_b_end
)
vtd_args=()
for name in "${vtd_symbols[@]}"; do vtd_args+=("$(symbol_decimal "$name")"); done

lake exe leanos-boot-plan "${args[@]}" > "$output"
lake exe leanos-vtd-plan "${vtd_args[@]}" >> "$output"
