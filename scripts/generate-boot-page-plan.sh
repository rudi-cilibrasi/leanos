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
  page_map_level_4_a page_directory_pointer_a page_directory_a page_table_a
  page_map_level_4_b page_directory_pointer_b page_directory_b page_table_b
  page_table_b_end boot_stack __user_a_text_start
  __user_a_text_start __user_a_text_end
  __user_a_stack_start __user_a_stack_end
  __user_b_text_start __user_b_text_end
  __user_b_stack_start __user_b_stack_end
)
args=()
for name in "${symbols[@]}"; do args+=("$(symbol_decimal "$name")"); done

lake exe leanos-boot-plan "${args[@]}" > "$output"
