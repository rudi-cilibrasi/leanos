#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
build=build/boot-handoff-stream
rm -rf "$build"
mkdir -p "$build"

lake build LeanOS.BootMemoryMapStreaming LeanOS.BootMemoryMapStreamPipeline
prefix="$(lake env lean --print-prefix)"
cflags=(-m64 -std=c11 -O2 -ffreestanding -fno-stack-protector -fno-pic
  -mno-red-zone -ffunction-sections -fdata-sections -Wall -Wextra -Werror)

lake env leanc "${cflags[@]}" -I"$prefix/include" \
  -c .lake/build/ir/LeanOS/BootMemoryMapStreaming.c -o "$build/stream.o"
cc "${cflags[@]}" -c tests/boot-handoff-stream-freestanding.c -o "$build/test.o"
cc -m64 -nostdlib -static -no-pie -Wl,--gc-sections -Wl,-e,_start \
  "$build/test.o" "$build/stream.o" -o "$build/stream.elf"

undefined="$(nm -u "$build/stream.elf")"
if [[ -n "$undefined" ]]; then
  echo "error: handoff stream image has unexpected undefined symbols:" >&2
  echo "$undefined" >&2
  exit 1
fi

symbols="$(nm "$build/stream.elf")"
for symbol in leanos_boot_handoff_stream_init leanos_boot_handoff_stream_step; do
  if ! grep -q " T ${symbol}$" <<<"$symbols"; then
    echo "error: handoff stream image does not retain $symbol" >&2
    exit 1
  fi
done

# This focused final ELF retains only the version-two transport decision
# boundary.  In particular, neither the boxed whole-buffer reader nor the old
# scalar allocation-policy adapter may become an accidental second authority.
for forbidden_policy in leanos_boot_handoff_query leanos_boot_handoff_fixture_query \
  leanos_boot_allocation_check; do
  if grep -q " T ${forbidden_policy}$" <<<"$symbols"; then
    echo "error: handoff stream image retained forbidden policy symbol $forbidden_policy" >&2
    exit 1
  fi
done

# Inventory every retained text symbol so a static C parser/classifier cannot
# hide behind a non-exported name in this final focused artifact.
while read -r text_symbol; do
  case "$text_symbol" in
    _start|check_stream|step_query|leanos_boot_handoff_stream_init|\
leanos_boot_handoff_stream_step|\
lp_leanos___private_LeanOS_BootMemoryMapStreaming_0__LeanOS_BootMemoryMapStreaming_canonicalChunk)
      ;;
    *)
      echo "error: unreviewed handoff stream text symbol $text_symbol" >&2
      exit 1
      ;;
  esac
done < <(awk '$2 == "T" || $2 == "t" { print $3 }' <<<"$symbols")

forbidden='lean_(alloc|box|mk_|dec|inc|nat|array|list|initialize|internal_panic)|mi_(malloc|calloc)|Nat_'
if grep -Eq "$forbidden" \
    <<<"$symbols"; then
  echo "error: handoff stream image retained allocation, boxed, Nat, or initialization runtime" >&2
  grep -E "$forbidden" <<<"$symbols" >&2
  exit 1
fi

"$build/stream.elf"
echo "Freestanding generated-C handoff stream replay passed"
