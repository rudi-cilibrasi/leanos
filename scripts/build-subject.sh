#!/usr/bin/env bash
# Build one ring-3 subject from a subjects/ directory into a relocatable
# object for one slot of the boot image (#484).
#
#   build-subject.sh --cc CC --slot c --output OBJ SUBJECT_DIR
#
# 1. Compile every *.c and *.S in SUBJECT_DIR, plus subjects/runtime/entry.S,
#    separately and freestanding: no libc, no SSE/x87, no stack protector,
#    no unwind tables or CET notes.
# 2. Link them with `ld -r -T subjects/subject.ld` into .subject.text and
#    .subject.bss.  This chooses no address.
# 3. Check the object against the assembly/ABI policy
#    (scripts/check-subject-policy.py object): no privileged or system
#    instruction, no stac/clac, kernel entry only through int $0x80, no
#    extended-state registers, no undefined symbols, and the slot's sizes.
# 4. Rename the sections to the slot's input sections (.user.<slot>.text,
#    .user.<slot>.bss) and the symbols to the slot's names (user_<slot>_entry,
#    user_<slot>_stack, user_<slot>_stack_top, user_<slot>_template_text);
#    every other symbol is prefixed with user_<slot>_ and made local.
#
# boot/linker.ld places the renamed sections at the slot's range when the
# image is linked, and the boot page plan is generated from that linked ELF,
# so addresses flow from the plan's linked input to the subject, never back.
# check-image-policy.sh re-runs the instruction policy on the final ELF.
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cc="${LEANOS_CC:-gcc}"
slot=""
output=""
while (($#)); do
  case "$1" in
    --cc) cc="$2"; shift 2 ;;
    --slot) slot="$2"; shift 2 ;;
    --output) output="$2"; shift 2 ;;
    --) shift; break ;;
    -*) echo "error: build-subject: unknown option $1" >&2; exit 2 ;;
    *) break ;;
  esac
done
(($# == 1)) && [[ -n "$output" ]] || {
  echo "usage: build-subject.sh [--cc CC] --slot c --output OBJ SUBJECT_DIR" >&2
  exit 2
}
subject_dir="${1%/}"
# Only slot C is linked from a separate object today; A and B are still the
# handwritten boot.S subjects every image shares.
[[ "$slot" == c ]] || {
  echo "error: build-subject: unsupported slot '$slot' (only c)" >&2; exit 2;
}
[[ -d "$subject_dir" ]] || {
  echo "error: build-subject: no subject directory $subject_dir" >&2; exit 2;
}

sources=()
while IFS= read -r -d '' source; do
  sources+=("$source")
done < <(find "$subject_dir" -maxdepth 1 -type f \( -name '*.c' -o -name '*.S' \) \
  -print0 | LC_ALL=C sort -z)
((${#sources[@]} > 0)) || {
  echo "error: build-subject: $subject_dir has no .c or .S sources" >&2; exit 1;
}

cflags=(-m64 -std=c11 -ffreestanding -fno-builtin -fno-stack-protector
  -fno-pic -fno-common -mno-red-zone -mgeneral-regs-only -fno-jump-tables
  -fno-asynchronous-unwind-tables -fno-unwind-tables -fcf-protection=none
  -O2 -Wall -Wextra -Werror -I"$repo_root/subjects/include"
  -ffile-prefix-map="$repo_root"=.)

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
objects=()
index=0
for source in "$repo_root/subjects/runtime/entry.S" "${sources[@]}"; do
  object="$work/$index.o"
  "$cc" "${cflags[@]}" -c "$source" -o "$object"
  objects+=("$object")
  index=$((index + 1))
done
ld -m elf_x86_64 -r --build-id=none -T "$repo_root/subjects/subject.ld" \
  -o "$work/subject.o" "${objects[@]}"
python3 "$repo_root/scripts/check-subject-policy.py" object "$work/subject.o" \
  >/dev/null

objcopy --prefix-symbols="user_${slot}_" "$work/subject.o" "$work/prefixed.o"
objcopy \
  --rename-section ".subject.text=.user.${slot}.text" \
  --rename-section ".subject.bss=.user.${slot}.bss" \
  --redefine-sym "user_${slot}_subject_entry=user_${slot}_entry" \
  --redefine-sym "user_${slot}_subject_stack=user_${slot}_stack" \
  --redefine-sym "user_${slot}_subject_stack_top=user_${slot}_stack_top" \
  --redefine-sym "user_${slot}_subject_template_text=user_${slot}_template_text" \
  "$work/prefixed.o" "$work/renamed.o"
objcopy \
  --keep-global-symbol "user_${slot}_entry" \
  --keep-global-symbol "user_${slot}_stack" \
  --keep-global-symbol "user_${slot}_stack_top" \
  --keep-global-symbol "user_${slot}_template_text" \
  "$work/renamed.o" "$work/slot.o"
for symbol in entry stack stack_top template_text; do
  nm "$work/slot.o" | grep -Eq "^[0-9a-f]+ [A-Z] user_${slot}_${symbol}$" || {
    echo "error: build-subject: slot object lacks global user_${slot}_${symbol}" >&2
    exit 1
  }
done
mkdir -p "$(dirname "$output")"
mv "$work/slot.o" "$output"
