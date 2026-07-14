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
require_tool gcc "install Ubuntu package gcc=4:13.2.0-7ubuntu1"
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
rm -rf "$build"
mkdir -p "$iso_root/boot/grub"

lake env lean --c="$build/KernelTransition.c" LeanOS/KernelTransition.lean
lean_prefix="$(lake env lean --print-prefix)"
cflags=(-m64 -std=c11 -ffreestanding -fno-stack-protector -fno-pic
  -mno-red-zone -mgeneral-regs-only -ffunction-sections -fdata-sections
  -g3 -O2)
gcc "${cflags[@]}" -I"$lean_prefix/include" -c "$build/KernelTransition.c" \
  -o "$build/KernelTransition.o"
gcc "${cflags[@]}" -Wall -Wextra -Werror -c boot/kernel.c \
  -o "$build/kernel.o"
gcc -m64 -ffreestanding -g3 -c boot/boot.S -o "$build/boot.o"

ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos.map" \
  -o "$build/leanos.elf" "$build/boot.o" "$build/kernel.o" \
  "$build/KernelTransition.o"

undefined="$(nm -u "$build/leanos.elf")"
if [[ -n "$undefined" ]]; then
  echo "error: boot image has unexpected undefined symbols:" >&2
  echo "$undefined" >&2
  exit 1
fi
if ! nm "$build/leanos.elf" | grep -q ' T leanos_boot_transition$'; then
  echo "error: generated image does not retain leanos_boot_transition" >&2
  exit 1
fi
if ! grub-file --is-x86-multiboot2 "$build/leanos.elf"; then
  echo "error: kernel ELF has no valid Multiboot2 header" >&2
  exit 1
fi

cp "$build/leanos.elf" "$iso_root/boot/leanos.elf"
cp boot/grub.cfg "$iso_root/boot/grub/grub.cfg"
grub-mkrescue -o "$build/leanos-0.1.0-x86_64.iso" "$iso_root" >/dev/null
sha256sum "$build/leanos-0.1.0-x86_64.iso" "$build/leanos.elf" \
  > "$build/SHA256SUMS"
echo "built build/boot/leanos-0.1.0-x86_64.iso"
echo "symbols: build/boot/leanos.map; debug ELF: build/boot/leanos.elf"
