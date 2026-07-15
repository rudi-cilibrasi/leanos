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
version="${LEANOS_VERSION:-0.1.0}"
source_revision="${LEANOS_SOURCE_REVISION:-$(git rev-parse HEAD)}"
if [[ ! "$version" =~ ^[0-9]+\.[0-9]+\.[0-9]+$ ]]; then
  echo "error: LEANOS_VERSION must be MAJOR.MINOR.PATCH" >&2
  exit 1
fi
if [[ ! "$source_revision" =~ ^[0-9a-f]{40}$ ]]; then
  echo "error: LEANOS_SOURCE_REVISION must be a full lowercase Git commit" >&2
  exit 1
fi
rm -rf "$build"
mkdir -p "$iso_root/boot/grub"
./scripts/generate-oracle.sh "$build"

# C generation resolves project imports through Lake's compiled module path.
# Build them here because image jobs and clean checkouts cannot rely on a
# previous proof-check job's workspace.
lake build
lake env lean --c="$build/KernelTransition.c" LeanOS/KernelTransition.lean
lake env lean --c="$build/Syscall.c" LeanOS/Syscall.lean
lake env lean --c="$build/IPCSyscall.c" LeanOS/IPCSyscall.lean
lean_prefix="$(lake env lean --print-prefix)"
cflags=(-m64 -std=c11 -ffreestanding -fno-stack-protector -fno-pic
  -mno-red-zone -mgeneral-regs-only -ffunction-sections -fdata-sections
  -fdebug-prefix-map="$repo_root"=. -ffile-prefix-map="$repo_root"=.
  -fdebug-prefix-map="$lean_prefix"=/lean-toolchain
  -ffile-prefix-map="$lean_prefix"=/lean-toolchain -g3 -O2)
"$cc" "${cflags[@]}" -I"$lean_prefix/include" -c "$build/KernelTransition.c" \
  -o "$build/KernelTransition.o"
"$cc" "${cflags[@]}" -I"$lean_prefix/include" -c "$build/Syscall.c" \
  -o "$build/Syscall.o"
"$cc" "${cflags[@]}" -I"$lean_prefix/include" -c "$build/IPCSyscall.c" \
  -o "$build/IPCSyscall.o"
"$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror -c boot/kernel.c \
  -o "$build/kernel.o"
"$cc" -m64 -ffreestanding -fdebug-prefix-map="$repo_root"=. \
  -ffile-prefix-map="$repo_root"=. -g3 -c boot/boot.S -o "$build/boot.o"

ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map build/boot/leanos.map \
  -o build/boot/leanos.elf build/boot/boot.o build/boot/kernel.o \
  build/boot/KernelTransition.o build/boot/Syscall.o build/boot/IPCSyscall.o

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
if ! nm "$build/leanos.elf" | grep -q ' T leanos_syscall_demo$'; then
  echo "error: generated image does not retain leanos_syscall_demo" >&2
  exit 1
fi
if ! nm "$build/leanos.elf" | grep -q ' T leanos_ipc_demo$'; then
  echo "error: generated image does not retain leanos_ipc_demo" >&2
  exit 1
fi
if ! grub-file --is-x86-multiboot2 "$build/leanos.elf"; then
  echo "error: kernel ELF has no valid Multiboot2 header" >&2
  exit 1
fi
./scripts/check-image-policy.sh "$build/leanos.elf"

cp "$build/leanos.elf" "$iso_root/boot/leanos.elf"
cp boot/grub.cfg "$iso_root/boot/grub/grub.cfg"
printf '%s\n' "$source_revision" | tee "$build/SOURCE_REVISION" \
  > "$iso_root/boot/SOURCE_REVISION"
# BIOS-only output avoids GRUB's nondeterministic FAT/EFI image. A fixed ISO
# UUID and file dates make repeated builds independent of wall-clock time.
grub-mkrescue -d /usr/lib/grub/i386-pc \
  -o "$build/leanos-${version}-x86_64.iso" "$iso_root" -- \
  -volume_date uuid 2000010100000000 \
  -volume_date all_file_dates 2000010100000000 >/dev/null
sha256sum "$build/leanos-${version}-x86_64.iso" "$build/leanos.elf" \
  > "$build/SHA256SUMS"
echo "built build/boot/leanos-${version}-x86_64.iso at $source_revision"
echo "symbols: build/boot/leanos.map; debug ELF: build/boot/leanos.elf"
