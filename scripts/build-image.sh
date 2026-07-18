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
preemption_iso_root="$build/iso-preemption"
df_iso_root="$build/iso-double-fault"
df_negative_iso_root="$build/iso-double-fault-guard-mapped"
version="${LEANOS_VERSION:-0.1.0}"
source_revision="${LEANOS_SOURCE_REVISION:-$(git rev-parse HEAD)}"
return_corruptions=(
  'kernel-selector:1:user-return-selector'
  'wrong-stack-selector:2:user-return-selector'
  'noncanonical-rip:3:user-return-noncanonical'
  'noncanonical-rsp:4:user-return-noncanonical'
  'outside-code:5:user-return-code'
  'outside-stack:6:user-return-stack'
  'flags-ac:7:user-return-flags'
  'flags-df:8:user-return-flags'
  'stale-cr3:9:user-return-cr3'
  'stale-context:10:user-return-code'
  'post-validation-mutation:11:user-return-noncanonical'
  'blocking-context-canary:12:register-canary'
)
if [[ ! "$version" =~ ^[0-9]+\.[0-9]+\.[0-9]+$ ]]; then
  echo "error: LEANOS_VERSION must be MAJOR.MINOR.PATCH" >&2
  exit 1
fi
if [[ ! "$source_revision" =~ ^[0-9a-f]{40}$ ]]; then
  echo "error: LEANOS_SOURCE_REVISION must be a full lowercase Git commit" >&2
  exit 1
fi
rm -rf "$build"
mkdir -p "$iso_root/boot/grub" "$preemption_iso_root/boot/grub" "$df_iso_root/boot/grub" \
  "$df_negative_iso_root/boot/grub"
./scripts/generate-oracle.sh "$build"
./scripts/generate-boot-page-plan.sh --stub "$build/boot-page-plan.h"
./scripts/generate-boot-page-plan.sh --stub "$build/boot-page-plan-preemption.h"
./scripts/generate-boot-page-plan.sh --stub "$build/boot-page-plan-double-fault.h"
./scripts/generate-boot-page-plan.sh --stub "$build/boot-page-plan-guard.h"

# C generation resolves project imports through Lake's compiled module path.
# Build them here because image jobs and clean checkouts cannot rely on a
# previous proof-check job's workspace.
lake build
lake env lean --c="$build/KernelTransition.c" LeanOS/KernelTransition.lean
lake env lean --c="$build/Syscall.c" LeanOS/Syscall.lean
lake env lean --c="$build/IPCSyscall.c" LeanOS/IPCSyscall.lean
lake env lean --c="$build/Preemption.c" LeanOS/Preemption.lean
lake env lean --c="$build/BootAllocation.c" LeanOS/BootAllocation.lean
lake env lean --c="$build/Interrupt.c" LeanOS/Interrupt.lean
lake env lean --c="$build/InterruptEntry.c" LeanOS/InterruptEntry.lean
lake env lean --c="$build/BlockingIPC.c" LeanOS/BlockingIPC.lean
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
"$cc" "${cflags[@]}" -I"$lean_prefix/include" -c "$build/Preemption.c" \
  -o "$build/Preemption.o"
"$cc" "${cflags[@]}" -I"$lean_prefix/include" -c "$build/BootAllocation.c" \
  -o "$build/BootAllocation.o"
"$cc" "${cflags[@]}" -I"$lean_prefix/include" -c "$build/Interrupt.c" \
  -o "$build/Interrupt.o"
"$cc" "${cflags[@]}" -I"$lean_prefix/include" -c "$build/InterruptEntry.c" \
  -o "$build/InterruptEntry.o"
"$cc" "${cflags[@]}" -I"$lean_prefix/include" -c "$build/BlockingIPC.c" \
  -o "$build/BlockingIPC.o"
"$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror -c boot/kernel.c \
  -o "$build/kernel.o"
"$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
  -DLEANOS_PREEMPTION_SCENARIO=1 \
  -DLEANOS_BOOT_PAGE_PLAN_HEADER='"boot-page-plan-preemption.h"' \
  -c boot/kernel.c -o "$build/kernel-preemption.o"
"$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
  -DLEANOS_DOUBLE_FAULT_PROBE=1 -c boot/kernel.c -o "$build/kernel-double-fault.o"
"$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
  -DLEANOS_DOUBLE_FAULT_PROBE=1 -DLEANOS_DF_MAP_GUARD=1 \
  -c boot/kernel.c -o "$build/kernel-double-fault-guard-mapped.o"
"$cc" -m64 -ffreestanding -fdebug-prefix-map="$repo_root"=. \
  -ffile-prefix-map="$repo_root"=. -g3 -c boot/boot.S -o "$build/boot.o"
"$cc" -m64 -ffreestanding -fdebug-prefix-map="$repo_root"=. \
  -ffile-prefix-map="$repo_root"=. -g3 -DLEANOS_PREEMPTION_SCENARIO=1 \
  -c boot/boot.S -o "$build/boot-preemption.o"
"$cc" -m64 -ffreestanding -fdebug-prefix-map="$repo_root"=. \
  -ffile-prefix-map="$repo_root"=. -g3 -DLEANOS_RETURN_RESTORE_FIXTURE=1 \
  -c boot/boot.S -o "$build/boot-return-restore-fixture.o"
"$cc" -m64 -ffreestanding -fdebug-prefix-map="$repo_root"=. \
  -ffile-prefix-map="$repo_root"=. -g3 -DLEANOS_RETURN_BRANCH_FIXTURE=1 \
  -c boot/boot.S -o "$build/boot-return-branch-fixture.o"
"$cc" -m64 -ffreestanding -fdebug-prefix-map="$repo_root"=. \
  -ffile-prefix-map="$repo_root"=. -g3 -DLEANOS_RETURN_INDIRECT_FIXTURE=1 \
  -c boot/boot.S -o "$build/boot-return-indirect-fixture.o"
"$cc" -m64 -ffreestanding -fdebug-prefix-map="$repo_root"=. \
  -ffile-prefix-map="$repo_root"=. -g3 -DLEANOS_RETURN_INITIAL_INDIRECT_FIXTURE=1 \
  -c boot/boot.S -o "$build/boot-return-initial-indirect-fixture.o"
"$cc" -m64 -ffreestanding -fdebug-prefix-map="$repo_root"=. \
  -ffile-prefix-map="$repo_root"=. -g3 -DLEANOS_RETURN_POST_VALIDATE_QEMU_FIXTURE=1 \
  -c boot/boot.S -o "$build/boot-return-post-validation-qemu.o"
"$cc" -m64 -ffreestanding -fdebug-prefix-map="$repo_root"=. \
  -ffile-prefix-map="$repo_root"=. -g3 -DLEANOS_DF_MAP_GUARD=1 \
  -c boot/boot.S -o "$build/boot-df-guard-mapped.o"

# The first link fixes every symbol address while using a same-sized plan
# placeholder. Lean then accepts the linker-resolved Input and emits the exact
# PTE arrays used by the guest walker. Recompiling only kernel.c preserves all
# section sizes; the final comparison rejects any unexpected address drift.
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-prelink.map" \
  -o "$build/leanos-prelink.elf" "$build/boot.o" "$build/kernel.o" \
  "$build/KernelTransition.o" "$build/Syscall.o" "$build/IPCSyscall.o" \
  "$build/Preemption.o" "$build/BootAllocation.o" "$build/Interrupt.o" "$build/InterruptEntry.o" \
  "$build/BlockingIPC.o"
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-preemption-prelink.map" \
  -o "$build/leanos-preemption-prelink.elf" "$build/boot-preemption.o" \
  "$build/kernel-preemption.o" "$build/KernelTransition.o" "$build/Syscall.o" \
  "$build/IPCSyscall.o" "$build/Preemption.o" "$build/BootAllocation.o" \
  "$build/Interrupt.o" "$build/InterruptEntry.o" "$build/BlockingIPC.o"
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-double-fault-prelink.map" \
  -o "$build/leanos-double-fault-prelink.elf" "$build/boot.o" \
  "$build/kernel-double-fault.o" "$build/KernelTransition.o" \
  "$build/Syscall.o" "$build/IPCSyscall.o" "$build/Preemption.o" \
  "$build/BootAllocation.o" "$build/Interrupt.o" "$build/InterruptEntry.o" "$build/BlockingIPC.o"
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-guard-prelink.map" \
  -o "$build/leanos-guard-prelink.elf" "$build/boot-df-guard-mapped.o" \
  "$build/kernel-double-fault-guard-mapped.o" "$build/KernelTransition.o" \
  "$build/Syscall.o" "$build/IPCSyscall.o" "$build/Preemption.o" \
  "$build/BootAllocation.o" "$build/Interrupt.o" "$build/InterruptEntry.o" "$build/BlockingIPC.o"
./scripts/generate-boot-page-plan.sh "$build/leanos-prelink.elf" \
  "$build/boot-page-plan.h"
./scripts/generate-boot-page-plan.sh "$build/leanos-preemption-prelink.elf" \
  "$build/boot-page-plan-preemption.h"
./scripts/generate-boot-page-plan.sh "$build/leanos-double-fault-prelink.elf" \
  "$build/boot-page-plan-double-fault.h"
./scripts/generate-boot-page-plan.sh "$build/leanos-guard-prelink.elf" \
  "$build/boot-page-plan-guard.h"
"$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror -c boot/kernel.c \
  -o "$build/kernel.o"
"$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
  -DLEANOS_PREEMPTION_SCENARIO=1 \
  -DLEANOS_BOOT_PAGE_PLAN_HEADER='"boot-page-plan-preemption.h"' \
  -c boot/kernel.c -o "$build/kernel-preemption.o"
if nm "$build/kernel.o" | grep -Eq \
    'return_corruption_mode|return_corruption_name|inject_return_corruption'; then
  echo "error: normal kernel object contains return-corruption fixture code" >&2
  exit 1
fi
for spec in "${return_corruptions[@]}"; do
  IFS=: read -r fixture mode _reason <<<"$spec"
  "$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
    -DLEANOS_RETURN_CORRUPTION_MODE="$mode" -c boot/kernel.c \
    -o "$build/kernel-return-${fixture}.o"
done
"$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
  -DLEANOS_DOUBLE_FAULT_PROBE=1 -c boot/kernel.c -o "$build/kernel-double-fault.o"
"$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
  -DLEANOS_DOUBLE_FAULT_PROBE=1 -DLEANOS_DF_MAP_GUARD=1 \
  -c boot/kernel.c -o "$build/kernel-double-fault-guard-mapped.o"

ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map build/boot/leanos.map \
  -o build/boot/leanos.elf build/boot/boot.o build/boot/kernel.o \
  build/boot/KernelTransition.o build/boot/Syscall.o build/boot/IPCSyscall.o \
  build/boot/Preemption.o build/boot/BootAllocation.o build/boot/Interrupt.o build/boot/InterruptEntry.o \
  build/boot/BlockingIPC.o
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map "$build/leanos-preemption.map" \
  -o "$build/leanos-preemption.elf" "$build/boot-preemption.o" \
  "$build/kernel-preemption.o" "$build/KernelTransition.o" "$build/Syscall.o" \
  "$build/IPCSyscall.o" "$build/Preemption.o" "$build/BootAllocation.o" \
  "$build/Interrupt.o" "$build/InterruptEntry.o" "$build/BlockingIPC.o"

for spec in "${return_corruptions[@]}"; do
  IFS=: read -r fixture mode _reason <<<"$spec"
  boot_object="$build/boot.o"
  if [[ "$fixture" == post-validation-mutation ]]; then
    boot_object="$build/boot-return-post-validation-qemu.o"
  fi
  ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
    -T boot/linker.ld -Map "$build/leanos-return-${fixture}-prelink.map" \
    -o "$build/leanos-return-${fixture}-prelink.elf" "$boot_object" \
    "$build/kernel-return-${fixture}.o" "$build/KernelTransition.o" \
    "$build/Syscall.o" "$build/IPCSyscall.o" "$build/Preemption.o" \
    "$build/BootAllocation.o" "$build/Interrupt.o" "$build/InterruptEntry.o" "$build/BlockingIPC.o"
  ./scripts/generate-boot-page-plan.sh "$build/leanos-return-${fixture}-prelink.elf" \
    "$build/boot-page-plan-return-${fixture}.h"
  "$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
    -DLEANOS_RETURN_CORRUPTION_MODE="$mode" \
    -DLEANOS_BOOT_PAGE_PLAN_HEADER="\"boot-page-plan-return-${fixture}.h\"" \
    -c boot/kernel.c -o "$build/kernel-return-${fixture}.o"
  ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
    -T boot/linker.ld -Map "$build/leanos-return-${fixture}.map" \
    -o "$build/leanos-return-${fixture}.elf" "$boot_object" \
    "$build/kernel-return-${fixture}.o" "$build/KernelTransition.o" \
    "$build/Syscall.o" "$build/IPCSyscall.o" "$build/Preemption.o" \
    "$build/BootAllocation.o" "$build/Interrupt.o" "$build/InterruptEntry.o" "$build/BlockingIPC.o"
  ./scripts/generate-boot-page-plan.sh "$build/leanos-return-${fixture}.elf" \
    "$build/boot-page-plan-return-${fixture}.final.h"
  cmp "$build/boot-page-plan-return-${fixture}.h" \
    "$build/boot-page-plan-return-${fixture}.final.h" || {
    echo "error: ${fixture} boot page-table plan drifted after final link" >&2
    exit 1
  }
  if [[ "$fixture" == post-validation-mutation ]]; then
    if ./scripts/check-image-policy.sh "$build/leanos-return-${fixture}.elf" \
        >"$build/return-${fixture}-policy.log" 2>&1; then
      echo "error: post-validation mutation policy fixture unexpectedly passed" >&2
      exit 1
    fi
    grep -Fq 'mutation or control flow added after user-return validation' \
      "$build/return-${fixture}-policy.log" || {
      echo "error: post-validation fixture lacked policy diagnostic" >&2; exit 1;
    }
  else
    ./scripts/check-image-policy.sh "$build/leanos-return-${fixture}.elf"
  fi
done

./scripts/generate-boot-page-plan.sh "$build/leanos.elf" \
  "$build/boot-page-plan.final.h"
cmp "$build/boot-page-plan.h" "$build/boot-page-plan.final.h" || {
  echo "error: linker-resolved boot page-table plan drifted after final link" >&2
  exit 1
}
./scripts/generate-boot-page-plan.sh "$build/leanos-preemption.elf" \
  "$build/boot-page-plan-preemption.final.h"
cmp "$build/boot-page-plan-preemption.h" \
  "$build/boot-page-plan-preemption.final.h" || {
  echo "error: preemption boot page-table plan drifted after final link" >&2
  exit 1
}
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map build/boot/leanos-double-fault.map \
  -o build/boot/leanos-double-fault.elf build/boot/boot.o \
  build/boot/kernel-double-fault.o build/boot/KernelTransition.o \
  build/boot/Syscall.o build/boot/IPCSyscall.o build/boot/Preemption.o \
  build/boot/BootAllocation.o build/boot/Interrupt.o build/boot/InterruptEntry.o build/boot/BlockingIPC.o
ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
  -T boot/linker.ld -Map build/boot/leanos-double-fault-guard-mapped.map \
  -o build/boot/leanos-double-fault-guard-mapped.elf \
  build/boot/boot-df-guard-mapped.o \
  build/boot/kernel-double-fault-guard-mapped.o \
  build/boot/KernelTransition.o build/boot/Syscall.o build/boot/IPCSyscall.o \
  build/boot/Preemption.o build/boot/BootAllocation.o build/boot/Interrupt.o build/boot/InterruptEntry.o \
  build/boot/BlockingIPC.o

./scripts/generate-boot-page-plan.sh "$build/leanos-double-fault.elf" \
  "$build/boot-page-plan-double-fault.final.h"
cmp "$build/boot-page-plan-double-fault.h" \
  "$build/boot-page-plan-double-fault.final.h" || {
  echo "error: double-fault boot page-table plan drifted after final link" >&2
  exit 1
}
./scripts/generate-boot-page-plan.sh "$build/leanos-double-fault-guard-mapped.elf" \
  "$build/boot-page-plan-guard.final.h"
cmp "$build/boot-page-plan-guard.h" "$build/boot-page-plan-guard.final.h" || {
  echo "error: guard-mapped boot page-table plan drifted after final link" >&2
  exit 1
}

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
if ! grep -q ' T leanos_boot_allocation_check$' <<<"$symbols"; then
  echo "error: generated image does not retain leanos_boot_allocation_check" >&2
  exit 1
fi
if ! grep -q ' T leanos_user_return_demo$' <<<"$symbols"; then
  echo "error: generated image does not retain leanos_user_return_demo" >&2
  exit 1
fi
if ! grep -q ' T leanos_blocking_ipc_demo$' <<<"$symbols"; then
  echo "error: generated image does not retain leanos_blocking_ipc_demo" >&2
  exit 1
fi
if ! grub-file --is-x86-multiboot2 "$build/leanos.elf"; then
  echo "error: kernel ELF has no valid Multiboot2 header" >&2
  exit 1
fi
./scripts/check-image-policy.sh "$build/leanos.elf"
./scripts/check-image-policy.sh "$build/leanos-preemption.elf"
./scripts/check-image-policy.sh "$build/leanos-double-fault.elf"

for fixture in restore branch indirect initial-indirect; do
  ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
    -T boot/linker.ld -Map "$build/leanos-return-${fixture}-fixture.map" \
    -o "$build/leanos-return-${fixture}-fixture.elf" \
    "$build/boot-return-${fixture}-fixture.o" "$build/kernel.o" \
    "$build/KernelTransition.o" "$build/Syscall.o" "$build/IPCSyscall.o" \
    "$build/Preemption.o" "$build/BootAllocation.o" "$build/Interrupt.o" "$build/InterruptEntry.o" \
    "$build/BlockingIPC.o"
  if ./scripts/check-image-policy.sh "$build/leanos-return-${fixture}-fixture.elf" \
      >"$build/return-${fixture}-fixture.log" 2>&1; then
    echo "error: user-return ${fixture} negative fixture unexpectedly passed" >&2
    exit 1
  fi
done
grep -Fq 'error: unexpected exact user-return restore sequence' \
  "$build/return-restore-fixture.log" || {
  echo "error: restore negative fixture lacked expected diagnostic" >&2; exit 1;
}
grep -Fq 'enters post-validation restore interval' \
  "$build/return-branch-fixture.log" || {
  echo "error: branch negative fixture lacked expected diagnostic" >&2; exit 1;
}
grep -Fq 'indirect control-flow instruction' \
  "$build/return-indirect-fixture.log" || {
  echo "error: indirect negative fixture lacked expected diagnostic" >&2; exit 1;
}
grep -Fq 'indirect control-flow instruction' \
  "$build/return-initial-indirect-fixture.log" || {
  echo "error: initial indirect fixture lacked expected diagnostic" >&2; exit 1;
}

cp "$build/leanos.elf" "$iso_root/boot/leanos.elf"
cp boot/grub.cfg "$iso_root/boot/grub/grub.cfg"
cp "$build/leanos-preemption.elf" "$preemption_iso_root/boot/leanos.elf"
cp boot/grub.cfg "$preemption_iso_root/boot/grub/grub.cfg"
cp "$build/leanos-double-fault.elf" "$df_iso_root/boot/leanos.elf"
cp boot/grub-double-fault.cfg "$df_iso_root/boot/grub/grub.cfg"
cp "$build/leanos-double-fault-guard-mapped.elf" \
  "$df_negative_iso_root/boot/leanos.elf"
cp boot/grub-double-fault.cfg "$df_negative_iso_root/boot/grub/grub.cfg"
printf '%s\n' "$source_revision" | tee "$build/SOURCE_REVISION" \
  > "$iso_root/boot/SOURCE_REVISION"
cp "$build/SOURCE_REVISION" "$df_iso_root/boot/SOURCE_REVISION"
cp "$build/SOURCE_REVISION" "$preemption_iso_root/boot/SOURCE_REVISION"
cp "$build/SOURCE_REVISION" "$df_negative_iso_root/boot/SOURCE_REVISION"
for spec in "${return_corruptions[@]}"; do
  IFS=: read -r fixture _mode _reason <<<"$spec"
  fixture_root="$build/iso-return-${fixture}"
  mkdir -p "$fixture_root/boot/grub"
  cp "$build/leanos-return-${fixture}.elf" "$fixture_root/boot/leanos.elf"
  cp boot/grub.cfg "$fixture_root/boot/grub/grub.cfg"
  cp "$build/SOURCE_REVISION" "$fixture_root/boot/SOURCE_REVISION"
done
# BIOS-only output avoids GRUB's nondeterministic FAT/EFI image. A fixed ISO
# UUID and file dates make repeated builds independent of wall-clock time.
grub-mkrescue -d /usr/lib/grub/i386-pc \
  -o "$build/leanos-${version}-x86_64.iso" "$iso_root" -- \
  -volume_date uuid 2000010100000000 \
  -volume_date all_file_dates 2000010100000000 >/dev/null
grub-mkrescue -d /usr/lib/grub/i386-pc \
  -o "$build/leanos-${version}-x86_64-preemption.iso" "$preemption_iso_root" -- \
  -volume_date uuid 2000010100000000 \
  -volume_date all_file_dates 2000010100000000 >/dev/null
grub-mkrescue -d /usr/lib/grub/i386-pc \
  -o "$build/leanos-${version}-x86_64-double-fault.iso" "$df_iso_root" -- \
  -volume_date uuid 2000010100000000 \
  -volume_date all_file_dates 2000010100000000 >/dev/null
grub-mkrescue -d /usr/lib/grub/i386-pc \
  -o "$build/leanos-${version}-x86_64-double-fault-guard-mapped.iso" \
  "$df_negative_iso_root" -- -volume_date uuid 2000010100000000 \
  -volume_date all_file_dates 2000010100000000 >/dev/null
for spec in "${return_corruptions[@]}"; do
  IFS=: read -r fixture _mode _reason <<<"$spec"
  grub-mkrescue -d /usr/lib/grub/i386-pc \
    -o "$build/leanos-${version}-x86_64-return-${fixture}.iso" \
    "$build/iso-return-${fixture}" -- \
    -volume_date uuid 2000010100000000 \
    -volume_date all_file_dates 2000010100000000 >/dev/null
done
sha256sum "$build/leanos-${version}-x86_64.iso" \
  "$build/leanos-${version}-x86_64-preemption.iso" \
  "$build/leanos-${version}-x86_64-double-fault.iso" "$build/leanos.elf" \
  "$build/leanos-preemption.elf" "$build/leanos-preemption.map" \
  "$build/leanos-double-fault.elf" \
  "$build/leanos-${version}-x86_64-double-fault-guard-mapped.iso" \
  "$build/leanos-double-fault-guard-mapped.elf" \
  > "$build/SHA256SUMS"
for spec in "${return_corruptions[@]}"; do
  IFS=: read -r fixture _mode _reason <<<"$spec"
  sha256sum "$build/leanos-${version}-x86_64-return-${fixture}.iso" \
    "$build/leanos-return-${fixture}.elf" >> "$build/SHA256SUMS"
done
echo "built build/boot/leanos-${version}-x86_64.iso at $source_revision"
echo "symbols: build/boot/leanos.map; debug ELF: build/boot/leanos.elf"
