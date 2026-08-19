#!/usr/bin/env bash
# Sourced by build-image.sh after the shared generated objects are available.
# Keeping this scenario in a separate image preserves the production q35
# topology and makes accidental EDU admission impossible in the default ELF.

if [[ "${BASH_SOURCE[0]}" == "$0" ]]; then
  echo "error: build-assigned-edu-image.sh must be sourced by build-image.sh" >&2
  exit 1
fi

for variable in build cc version source_revision; do
  [[ -n "${!variable:-}" ]] || {
    echo "error: assigned-EDU builder is missing $variable" >&2
    return 1
  }
done
[[ ${#cflags[@]} -gt 0 ]] || {
  echo "error: assigned-EDU builder is missing canonical compiler flags" >&2
  return 1
}

assigned_iso_root="$build/iso-assigned-edu"
assigned_plan="$build/boot-page-plan-assigned-edu.h"
assigned_final_plan="$build/boot-page-plan-assigned-edu.final.h"
mkdir -p "$assigned_iso_root/boot/grub"
./scripts/generate-boot-page-plan.sh --stub "$assigned_plan"

link_assigned_edu() {
  local output_base="$1"
  local kernel_object="$2"
  ld -m elf_x86_64 -nostdlib --gc-sections --build-id=none \
    -T boot/linker.ld -Map "$build/${output_base}.map" \
    -o "$build/${output_base}.elf" "$build/boot.o" \
    "$kernel_object" "$build/KernelTransition.o" \
    "$build/Syscall.o" "$build/IPCSyscall.o" "$build/Preemption.o" \
    "$build/BootAllocation.o" "$build/Interrupt.o" \
    "$build/InterruptEntry.o" "$build/BlockingIPC.o" \
    "$build/CapabilityReuse.o" "$build/ExtendedState.o" \
    "$build/PrivilegeEntryControl.o" "$build/FaultDispatch.o"
}

assigned_plan_converged=false
for pass in 1 2 3 4; do
  "$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
    -DLEANOS_ENTRY_HIGH_WATER=1 -DLEANOS_ASSIGNED_EDU_SCENARIO=1 \
    -DLEANOS_BOOT_PAGE_PLAN_HEADER='"boot-page-plan-assigned-edu.h"' \
    -c boot/kernel.c -o "$build/kernel-assigned-edu.o"
  link_assigned_edu leanos-assigned-edu "$build/kernel-assigned-edu.o"
  ./scripts/generate-boot-page-plan.sh --assigned-edu \
    "$build/leanos-assigned-edu.elf" \
    "$assigned_final_plan"
  if cmp -s "$assigned_plan" "$assigned_final_plan"; then
    assigned_plan_converged=true
    break
  fi
  [[ "$pass" -lt 4 ]] || break
  cp "$assigned_final_plan" "$assigned_plan"
done
[[ "$assigned_plan_converged" == true ]] || {
  echo "error: assigned-EDU boot page-table plan did not converge" >&2
  return 1
}
./scripts/check-image-policy.sh "$build/leanos-assigned-edu.elf"

# These images must fail closed at admission and hardware-evidence boundaries:
# generated CPU mapping, exact device read-back, forged fault binding, and a
# changed protected victim record.
assigned_edu_negative_specs=(
  "missing-mmio-mapping:LEANOS_ASSIGNED_EDU_OMIT_MMIO_MAPPING_FIXTURE"
  "wrong-bar:LEANOS_ASSIGNED_EDU_WRONG_BAR_FIXTURE"
  "wrong-mmio-identity:LEANOS_ASSIGNED_EDU_WRONG_MMIO_IDENTITY_FIXTURE"
  "forged-fault:LEANOS_ASSIGNED_EDU_FORGED_FAULT_FIXTURE"
  "wrong-fault-victim:LEANOS_ASSIGNED_EDU_WRONG_FAULT_VICTIM_FIXTURE"
  "omit-reuse-invalidation:LEANOS_ASSIGNED_EDU_OMIT_REUSE_INVALIDATION_FIXTURE"
)
for spec in "${assigned_edu_negative_specs[@]}"; do
  IFS=: read -r fixture fixture_macro <<<"$spec"
  fixture_base="leanos-assigned-edu-${fixture}"
  fixture_iso_root="$build/iso-assigned-edu-${fixture}"
  "$cc" "${cflags[@]}" -I"$build" -Wall -Wextra -Werror \
    -DLEANOS_ENTRY_HIGH_WATER=1 -DLEANOS_ASSIGNED_EDU_SCENARIO=1 \
    -D"${fixture_macro}"=1 \
    -DLEANOS_BOOT_PAGE_PLAN_HEADER='"boot-page-plan-assigned-edu.h"' \
    -c boot/kernel.c -o "$build/kernel-assigned-edu-${fixture}.o"
  link_assigned_edu "$fixture_base" \
    "$build/kernel-assigned-edu-${fixture}.o"
  if [[ "$fixture" == "omit-reuse-invalidation" ]]; then
    LEANOS_EXPECT_OMIT_REUSE_INVALIDATION=1 \
      ./scripts/check-image-policy.sh "$build/${fixture_base}.elf"
  else
    ./scripts/check-image-policy.sh "$build/${fixture_base}.elf"
  fi
  mkdir -p "$fixture_iso_root/boot/grub"
  cp "$build/${fixture_base}.elf" "$fixture_iso_root/boot/leanos.elf"
  cp boot/grub.cfg "$fixture_iso_root/boot/grub/grub.cfg"
  printf '%s\n' "$source_revision" > "$fixture_iso_root/boot/SOURCE_REVISION"
  grub-mkrescue -d /usr/lib/grub/i386-pc \
    -o "$build/leanos-${version}-x86_64-assigned-edu-${fixture}.iso" \
    "$fixture_iso_root" -- -volume_date uuid 2000010100000000 \
    -volume_date all_file_dates 2000010100000000 >/dev/null
done

cp "$build/leanos-assigned-edu.elf" "$assigned_iso_root/boot/leanos.elf"
cp boot/grub.cfg "$assigned_iso_root/boot/grub/grub.cfg"
printf '%s\n' "$source_revision" > "$assigned_iso_root/boot/SOURCE_REVISION"
grub-mkrescue -d /usr/lib/grub/i386-pc \
  -o "$build/leanos-${version}-x86_64-assigned-edu.iso" \
  "$assigned_iso_root" -- -volume_date uuid 2000010100000000 \
  -volume_date all_file_dates 2000010100000000 >/dev/null
