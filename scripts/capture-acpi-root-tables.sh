#!/usr/bin/env bash
# Retain one exact physical table copy per distinct RSDT/XSDT address.
# Input roots are unmodified acpidump binaries; output names encode addresses,
# so repeated signatures never rely on acpidump's instance-number filenames.
set -euo pipefail
acpi="${1:?usage: capture-acpi-root-tables.sh ACPI_DIRECTORY}"
[[ "$(uname -m)" == x86_64 ]] || { echo 'error: root capture needs a little-endian x86_64 host' >&2; exit 1; }
[[ ! -e "$acpi/root-tables" ]] || { echo 'error: root table destination already exists' >&2; exit 1; }
mkdir "$acpi/root-tables"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
run_dump() {
  if [[ $EUID -eq 0 ]]; then acpidump "$@"; else sudo -n acpidump "$@"; fi
}
declare -A seen=()
total=0
for kind in RSDT XSDT; do
  root="$acpi/$kind.bin"
  [[ -f "$root" ]] || continue
  width=4
  [[ "$kind" == XSDT ]] && width=8
  size="$(stat -c %s "$root")"
  (( size >= 36 && size <= 65536 && (size - 36) % width == 0 && (size - 36) / width <= 256 )) || {
    echo "error: unsupported $kind capture bounds" >&2; exit 1;
  }
  # od is native little-endian, checked above. Preserve the root vector itself;
  # only duplicate physical reads across the two roots are elided.
  od -An -v -j36 "-tu$width" "$root" > "$work/addresses"
  for address in $(cat "$work/addresses"); do
    (( address > 0 && address <= 4503599627370495 )) || {
      echo 'error: root entry outside supported physical address range' >&2; exit 1;
    }
    [[ -z "${seen[$address]:-}" ]] || continue
    seen[$address]=1
    printf -v hex '%016x' "$address"
    mkdir "$work/$hex"
    (cd "$work/$hex" && run_dump -c off -a "0x$hex" -b) > "$work/dump.log" 2>&1 || {
      cat "$work/dump.log" >&2; exit 1;
    }
    shopt -s nullglob
    files=("$work/$hex/"*.dat)
    (( ${#files[@]} == 1 )) || { echo 'error: physical query did not return exactly one table' >&2; exit 1; }
    size="$(stat -c %s "${files[0]}")"
    (( size >= 36 && size <= 65536 && total + size <= 1048576 )) || {
      echo 'error: physical table copy exceeds capture bounds' >&2; exit 1;
    }
    total=$((total + size))
    cp "${files[0]}" "$acpi/root-tables/$hex.bin"
  done
done
