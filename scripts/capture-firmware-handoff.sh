#!/usr/bin/env bash
# Capture the firmware handoff inputs of the running Linux machine for the
# firmware handoff corpus (docs/firmware-handoff-corpus.md): the
# firmware-provided E820 memory map and the raw ACPI tables the boot decoders
# consume, with the executing processor's APIC identity and enough provenance
# to review the capture. Run it from a Linux live environment on the source
# machine, as root or with passwordless sudo (the raw ACPI tables are
# root-only in sysfs). It records nothing that identifies the machine beyond
# vendor/model/firmware-version strings; serial numbers and UUIDs are never
# read. The corpus converter (scripts/firmware-corpus.py) turns this capture
# into the exact decoder inputs; this script never reorders, merges, or
# repairs anything it reads.
set -euo pipefail
usage() {
  echo "usage: $0 <capture-directory>" >&2
  exit 2
}
[[ $# -eq 1 ]] || usage
out="$1"
[[ -e "$out" ]] && { echo "error: $out already exists" >&2; exit 1; }
mkdir -p "$out/acpi"

read_root() {
  if [[ $EUID -eq 0 ]]; then cat "$1"; else sudo -n cat "$1"; fi
}
sha() { sha256sum "$1" | cut -d ' ' -f 1; }

# The firmware-provided memory map, one row per sysfs entry in index order.
# sysfs `end` is the last byte of the range, not one past it.
memmap=/sys/firmware/memmap
[[ -d "$memmap" ]] || { echo "error: $memmap is not exposed by this kernel" >&2; exit 1; }
printf 'index\tstart\tend\ttype\n' > "$out/memmap.tsv"
for index in $(ls "$memmap" | sort -n); do
  printf '%s\t%s\t%s\t%s\n' "$index" "$(cat "$memmap/$index/start")" \
    "$(cat "$memmap/$index/end")" "$(cat "$memmap/$index/type")"
done >> "$out/memmap.tsv"

# The raw ACPI tables the decoders consume. The MADT (signature APIC) is
# mandatory. Linux does not expose the RSDP, RSDT, or XSDT in sysfs; they are
# recorded only when acpidump can read them, and the corpus marks the
# root-selection stage unavailable otherwise.
tables=/sys/firmware/acpi/tables
[[ -e "$tables/APIC" ]] || { echo "error: $tables/APIC is absent" >&2; exit 1; }
read_root "$tables/APIC" > "$out/acpi/APIC.bin"
root_tables=unavailable
if command -v acpidump > /dev/null 2>&1; then
  dump="$(mktemp -d)"
  if (cd "$dump" && { if [[ $EUID -eq 0 ]]; then acpidump -b; else sudo -n acpidump -b; fi; } > /dev/null 2>&1); then
    for table in rsdp rsdt xsdt; do
      [[ -f "$dump/$table.dat" ]] && cp "$dump/$table.dat" "$out/acpi/${table^^}.bin"
    done
    [[ -f "$out/acpi/RSDP.bin" ]] && root_tables=acpidump
  fi
  rm -rf "$dump"
fi

# The executing processor: Linux boots on the bootstrap processor and
# numbers it processor 0, whose APIC identity /proc/cpuinfo reports.
awk -F ': *' '/^processor/ { p = $2 } /^apicid/ && p == "0" { print $2; exit }' \
  /proc/cpuinfo > "$out/executing-apic-id.txt"
[[ -s "$out/executing-apic-id.txt" ]] || { echo "error: processor 0 APIC ID not found" >&2; exit 1; }

# Machine profile: vendor/model/firmware strings only.
profile() {
  local field="$1" path="/sys/class/dmi/id/$1"
  printf '  "%s": "%s"' "$field" "$( [[ -r "$path" ]] && tr -d '\n"\\' < "$path" || printf unknown )"
}
{
  echo "{"
  echo "  \"capture_tool\": \"scripts/capture-firmware-handoff.sh\","
  echo "  \"capture_tool_sha256\": \"$(sha "${BASH_SOURCE[0]}")\","
  echo "  \"captured_at\": \"$(date -u +%Y-%m-%dT%H:%M:%SZ)\","
  echo "  \"kernel\": \"$(uname -r)\","
  echo "  \"memory_map_source\": \"/sys/firmware/memmap\","
  echo "  \"acpi_table_source\": \"/sys/firmware/acpi/tables\","
  echo "  \"root_tables\": \"$root_tables\","
  echo "  \"processor_count\": $(nproc --all),"
  echo "  \"machine\": {"
  profile sys_vendor; echo ","
  profile product_name; echo ","
  profile bios_vendor; echo ","
  profile bios_version; echo ","
  profile bios_date; echo
  echo "  },"
  echo "  \"files\": {"
  first=1
  for file in $(cd "$out" && find . -type f ! -name provenance.json | sed 's#^\./##' | sort); do
    [[ $first -eq 1 ]] || echo ","
    first=0
    printf '    "%s": "%s"' "$file" "$(sha "$out/$file")"
  done
  echo
  echo "  }"
  echo "}"
} > "$out/provenance.json"
echo "captured firmware handoff inputs into $out (root tables: $root_tables)"
