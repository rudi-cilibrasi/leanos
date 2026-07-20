#!/usr/bin/env bash
set -euo pipefail

elf="${1:-build/boot/leanos.elf}"
manifest="${2:-scripts/direct-port-sites.tsv}"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

cp "$manifest" "$tmp/sites.tsv"
sed -i '0,/^[^#]/{/^[^#]/d;}' "$tmp/sites.tsv"
if ./scripts/check-direct-port-sites.py "$elf" "$tmp/sites.tsv" \
    >"$tmp/missing.log" 2>&1; then
  echo "error: omitted direct-port site fixture unexpectedly passed" >&2
  exit 1
fi
grep -Fq 'error: unauthorized final-ELF port-I/O site' "$tmp/missing.log" || {
  cat "$tmp/missing.log" >&2
  echo "error: omitted direct-port site fixture lacked semantic diagnostic" >&2
  exit 1
}

sed '0,/DMAQuarantine.boot-pci-config/s//DirectPortIO.serial/' \
  "$manifest" >"$tmp/wrong-owner.tsv"
if ./scripts/check-direct-port-sites.py "$elf" "$tmp/wrong-owner.tsv" \
    >"$tmp/owner.log" 2>&1; then
  echo "error: PCI owner fixture unexpectedly passed" >&2
  exit 1
fi
grep -Fq 'error: boot-only PCI configuration site classification drifted' \
  "$tmp/owner.log" || {
  cat "$tmp/owner.log" >&2
  echo "error: PCI owner fixture lacked semantic diagnostic" >&2
  exit 1
}

cp boot/kernel.c "$tmp/kernel.c"
printf '\nstatic void unauthorized_port_call(void) { out32(0x80u, 0); }\n' \
  >>"$tmp/kernel.c"
if ./scripts/check-direct-port-sites.py "$elf" "$manifest" \
    --source "$tmp/kernel.c" >"$tmp/caller.log" 2>&1; then
  echo "error: unauthorized PCI-wrapper caller fixture unexpectedly passed" >&2
  exit 1
fi
grep -Fq 'error: boot-only PCI configuration wrapper call contract drifted' \
  "$tmp/caller.log" || {
  cat "$tmp/caller.log" >&2
  echo "error: PCI-wrapper caller fixture lacked semantic diagnostic" >&2
  exit 1
}

echo 'Direct-port final-ELF negative fixtures passed'
