#!/usr/bin/env bash
set -euo pipefail

elf="${1:-build/boot/leanos.elf}"
manifest="${2:-scripts/direct-port-sites.tsv}"
cc="${LEANOS_CC:-gcc}"
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

if grep -q '^user_a_direct_port_probe' "$manifest"; then
  sed 's/DirectPortIO.user-denial-probe/DirectPortIO.debug-exit/' \
    "$manifest" >"$tmp/user-authority.tsv"
  if ./scripts/check-direct-port-sites.py "$elf" "$tmp/user-authority.tsv" \
      >"$tmp/user-authority.log" 2>&1; then
    echo "error: user denial probe authority fixture unexpectedly passed" >&2
    exit 1
  fi
  grep -Fq 'error: user direct-port denial probe has authority owner' \
    "$tmp/user-authority.log" || {
    cat "$tmp/user-authority.log" >&2
    echo "error: user denial probe fixture lacked semantic diagnostic" >&2
    exit 1
  }
fi

cp boot/kernel.c "$tmp/pci-kernel.c"
printf '\nstatic void unauthorized_port_call(void) { out32(0x80u, 0); }\n' \
  >>"$tmp/pci-kernel.c"
if ./scripts/check-direct-port-sites.py "$elf" "$manifest" \
    --source "$tmp/pci-kernel.c" >"$tmp/pci-caller.log" 2>&1; then
  echo "error: unauthorized PCI-wrapper caller fixture unexpectedly passed" >&2
  exit 1
fi
grep -Fq 'error: boot-only PCI configuration wrapper call contract drifted' \
  "$tmp/pci-caller.log" || {
  cat "$tmp/pci-caller.log" >&2
  echo "error: PCI-wrapper caller fixture lacked semantic diagnostic" >&2
  exit 1
}

cp boot/kernel.c "$tmp/byte-kernel.c"
printf '\nstatic void unauthorized_port_call(void) { out8(0x20u, 0); }\n' \
  >>"$tmp/byte-kernel.c"
if ./scripts/check-direct-port-sites.py "$elf" "$manifest" \
    --source "$tmp/byte-kernel.c" >"$tmp/byte-caller.log" 2>&1; then
  echo "error: unauthorized byte-wrapper caller fixture unexpectedly passed" >&2
  exit 1
fi
grep -Fq 'error: unauthorized byte-wrapper operation unauthorized_port_call out8 0x20' \
  "$tmp/byte-caller.log" || {
  cat "$tmp/byte-caller.log" >&2
  echo "error: byte-wrapper caller fixture lacked semantic diagnostic" >&2
  exit 1
}

"$cc" -m64 -c tests/fixtures/direct-port-sites.S \
  -o "$tmp/skipped-quarantine.o" -DLEANOS_SKIPPED_QUARANTINE=1
ld -m elf_x86_64 -nostdlib --build-id=none -e kernel_main \
  -o "$tmp/skipped-quarantine.elf" "$tmp/skipped-quarantine.o"
if ./scripts/check-direct-port-sites.py "$tmp/skipped-quarantine.elf" \
    tests/fixtures/direct-port-sites.tsv >"$tmp/skipped-quarantine.log" 2>&1; then
  echo "error: skipped PCI quarantine fixture unexpectedly passed" >&2
  exit 1
fi
grep -Fq 'error: boot-only PCI quarantine is unreachable from kernel_main entry' \
  "$tmp/skipped-quarantine.log" || {
  cat "$tmp/skipped-quarantine.log" >&2
  echo "error: skipped PCI quarantine fixture lacked reachability diagnostic" >&2
  exit 1
}

"$cc" -m64 -c tests/fixtures/direct-port-sites.S \
  -o "$tmp/runtime-reuse.o" -DLEANOS_RUNTIME_HANDLER_REUSE=1
ld -m elf_x86_64 -nostdlib --build-id=none -e kernel_main \
  -o "$tmp/runtime-reuse.elf" "$tmp/runtime-reuse.o"
if ./scripts/check-direct-port-sites.py "$tmp/runtime-reuse.elf" \
    tests/fixtures/direct-port-sites.tsv >"$tmp/runtime-reuse.log" 2>&1; then
  echo "error: runtime PCI-helper reuse fixture unexpectedly passed" >&2
  exit 1
fi
grep -Fq 'error: boot-only PCI final-ELF call graph drifted callee=pci_config_dword' \
  "$tmp/runtime-reuse.log" || {
  cat "$tmp/runtime-reuse.log" >&2
  echo "error: runtime PCI-helper reuse fixture lacked semantic diagnostic" >&2
  exit 1
}

"$cc" -m64 -c tests/fixtures/direct-port-sites.S \
  -o "$tmp/conditional-site.o" -DLEANOS_CONDITIONAL_PORT_SITE=1
ld -m elf_x86_64 -nostdlib --build-id=none -e kernel_main \
  -o "$tmp/conditional-site.elf" "$tmp/conditional-site.o"
if ./scripts/check-direct-port-sites.py "$tmp/conditional-site.elf" \
    tests/fixtures/direct-port-sites.tsv >"$tmp/conditional-site.log" 2>&1; then
  echo "error: conditional-only port site fixture unexpectedly passed" >&2
  exit 1
fi
grep -Fq 'error: unauthorized final-ELF port-I/O site conditional_port_path' \
  "$tmp/conditional-site.log" || {
  cat "$tmp/conditional-site.log" >&2
  echo "error: conditional-only port site fixture lacked semantic diagnostic" >&2
  exit 1
}

echo 'Direct-port final-ELF negative fixtures passed'
