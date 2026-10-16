#!/usr/bin/env python3
"""Build the production Qotom network image (issue #569).

The image runs the reviewed Qotom boot path end to end, with every stage of
the platform admission and the PCI trust contract (including the assigned
Broadcom variant of ADR 0027) composed in one fixed order, then the
production network profile: the WiFi driver subject, the DHCP subject and
the echo subject, each in its own address space, with frames crossing
through per-subject copy windows. It arms and reloads no watchdog, and it
halts after FINAL instead of resetting. See docs/qotom-production.md.

The flag set below is the one reviewed composition; nothing is optional.
The device program is the keyless smoke program `net-bcm-dhcp` unless
--program names another leanos-wifi-gen image (a `connect` image with
LEANOS_WIFI_NETWORK_SUBJECT=1 embeds the PMK: keep it under build/ and
never commit it).

usage: build-qotom-production.py [--program IMAGE]
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent

# The reviewed composition, in the order build-qotom-recovery-lab.py
# requires it: the captures and checks of the boot handoff, ACPI and ECAM,
# the native PCI inventory, every device quarantine stage, the final PCI
# admission and the initial trust contract, the no-SMAP control, the copy
# roots, entry integration and the blocking-IPC profile, then the device
# stream and the production network profile.
FLAGS = (
    '--mode', 'completion', '--pci-diagnostic', '--handoff-capture', '--acpi-capture',
    '--bootstrap-capture', '--ecam-memory-capture', '--dsdt-capture', '--ecam-read',
    '--native-inventory', '--bsp-topology', '--pci-capabilities', '--af-observation',
    '--ehci-capabilities', '--ehci-legacy', '--ehci-handoff', '--ehci-smi',
    '--ehci-operational', '--ehci-bme', '--xhci-capabilities', '--xhci-legacy',
    '--xhci-handoff', '--xhci-smi', '--xhci-operational', '--xhci-bme',
    '--pcie-device-observation', '--ahci-capabilities', '--ahci-port', '--ahci-interrupts',
    '--ahci-bme', '--hda-observation', '--hda-state', '--hda-bme', '--txe-status',
    '--rootport-bme', '--realtek-state', '--realtek-bme', '--pcie-pending', '--broadcom-d3',
    '--graphics-state', '--graphics-bme', '--txe-bme', '--pci-final-admission',
    '--pci-trust-contract', '--nosmap-control', '--copy-root-publication',
    '--entry-integration', '--exception-integration', '--blocking-ipc-integration',
    '--ipc-device-stream', '--production-network',
)
ELF = ROOT / 'build/qotom-production/leanos-qotom-production.elf'


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('--program', type=Path,
                        help='leanos-wifi-gen image (default: the keyless net-bcm-dhcp)')
    args = parser.parse_args()
    program = args.program
    if program is None:
        program = ROOT / 'build/net/net-bcm-dhcp.bin'
        program.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(['lake', 'build', 'leanos-wifi-gen'], cwd=ROOT, check=True)
        subprocess.run([str(ROOT / '.lake/build/bin/leanos-wifi-gen'), 'net-bcm-dhcp',
                        str(program)], cwd=ROOT, check=True)
    subprocess.run([sys.executable, str(ROOT / 'scripts/build-qotom-recovery-lab.py'),
                    '--prepared-repo', str(ROOT), *FLAGS, '--lab-program', str(program)],
                   cwd=ROOT, check=True)
    manifest = json.loads((ELF.parent / 'manifest.json').read_text())
    if not manifest.get('production_network') or manifest.get('evidence_class') != \
            'production-candidate':
        raise SystemExit('the lab builder did not produce the production profile')
    digest = hashlib.sha256(ELF.read_bytes()).hexdigest()
    print(f'{ELF}\nsha256 {digest}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
