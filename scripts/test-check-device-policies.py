#!/usr/bin/env python3
"""Self-test of scripts/check-device-policies.py (issue #642).

The unmodified sources pass. Each mutant below changes one C profile (or the
Lean side) in a temporary copy, and the check must reject it.

usage: test-check-device-policies.py POLICIES_FILE
"""
import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location('cdp', ROOT / 'scripts' / 'check-device-policies.py')
cdp = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cdp)

KERNEL = 'boot/kernel.c'
LAB = 'hardware/lab/qotom-wifi.c.inc'

# (description, file or None for the Lean side, old text, new text)
MUTANTS = [
    ('a dropped descriptor region (Qotom AHCI)', LAB,
     '2, { { 0, 0x0008u, 32, 32 }, { 0, 0x0880u, 120, 16 } }', '1, { { 0, 0x0008u, 32, 32 } }'),
    ('a shorter descriptor region (Qotom RTL8168)', LAB,
     '{ 0, 0x0108u, 240, 16 }', '{ 0, 0x0108u, 239, 16 }'),
    ('a TRB region typed as pointers (Qotom xHCI)', LAB,
     '{ 1, 0x20400u, 64, 16 }', '{ 0, 0x20400u, 64, 16 }'),
    ('a wider window (network source)', KERNEL,
     'network_source_profile = {\n    1, 0, 0x200u,', 'network_source_profile = {\n    1, 0, 0x400u,'),
    ('a changed address sink (Qotom RTL8168)', LAB,
     '{ 0x10, 0x20, 0x28, 0xE4 }', '{ 0x10, 0x20, 0x28, 0xE8 }'),
    ('a dropped address sink (q35 AHCI service)', KERNEL,
     '4,\n    { 0x100, 0x108, 0x180, 0x188 }, 2,', '3,\n    { 0x100, 0x108, 0x180 }, 2,'),
    ('an extra configuration-read bit (q35 xHCI service)', KERNEL,
     '1, 1, 0x4000u, UINT64_C(0x3), 0, UINT32_C(0xffff0000)',
     '1, 1, 0x4000u, UINT64_C(0x7), 0, UINT32_C(0xffff0000)'),
    ('a configuration-write bit (BCM43224)', LAB,
     '(UINT64_C(1) << (0xAC / 4))', '(UINT64_C(1) << (0xB0 / 4))'),
    ('a command mask that allows clearing Memory Space (BCM43224)', LAB,
     'UINT32_C(0xffff0004), UINT32_C(0x2), 0', 'UINT32_C(0xffff0006), UINT32_C(0x2), 0'),
    ('DMA turned on (BCM43224)', LAB,
     '{ 1, 0, 0x4000u, UINT64_C(0x3), (UINT64_C(1)', '{ 1, 1, 0x4000u, UINT64_C(0x3), (UINT64_C(1)'),
    ('a profile marked absent (DHCP source)', KERNEL,
     'dhcp_source_profile = {\n    1,', 'dhcp_source_profile = {\n    0,'),
    ('a nonzero sink past the count (DHCP source)', KERNEL,
     'dhcp_source_profile = {\n    1, 0, 0x200u, 0, 0, 0, 0, 0, { 0 },',
     'dhcp_source_profile = {\n    1, 0, 0x200u, 0, 0, 0, 0, 0, { 0x10 },'),
    ('a nonzero descriptor past the count (network source)', KERNEL,
     'network_source_profile = {\n    1, 0, 0x200u, 0, 0, 0, 0, 0, { 0 }, 0, { { 0, 0, 0, 0 } }',
     'network_source_profile = {\n    1, 0, 0x200u, 0, 0, 0, 0, 0, { 0 }, 0, { { 0, 0x100, 1, 8 } }'),
    ('a profile whose comment names no policy (DHCP source)', KERNEL,
     '(`q35FrameSourcePolicy`). */\nstatic const struct wifi_policy dhcp_source_profile',
     '(the frame-source policy). */\nstatic const struct wifi_policy dhcp_source_profile'),
    ('a profile whose comment names two policies (Qotom AHCI)', LAB,
     'mirrors `qotomAhciPolicy`.', 'mirrors `qotomAhciPolicy` (cf. `q35AhciPolicy`).'),
    ('the wrong policy named (Qotom AHCI mirrors the q35 one)', LAB,
     'mirrors `qotomAhciPolicy`.', 'mirrors `q35AhciPolicy`.'),
    ('a Lean policy that gained a descriptor region (Qotom RTL8168)', None,
     'descs=0:0x8:0x10:0x10,0:0x108:0xf0:0x10', 'descs=0:0x8:0x10:0x10,0:0x108:0xf0:0x10,0:0xa000:0x1:0x10'),
]


class DevicePolicyCheck(unittest.TestCase):
    policies = None

    def run_check(self, policies, sources):
        return cdp.check(policies, [str(p) for p in sources])

    def copy(self, tmp):
        out = []
        for rel in (KERNEL, LAB):
            dst = Path(tmp) / rel
            dst.parent.mkdir(parents=True, exist_ok=True)
            dst.write_text((ROOT / rel).read_text())
            out.append(dst)
        return out

    def test_sources_pass(self):
        count, errors = self.run_check(self.policies, [ROOT / KERNEL, ROOT / LAB])
        self.assertEqual(errors, [])
        # Four kernel profiles (two device-service variants, network and DHCP
        # sources) and five lab profiles.
        self.assertEqual(count, 9)

    def test_mutants_rejected(self):
        for desc, rel, old, new in MUTANTS:
            with self.subTest(desc), tempfile.TemporaryDirectory() as tmp:
                sources = self.copy(tmp)
                policies = self.policies
                if rel is None:
                    self.assertEqual(policies.count(old), 1, f'{desc}: anchor not unique')
                    policies = policies.replace(old, new)
                else:
                    path = Path(tmp) / rel
                    text = path.read_text()
                    self.assertEqual(text.count(old), 1, f'{desc}: anchor not unique in {rel}')
                    path.write_text(text.replace(old, new))
                try:
                    _, errors = self.run_check(policies, sources)
                except cdp.CheckError:
                    continue
                self.assertNotEqual(errors, [], f'{desc}: the check accepted it')


if __name__ == '__main__':
    if len(sys.argv) < 2:
        print(__doc__, file=sys.stderr)
        sys.exit(2)
    DevicePolicyCheck.policies = Path(sys.argv.pop(1)).read_text()
    unittest.main(verbosity=1)
