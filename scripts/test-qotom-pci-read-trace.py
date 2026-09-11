#!/usr/bin/env python3
"""Exercise lab PCI read evidence without granting inventory admission."""
import json
import hashlib
from pathlib import Path
import runpy
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
D = runpy.run_path(str(ROOT / 'scripts/check-qotom-pci-read-trace.py'))
PCI = runpy.run_path(str(ROOT / 'scripts/check-qotom-pci-diagnostic.py'))
CAPTURE = ROOT / 'hardware/lab/observations/qotom-acpi-pci-rejection-20260911'
PROTOCOL = PCI['load_protocol'](CAPTURE / 'diagnostic-protocol.tsv')
RAW = (CAPTURE / 'cycle-1/diagnostic.raw').read_bytes()
ADDRESS = 0x80000000 | 168 << 16 | 1 << 11 | 6 << 8


def trace(**changes):
    fields = dict(reads=43000, mismatches=0, requested=ADDRESS,
                  observed=ADDRESS, value=0, first_requested=0,
                  first_observed=0, first_value=0)
    fields.update(changes)
    return D['PREFIX'] + b' '.join(f'{key}={value}'.encode() for key, value in fields.items()) + b'\n'


def insert(record):
    position = RAW.index(PROTOCOL['PCI-SCAN'].encode())
    return RAW[:position] + record + RAW[position:]


class TraceTests(unittest.TestCase):
    def test_preserves_diagnostic_and_raw_value(self):
        raw, data = D['extract'](insert(trace()), PROTOCOL)
        self.assertEqual(raw, RAW)
        self.assertEqual(data['value'], 0)
        raw, data = D['extract'](insert(trace(mismatches=1, observed=0,
            first_requested=ADDRESS, first_observed=0, first_value=0x12345678)), PROTOCOL)
        self.assertEqual(raw, RAW)
        self.assertEqual(data['first_value'], 0x12345678)

    def test_rejects_inconsistent_or_unbounded_records(self):
        for changes in ({'reads':0}, {'reads':65777}, {'mismatches':43001},
                        {'value':1 << 32}, {'requested':1}, {'observed':0},
                        {'first_value':1}, {'mismatches':1}, {'reads':'01'}):
            with self.subTest(changes=changes), self.assertRaises(ValueError):
                D['extract'](insert(trace(**changes)), PROTOCOL)
        for raw in (RAW, insert(trace() * 2), trace() + RAW, insert(trace()[:-1])):
            with self.subTest(raw=raw), self.assertRaises(ValueError):
                D['extract'](raw, PROTOCOL)

    def test_no_scan_has_no_trace(self):
        raw = PROTOCOL['FINAL'].encode() + b' status=FAIL reason=j1900-cpu-profile\n'
        self.assertEqual(D['extract'](raw, PROTOCOL), (raw, None))
        with self.assertRaises(ValueError): D['extract'](trace() + raw, PROTOCOL)

    def test_retained_physical_mismatch(self):
        directory = ROOT / 'hardware/lab/observations/qotom-pci-cf8-mismatch-20260911'
        manifest = json.loads((directory / 'manifest.json').read_text())
        for name, digest in manifest['files'].items():
            self.assertEqual(hashlib.sha256((directory / name).read_bytes()).hexdigest(), digest, name)
        lab = runpy.run_path(str(ROOT / 'scripts/run-qotom-recovery-lab.py'))
        events = [json.loads(line) for line in (directory / 'cycle-1/events.jsonl').read_text().splitlines()]
        raw = b''.join(bytes.fromhex(event['hex']) for event in events)
        self.assertEqual(raw, (directory / 'cycle-1/serial.raw').read_bytes())
        recorded = json.loads((directory / 'cycle-1/result.json').read_text())
        result = lab['classify_cpu_protected'](events, recorded['elf_sha256'],
            directory / 'diagnostic-protocol.tsv', ROOT / 'build/j1900-cpu-host/host',
            ROOT / 'build/qotom-pci-inventory-host/host', True, True, True)
        self.assertEqual(result['pci_read_trace'], recorded['pci_read_trace'])
        self.assertEqual(result['pci_read_trace']['requested'], 0x8018e900)
        self.assertEqual(result['pci_read_trace']['observed'], 0x8000e86c)
        self.assertEqual(result['pci_read_trace']['value'], 0x82005)
        self.assertEqual(result['diagnostic']['pci_headers'], [])
        self.assertFalse(result['diagnostic']['platform_admitted'])

    def test_native_wrapper_rejects_and_preserves_first_mismatch(self):
        source = r'''
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
static uint32_t address_readback, calls;
static int pci_config_read(void *c, uint8_t b, uint8_t d, uint8_t f,
                           uint8_t o, uint32_t *v) {
    (void)c; (void)b; (void)d; (void)f; (void)o;
    if (!v) return 0;
    ++calls; *v = 0x12345678; return 1;
}
static uint32_t in32(uint16_t port) { assert(port == 0xcf8); return address_readback; }
static void serial_puts(const char *s) { fputs(s, stdout); }
static void serial_putc(char c) { putchar(c); }
static void serial_u64(uint64_t v) { printf("%llu", (unsigned long long)v); }
#define LEANOS_QOTOM_PCI_DIAGNOSTIC 1
#include "hardware/lab/qotom-pci-read-trace.c.inc"
int main(void) {
    uint32_t value;
    address_readback = 0x80000800;
    assert(lab_pci_read(0, 0, 1, 0, 0, &value));
    assert(value == 0x12345678 && calls == 1 && !lab_pci_trace.mismatches);
    address_readback = 0;
    assert(!lab_pci_read(0, 0, 2, 0, 0, &value));
    assert(value == 0x12345678 && calls == 2);
    /* Exercise a second direct adapter call to check first-trace retention.
       The real enumerator stops at the first failure (covered separately). */
    address_readback = 4;
    assert(!lab_pci_read(0, 0, 3, 0, 0, &value));
    assert(lab_pci_trace.mismatches == 2 && lab_pci_trace.reads == 3);
    assert(lab_pci_trace.first_requested == 0x80001000);
    assert(lab_pci_trace.first_observed == 0);
    assert(!lab_pci_read(0,0,0,0,0,0));
    assert(calls == 3 && lab_pci_trace.reads == 3);
    lab_report_pci_read();
}
'''
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp); (directory / 'test.c').write_text(source)
            subprocess.run(['gcc', '-std=c11', '-Wall', '-Wextra', '-Werror',
                            '-fsanitize=undefined', '-fno-sanitize-recover=all',
                            '-I', str(ROOT), str(directory / 'test.c'), '-o', str(directory / 'test')], check=True)
            output = subprocess.check_output([str(directory / 'test')])
            _, data = D['extract'](insert(output), PROTOCOL)
            self.assertEqual(data['reads'], 3)
            self.assertEqual(data['mismatches'], 2)
            self.assertEqual(data['value'], 0x12345678)

    def test_protected_capture_retains_guard(self):
        lab = runpy.run_path(str(ROOT / 'scripts/run-qotom-recovery-lab.py'))
        recorded = json.loads((CAPTURE / 'cycle-1/result.json').read_text())
        raw = (CAPTURE / 'cycle-1/serial.raw').read_bytes()
        raw = raw.replace(RAW, insert(trace()))
        final = raw.index(PROTOCOL['FINAL'].encode()); end = raw.index(b'\n', final) + 1
        events = [{'hex':raw[:end].hex(), 'elapsed':1}, {'hex':raw[end:].hex(), 'elapsed':36}]
        args = (events, recorded['elf_sha256'], CAPTURE / 'diagnostic-protocol.tsv',
                ROOT / 'build/j1900-cpu-host/host', ROOT / 'build/qotom-pci-inventory-host/host')
        result = lab['classify_cpu_protected'](*args, handoff=True, acpi=True, pci_read_trace=True)
        self.assertEqual(result['diagnostic']['terminal_reason'], 'qotom-pci-enumeration')
        self.assertEqual(result['diagnostic']['pci_headers'], [])
        self.assertFalse(result['diagnostic']['platform_admitted'])
        self.assertEqual(result['pci_read_trace']['value'], 0)
        with self.assertRaises(ValueError):
            lab['classify_cpu_protected'](*args, handoff=True, acpi=True)


if __name__ == '__main__': unittest.main()
