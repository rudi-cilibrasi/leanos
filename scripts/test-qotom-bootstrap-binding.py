#!/usr/bin/env python3
"""Replay native BSP role and root-selected topology together, without admission."""
from pathlib import Path
import json
import hashlib
import re
import runpy
import subprocess

import firmware_root_corpus as roots
import native_firmware_root_corpus as native

ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = ROOT / 'hardware/lab/observations/qotom-bootstrap-20260911'

CAPTURE_MANIFEST_SHA256 = '46726ba6ecb26f1ed25ad47c5e198d11614bce254a30d7f9cdcf4f3d865968c2'


def load():
    if hashlib.sha256((DIRECTORY / 'manifest.json').read_bytes()).hexdigest() != CAPTURE_MANIFEST_SHA256:
        raise ValueError('bootstrap capture manifest differs from pinned physical input')
    base, executing = native.load(DIRECTORY)
    cycle = DIRECTORY / 'cycle-1'
    lab = runpy.run_path(str(ROOT / 'scripts/run-qotom-recovery-lab.py'))
    protocol = lab['cpu_replay_module'](True).load_protocol(DIRECTORY / 'diagnostic-protocol.tsv')
    events = [json.loads(line) for line in (cycle / 'events.jsonl').read_text().splitlines()]
    _, raw = lab['cpu_diagnostic_bytes'](events, protocol, True)
    acpi = runpy.run_path(str(ROOT / 'scripts/check-qotom-acpi-capture.py'))
    raw, _, _ = acpi['extract'](raw, base.info)
    bootstrap = runpy.run_path(str(ROOT / 'scripts/check-qotom-bootstrap-capture.py'))
    _, observed = bootstrap['extract'](raw, protocol)
    if observed is None or observed != json.loads((cycle / 'bootstrap.json').read_text()):
        raise ValueError('bootstrap metadata differs from native serial sample')
    return base, executing, observed


def main():
    base, executing, sample = load()
    edx, available, value = sample['cpuid_edx'], sample['available'], sample['ia32_apic_base']
    mutations = roots.mutations(base)
    # Each row preserves all unmodified physical inputs and changes named fields only.
    cases = [('native', base, executing, edx, available, value, executing, '.candidate')]
    for name, cpuid, read, apic, identity, reason in (
        ('unavailable', edx, False, 0, executing, 'unavailable'),
        ('missing-msr', edx & ~0x20, True, value, executing, 'missingFeatures'),
        ('missing-apic', edx & ~0x200, True, value, executing, 'missingFeatures'),
        ('wrong-sample-id', edx, True, value, 2, 'executingIdMismatch'),
        ('not-bsp', edx, True, value & ~0x100, executing, 'notBootstrapProcessor'),
        ('apic-disabled', edx, True, value & ~0x800, executing, 'unsupportedApicState'),
        ('x2apic', edx, True, value | 0x400, executing, 'unsupportedApicState'),
        ('changed-base', edx, True, value ^ 0x1000, executing, 'unsupportedApicState'),
        ('reserved-bit', edx, True, value | 1, executing, 'unsupportedApicState'),
    ):
        cases.append((name, base, executing, cpuid, read, apic, identity, f'.pipeline (.bootstrap .{reason})'))
    for name, error in (
        ('root-duplicate-cpu', '.topology .duplicateApicId'),
        ('root-missing-cpus', '.topology .noEnabledProcessor'),
        ('root-madt-checksum', '.acpi (.completeMadt (.sdt .invalidChecksum))'),
        ('root-checksum', '.acpi (.madtSelection (.root .invalidChecksum))'),
    ):
        cases.append((name, mutations[name], executing, edx, available, value, executing,
                      f'.pipeline (.topology ({error}))'))
    cases.append(('wrong-executing-id', base, 2, edx, available, value, 2,
                  '.pipeline (.topology (.topology .wrongBsp))'))
    source = '''import LeanOS.QotomBspTopology
import LeanOS.BootMemoryMapDecoderABI
open LeanOS QotomBspTopology
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
inductive Outcome where
  | rootRejected
  | pipeline (reason : BootstrapPipelineError)
  | candidate
  deriving DecidableEq

def observe (magic infoAddress : UInt64) (info rootBytes : ByteArray)
    (rootAddress : UInt64) (addresses : Array UInt64) (tables : Array ByteArray)
    (executing : UInt64) (edx : UInt32) (available : Bool) (apicBase : UInt64)
    (sampleId : UInt32) : Outcome :=
  match BootMemoryMapDecoder.AcpiRootDecoder.decode
      { magic := magic.toNat, infoAddress := infoAddress.toNat, bytes := info.data.toList } with
  | .error _ => .rootRejected
  | .ok tags =>
    let copies := (addresses.toList.zip tables.toList).map fun (address, bytes) =>
      ({ physicalAddress := address, bytes := bytes.data.toList } : BootTopology.CopiedAcpiSdt)
    match checkBootstrapAuthoritative tags
        { physicalAddress := rootAddress, bytes := rootBytes.data.toList } copies
        (UInt32.ofNat executing.toNat)
        { cpuidEdx := edx, readAvailable := available, apicBase, executingId := sampleId } with
    | .error reason => .pipeline reason
    | .ok _ => .candidate
'''
    blobs, queries = {}, []
    for name, replay, cpu, cpuid, read, apic, identity, expected in cases:
        query = roots.lean_query(replay, cpu).replace('BootMemoryMapDecoderABI.capturedRootQuery', 'observe', 1)
        def intern(match):
            literal = match[0]
            if literal not in blobs:
                blobs[literal] = f'captureBytes{len(blobs)}'
            return blobs[literal]
        query = re.sub(r'⟨#\[[^\]]*\]⟩', intern, query)
        query += f' {cpuid} {str(read).lower()} {apic} {identity}'
        queries.append(f'-- {name}\nexample : {query} = {expected} := by native_decide\n')
    source += ''.join(f'def {name} : ByteArray := {literal}\n' for literal, name in blobs.items())
    source += ''.join(queries)
    out = ROOT / 'build/qotom-bootstrap-binding/Replay.lean'
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(source)
    subprocess.run(['lake', 'env', 'lean', str(out)], cwd=ROOT, check=True)
    print(f'PASS: {len(cases)} native bootstrap/topology binding cases')


if __name__ == '__main__':
    main()
