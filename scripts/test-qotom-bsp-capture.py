#!/usr/bin/env python3
"""Replay the source-validated Qotom capture through the topology candidate.

This is hosted model evidence, not a physical GRUB handoff or runtime admission.
"""
import importlib.util
from pathlib import Path
import subprocess
import re

import firmware_root_corpus as roots

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('firmware_corpus', ROOT / 'scripts/firmware-corpus.py')
corpus = importlib.util.module_from_spec(spec)
spec.loader.exec_module(corpus)


def main():
    cases = corpus.validate(corpus.load_manifest())
    case = next(c for c in cases if c['id'] == 'qotom-j1900-freebsd-uefi')
    directory = corpus.CORPUS / case['id']
    roots.validate_freebsd_projection(directory)
    memory = corpus.multiboot2_information(corpus.read_memmap(directory / 'memmap.tsv'))
    base = roots.from_capture(directory, memory)
    executing = int((directory / 'executing-apic-id.txt').read_text().strip(), 0)
    variants = {'root': base, **roots.mutations(base)}
    expectations = {
        'root': '.candidate',
        'root-duplicate-cpu': '.pipeline (.topology .duplicateApicId)',
        'root-missing-cpus': '.pipeline (.topology .noEnabledProcessor)',
        'root-bsp-mismatch': '.pipeline (.topology .wrongBsp)',
        'root-madt-checksum': '.pipeline (.acpi (.completeMadt (.sdt .invalidChecksum)))',
        'root-checksum': '.pipeline (.acpi (.madtSelection (.root .invalidChecksum)))',
        'root-declared-length': '.pipeline (.acpi (.madtSelection (.root .invalidLength)))',
        'root-wrong-address': f'.pipeline (.acpi (.selectedRootAddressMismatch {base.root_address} 0))',
    }
    source = '''import LeanOS.QotomBspTopology
import LeanOS.BootMemoryMapDecoderABI
open LeanOS
open QotomBspTopology
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
inductive Outcome where
  | rootRejected
  | pipeline (reason : PipelineError)
  | candidate
  deriving DecidableEq

def observe (magic infoAddress : UInt64) (info rootBytes : ByteArray)
    (rootAddress : UInt64) (addresses : Array UInt64) (tables : Array ByteArray)
    (executing : UInt64) : Outcome :=
  match BootMemoryMapDecoder.AcpiRootDecoder.decode
      { magic := magic.toNat, infoAddress := infoAddress.toNat, bytes := info.data.toList } with
  | .error _ => .rootRejected
  | .ok tags =>
    let copies := (addresses.toList.zip tables.toList).map fun (address, bytes) =>
      ({ physicalAddress := address, bytes := bytes.data.toList } : BootTopology.CopiedAcpiSdt)
    match checkAuthoritative tags
        { physicalAddress := rootAddress, bytes := rootBytes.data.toList } copies
        (UInt32.ofNat executing.toNat) with
    | .error reason => .pipeline reason
    | .ok _ => .candidate
'''
    # Intern byte arrays so every unchanged captured table has one definition.
    blobs = {}
    queries = []
    for name, expected in expectations.items():
        query = roots.lean_query(variants[name], executing).replace(
            'BootMemoryMapDecoderABI.capturedRootQuery', 'observe', 1)
        def intern(match):
            literal = match[0]
            if literal not in blobs:
                blobs[literal] = f'captureBytes{len(blobs)}'
            return blobs[literal]
        query = re.sub(r'⟨#\[[^\]]*\]⟩', intern, query)
        queries.append(f'-- {name}\nexample : {query} = {expected} := by native_decide\n')
    source += ''.join(f'def {name} : ByteArray := {literal}\n' for literal, name in blobs.items())
    source += ''.join(queries)
    out = ROOT / 'build/qotom-bsp-capture/Replay.lean'
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(source)
    subprocess.run(['lake', 'env', 'lean', str(out)], cwd=ROOT, check=True)
    print(f'PASS: {len(expectations)} source-validated captured Qotom topology cases')


if __name__ == '__main__':
    main()
