#!/usr/bin/env python3
"""Produce identical native bootstrap inputs and pinned words for Lean and C."""
import argparse
from pathlib import Path
import re
import runpy
import firmware_root_corpus as roots

ROOT = Path(__file__).resolve().parents[1]


def normalize(out):
    out.mkdir(parents=True, exist_ok=True)
    cases = runpy.run_path(str(ROOT / 'scripts/test-qotom-bootstrap-binding.py'))['replay_cases']()
    expected = {'native': [1, 1, 0, 4, 0xfee00900, 0]}
    for name, code in [('unavailable', 1), ('missing-msr', 2), ('missing-apic', 2),
                       ('wrong-sample-id', 3), ('not-bsp', 4), ('apic-disabled', 5),
                       ('x2apic', 5), ('changed-base', 5), ('reserved-bit', 5)]:
        expected[name] = [1, 5, code, 0, 0, 0]
    expected.update({'root-duplicate-cpu': [1,4,4,0,0,0], 'root-missing-cpus': [1,4,5,0,0,0],
                     'root-madt-checksum': [1,2,43,0,0,0], 'root-checksum': [1,2,25,5,0,0],
                     'wrong-executing-id': [1,4,6,0,0,0]})
    for name, field, value, code in [('wide-cpuid',3,2**32,306),('wide-available',4,2,307),
                                    ('wide-sample-id',6,2**32,308),('wide-executing',2,2**32,304)]:
        row = list(cases[0]); row[0] = name; row[field] = value
        cases.append(tuple(row)); expected[name] = [1,2,code,0,0,0]
    if set(expected) != {case[0] for case in cases}:
        raise ValueError('bootstrap corpus expectations differ from input cases')
    blobs, proofs, driver = {}, [], ['# name\tbundle\texecuting\tcpuid\tavailable\tapic\tsample\twords']
    for name, replay, cpu, cpuid, read, apic, identity, _ in cases:
        bundle = replay.write(out / name)
        words = expected[name]
        driver.append('\t'.join(map(str, [name, bundle.resolve(), cpu, cpuid, int(read), apic, identity,
                                         ','.join(map(str, words))])))
        query = roots.lean_query(replay, cpu).replace('BootMemoryMapDecoderABI.capturedRootQuery',
                                                     'QotomBootstrapABI.query', 1)
        def intern(match):
            literal = match[0]
            if literal not in blobs: blobs[literal] = f'captureBytes{len(blobs)}'
            return blobs[literal]
        query = re.sub(r'⟨#\[[^\]]*\]⟩', intern, query)
        query += f' {cpuid} {int(read)} {apic} {identity}'
        proofs.append(f'-- {name}\nexample : [{", ".join(query + " " + str(i) for i in range(6))}] =\n'
                      f'    [{", ".join(map(str, words))}] := by native_decide\n')
    source = 'import LeanOS.QotomBootstrapABI\nopen LeanOS\nset_option maxRecDepth 8192\nset_option maxHeartbeats 2000000\n'
    source += ''.join(f'def {name} : ByteArray := {literal}\n' for literal, name in blobs.items())
    (out / 'Replay.lean').write_text(source + ''.join(proofs))
    (out / 'replay.tsv').write_text('\n'.join(driver) + '\n')
    print(f'Normalized {len(cases)} bootstrap ABI inputs / {len(cases)*6} words')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, default=ROOT / 'build/qotom-bootstrap-corpus')
    normalize(parser.parse_args().out)
