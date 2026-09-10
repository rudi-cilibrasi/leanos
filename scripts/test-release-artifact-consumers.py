#!/usr/bin/env python3
"""Exercise real shell consumers with injected query/verifier services.

This tests packaging and failure propagation, not emulator evidence validity.
The real evidence verifier has its own tests and full release validation.
"""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def main():
    with tempfile.TemporaryDirectory(prefix='leanos-artifact-consumers-') as directory:
        root = Path(directory)
        for path in ('scripts', 'docs', 'build/evidence', 'build/boot'):
            (root / path).mkdir(parents=True)
        for name in ('package-release.sh', 'write-reproducibility-manifest.sh'):
            shutil.copy2(ROOT / 'scripts' / name, root / 'scripts' / name)
        service = root / 'scripts/run-emulator-evidence.py'
        service.write_text('''#!/usr/bin/env python3
import os, sys
from pathlib import Path
mode = os.environ['TEST_QUERY_MODE']
operation = sys.argv[1]
with open('calls', 'a') as output:
    output.write(operation + '\\n')
if operation == 'verify':
    if mode == 'verify-failure':
        print('injected verification failure', file=sys.stderr)
        sys.exit(8)
    sys.exit(0)
if mode in ('failure', 'empty'):
    sys.exit(7 if mode == 'failure' else 0)
if mode == 'malformed':
    print('build/boot/a.elf')
    sys.exit(0)
names = ['a.elf', 'file with space.map']
if mode == 'missing':
    names[1] = 'missing.elf'
for index, name in enumerate(names):
    print(('build/boot/' + name + '\\t' + name) if operation == 'release-artifacts' else name, flush=True)
    if mode == 'partial' and index == 0:
        print('injected query failure after a row', file=sys.stderr)
        sys.exit(7)
''')
        service.chmod(0o755)
        recorder = root / 'scripts/record-tool-versions.sh'
        recorder.write_text('#!/bin/bash\nprintf "fixture toolchain\\n" > "$1"\n')
        recorder.chmod(0o755)
        for name in ('a.elf', 'file with space.map'):
            (root / 'build/boot' / name).write_text('distinct content for ' + name)
        for path in ('build/evidence/emulator-evidence.json', 'scripts/emulator-evidence-matrix.tsv',
                     'docs/release-notes.md'):
            (root / path).write_text('fixture\n')
        for args in (['init'], ['add', '.'], ['-c', 'user.name=Test', '-c',
                     'user.email=test@example.invalid', 'commit', '-m', 'fixture'], ['tag', 'v0.1.0']):
            subprocess.run(['git', *args], cwd=root, check=True, capture_output=True)

        def run(script, mode='success', *arguments):
            (root / 'calls').write_text('')
            return subprocess.run(['bash', 'scripts/' + script, *arguments], cwd=root,
                                  env=dict(os.environ, TEST_QUERY_MODE=mode, LEANOS_VERSION='0.1.0'),
                                  text=True, capture_output=True)

        package = 'package-release.sh'
        result = run(package, 'success', 'v0.1.0')
        require(result.returncode == 0, result)
        release = root / 'build/release'
        expected = {'a.elf', 'file with space.map', 'EMULATOR_EVIDENCE.json',
                    'EMULATOR_EVIDENCE_MATRIX.tsv', 'TOOLCHAIN.txt', 'RELEASE_NOTES.md', 'SHA256SUMS'}
        require({p.name for p in release.iterdir()} == expected, 'release inventory differs')
        for name in ('a.elf', 'file with space.map'):
            require((release / name).read_bytes() == (root / 'build/boot' / name).read_bytes(), name)
        subprocess.run(['sha256sum', '-c', 'SHA256SUMS'], cwd=release, check=True, capture_output=True)
        require((root / 'calls').read_text().splitlines() == ['verify', 'release-artifacts'],
                'verification must precede artifact generation')
        for mode in ('verify-failure', 'failure', 'empty', 'partial'):
            prior = {p.name: p.read_bytes() for p in release.iterdir()}
            result = run(package, mode, 'v0.1.0')
            require(result.returncode != 0, f'accepted {mode}')
            require(prior == {p.name: p.read_bytes() for p in release.iterdir()},
                    f'{mode} replaced prior release')
        for mode in ('malformed', 'missing'):
            result = run(package, mode, 'v0.1.0')
            require(result.returncode != 0 and not (release / 'SHA256SUMS').exists(), result)
            require(('malformed' if mode == 'malformed' else 'missing') in result.stderr, result)

        writer = 'write-reproducibility-manifest.sh'
        result = run(writer, 'success', '--list')
        require(result.returncode == 0 and result.stdout == 'a.elf\nfile with space.map\n', result)
        result = run(writer)
        require(result.returncode == 0, result)
        output = root / 'build/boot/REPRODUCIBILITY-SHA256SUMS'
        subprocess.run(['sha256sum', '-c', output.name], cwd=output.parent, check=True, capture_output=True)
        prior = output.read_bytes()
        for mode in ('failure', 'empty', 'partial', 'missing'):
            result = run(writer, mode)
            require(result.returncode != 0 and output.read_bytes() == prior, f'writer accepted/replaced on {mode}')
        for mode in ('failure', 'empty', 'partial'):
            result = run(writer, mode, '--list')
            require(result.returncode != 0 and not result.stdout, f'list published partial data on {mode}')
    print('Release and reproducibility consumers passed success and injected failure checks')


if __name__ == '__main__':
    main()
