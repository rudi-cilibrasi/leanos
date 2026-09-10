#!/usr/bin/env python3
"""Inspect actual text cells and sink lifetime in a built image under QEMU TCG."""
import argparse
import importlib.util
import hashlib
import json
import os
from pathlib import Path
import socket
import subprocess
import tempfile
import time

root = Path(__file__).resolve().parent.parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('image', type=Path)
parser.add_argument('--elf', type=Path, default=root / 'build/boot/leanos.elf')
parser.add_argument('--output', type=Path, default=root / 'build/text-console/images')
args = parser.parse_args()
args.output.mkdir(parents=True, exist_ok=False)
with (args.output / 'native-replay-build.log').open('wb') as log:
    subprocess.run(['./scripts/check-j1900-cpu-host.sh', 'ordinary'], cwd=root,
                   stdout=log, stderr=subprocess.STDOUT, check=True)
inputs = {'image_sha256': hashlib.sha256(args.image.read_bytes()).hexdigest(),
          'elf_sha256': hashlib.sha256(args.elf.read_bytes()).hexdigest(),
          'source_revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip(),
          'source_dirty': bool(subprocess.check_output(['git', 'status', '--porcelain'], cwd=root)),
          'qemu': subprocess.check_output(['qemu-system-x86_64', '--version'], text=True).splitlines()[0]}
(args.output / 'inputs.json').write_text(json.dumps(inputs, indent=2) + '\n')
symbols = subprocess.check_output(['nm', '-S', '--defined-only', str(args.elf)], text=True)
entries = [line.split() for line in symbols.splitlines() if line.endswith(' early_text_console')]
assert len(entries) == 1 and int(entries[0][1], 16) == 32
state_address = int(entries[0][0], 16)
spec = importlib.util.spec_from_file_location('diagnostic', root / 'scripts/check-j1900-diagnostic.py')
diagnostic = importlib.util.module_from_spec(spec)
spec.loader.exec_module(diagnostic)
protocol = diagnostic.load_protocol(root / 'build/boot/serial-protocol.tsv')
canonical = subprocess.check_output(['bash', '-c',
    'source build/boot/serial-protocol.sh; source scripts/expectation-template.sh; corpus=build/boot/corpus.tsv; render_expectation scripts/expectations/blocking-ipc.transcript'],
    cwd=root).splitlines(keepends=True)


def qmp(path, commands):
    with socket.socket(socket.AF_UNIX) as conn:
        conn.settimeout(5)
        conn.connect(str(path))
        stream = conn.makefile('rwb')
        json.loads(stream.readline())
        for command in [{'execute': 'qmp_capabilities'}, *commands]:
            stream.write((json.dumps(command) + '\n').encode())
            stream.flush()
            while True:
                response = json.loads(stream.readline())
                if 'event' not in response:
                    assert 'error' not in response, response
                    break


def expected_cells(raw):
    # This corpus has no CR/control bytes. Split logical lines into 80-column
    # display rows, retaining the final empty row after the final newline.
    lines = []
    for line in raw.decode('ascii').split('\n'):
        lines.extend([line[i:i+80] for i in range(0, len(line), 80)] or [''])
    lines = lines[-25:]
    lines.extend([''] * (25 - len(lines)))
    return b''.join(bytes((ord(ch), 7)) for line in lines for ch in line.ljust(80))


results = []
for name, intel, display in [('intel-text', True, True), ('intel-headless', True, False),
                             ('q35-lifetime', False, True)]:
    out = args.output / name
    out.mkdir()
    raw_path = out / 'serial.raw'
    cpu = ('max,vendor=GenuineIntel,family=6,model=55,stepping=8,xsave=off,avx=off,smap=off'
           if intel else 'max,vendor=AuthenticAMD')
    final = (b'LEANOS/3 FINAL status=FAIL reason=qotom-platform-pending\n' if intel
             else canonical[-1])
    with tempfile.TemporaryDirectory(prefix='leanos-text-', dir='/tmp') as temp:
        control = Path(temp) / 'qmp.sock'
        construction = subprocess.check_output(['bash', '-c',
            'source scripts/q35-platform.sh; leanos_q35_command command qemu-system-x86_64 128 "$1" "$2"; printf "%s\\0" "${command[@]}"',
            'text-fixture', str(raw_path.resolve()), str(args.image.resolve())],
            cwd=root, env=dict(os.environ, LEANOS_QEMU_ACCELERATOR='tcg'))
        baseline = construction.decode().rstrip('\0').split('\0')
        command = []
        i = 0
        while i < len(baseline):
            if baseline[i] == '-device' and (baseline[i+1].startswith('isa-debug-exit,') or
                                             (not display and baseline[i+1].startswith('VGA,'))):
                i += 2
                continue
            if baseline[i] == '-cpu' and intel:
                command += ['-cpu', cpu]
                i += 2
                continue
            command.append(baseline[i])
            i += 1
        command += ['-qmp', 'unix:' + str(control) + ',server=on,wait=off']
        (out / 'command.json').write_text(json.dumps(command, indent=2) + '\n')
        with (out / 'qemu.log').open('wb') as log:
            process = subprocess.Popen(command, stdout=log, stderr=subprocess.STDOUT)
            try:
                deadline = time.monotonic() + 20
                while time.monotonic() < deadline:
                    raw = raw_path.read_bytes() if raw_path.exists() else b''
                    if raw.endswith(final):
                        break
                    if process.poll() is not None:
                        raise RuntimeError(name + ': QEMU exited before terminal record')
                    time.sleep(.1)
                else:
                    raise RuntimeError(name + ': terminal capture timed out')
                commands = [{'execute': 'stop'}, {'execute': 'human-monitor-command', 'arguments': {
                    'command-line': f'pmemsave {state_address:#x} 32 "{(out / "state.bin").resolve()}"'}}]
                if display:
                    commands += [{'execute': 'human-monitor-command', 'arguments': {
                        'command-line': f'pmemsave 0xb8000 4000 "{(out / "cells.bin").resolve()}"'}},
                        {'execute': 'screendump', 'arguments': {'filename': str((out / 'screen.ppm').resolve())}}]
                qmp(control, commands)
            finally:
                if process.poll() is None:
                    process.terminate()
                    try:
                        process.wait(timeout=3)
                    except subprocess.TimeoutExpired:
                        process.kill()
                        process.wait()
    state = (out / 'state.bin').read_bytes()
    assert state[28] == int(intel and display), (name, state.hex())
    if intel:
        replay = diagnostic.classify(raw, protocol, root / 'build/j1900-cpu-host/host')
        assert replay['cpu_selection'] == 65536 and replay['msr_readback'] == 1
    if display:
        shown = raw if intel else canonical[0]
        if not intel:
            assert raw.startswith(shown), name
        assert (out / 'cells.bin').read_bytes() == expected_cells(shown), name
    results.append(dict(case=name, sink_enabled=bool(state[28]), result='PASS',
                        serial_sha256=hashlib.sha256(raw).hexdigest(),
                        state_sha256=hashlib.sha256(state).hexdigest()))
    print(name + ': serial, screen cells and sink lifetime PASS')
(args.output / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
