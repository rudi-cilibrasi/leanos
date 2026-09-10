#!/usr/bin/env python3
"""Execute bounded copies and prove closure by a deliberate post-return fault."""
import hashlib
import importlib.util
import re
import tempfile
import time
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / 'build/copy-roots' / ('transfer-qemu-' + Path(os.environ.get('LEANOS_CC', 'gcc')).name)


def observe_rejection(command, directory, capture, elf, direction, fault=False, cleanup_failure=False, nmi=False):
    spec = importlib.util.spec_from_file_location('reload_test', ROOT / 'scripts/test-copy-root-reload-qemu.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    symbols = {}
    for line in subprocess.check_output(['nm', '-S', str(elf)], text=True).splitlines():
        fields = line.split()
        if len(fields) in (3, 4):
            symbols[fields[-1]] = (int(fields[0], 16), int(fields[1], 16) if len(fields) == 4 else 0)
    terminal, size = symbols['leanos_copy_root_terminal']
    expected_root = symbols['root_a' if cleanup_failure else 'root_b'][0]
    with tempfile.TemporaryDirectory(prefix='leanos-transfer-', dir='/tmp') as temp:
        monitor = Path(temp) / 'qmp.sock'
        command = command + ['-qmp', f'unix:{monitor},server=on,wait=off']
        (directory / 'command.json').write_text(json.dumps(command, indent=2)+'\n')
        with (directory / 'qemu.log').open('w') as log:
            process = subprocess.Popen(command, stdout=log, stderr=subprocess.STDOUT)
            try:
                deadline = time.monotonic() + 20
                injected_nmi = False
                while True:
                    raw = capture.read_bytes() if capture.exists() else b''
                    if process.poll() is not None or time.monotonic() >= deadline:
                        raise RuntimeError(f'transfer did not halt: {process.poll()}, {raw!r}')
                    if nmi and not injected_nmi and raw == b'RW' and monitor.exists():
                        registers = module.qmp_command(monitor)
                        rip = re.search(r'RIP=([0-9a-fA-F]+)', registers)
                        begin = symbols['leanos_copy_transfer_nmi_wait'][0]
                        end = symbols['leanos_copy_transfer_nmi_wait_end'][0]
                        if rip and begin <= int(rip[1], 16) < end and 'HLT=1' in registers:
                            module.qmp_command(monitor, {'execute': 'inject-nmi'})
                            injected_nmi = True
                    if raw == (b'RWN' if nmi else b'RX' if fault else b'R') and monitor.exists():
                        registers = module.qmp_command(monitor)
                        rip = re.search(r'RIP=([0-9a-fA-F]+)', registers)
                        cr3 = re.search(r'CR3=([0-9a-fA-F]+)', registers)
                        if rip and terminal <= int(rip[1], 16) < terminal + size and 'HLT=1' in registers:
                            if not cr3 or int(cr3[1], 16) != expected_root:
                                raise RuntimeError('transfer halted under an unexpected root')
                            if nmi and not injected_nmi:
                                raise RuntimeError('NMI terminal preceded the requested injection')
                            if nmi:
                                rsp = re.search(r'RSP=([0-9a-fA-F]+)', registers)
                                if not rsp or int(rsp[1], 16) != symbols['nmi_stack_top'][0] - 40:
                                    raise RuntimeError('NMI did not retain its dedicated IST frame')
                            (directory / 'terminal-registers.txt').write_text(registers)
                            break
                    time.sleep(0.05)
                pattern = bytes(range(0x10, 0x20))
                prefix = 16 if cleanup_failure else 8 if fault or nmi else 0
                expected_kernel = bytearray([0xa5])*32
                expected_user = bytearray([0xa5])*32
                if direction:
                    expected_kernel[8:24] = pattern
                    expected_user[8:8+prefix] = pattern[:prefix]
                else:
                    expected_user[8:24] = pattern
                    expected_kernel[8:8+prefix] = pattern[:prefix]
                hashes = {}
                for name, address, expected in (
                    ('kernel', symbols['transfer_buffer'][0], expected_kernel),
                    ('user', symbols['value_a'][0]+4080, expected_user),
                ):
                    dump = directory / (name + '-after.bin')
                    dump.unlink(missing_ok=True)
                    response = module.qmp_command(monitor, {'execute': 'human-monitor-command',
                        'arguments': {'command-line': f'pmemsave {address:#x} 32 {json.dumps(str(dump))}'}})
                    if response.strip():
                        raise RuntimeError(f'physical dump failed: {response}')
                    actual = dump.read_bytes()
                    if actual != expected:
                        raise RuntimeError(f'transfer changed unexpected {name} bytes: {actual.hex()}')
                    hashes[name] = hashlib.sha256(actual).hexdigest()
                if nmi:
                    # Inspect both roots independently of the guest assertions.
                    for root in ('a', 'b'):
                        for guard in ('nmi_guard_low', 'nmi_guard_high', 'nmi_stack'):
                            address = symbols['leaves_' + root][0] + (symbols[guard][0] >> 12) * 8
                            dump = directory / (root + '-' + guard + '.bin')
                            dump.unlink(missing_ok=True)
                            response = module.qmp_command(monitor, {'execute': 'human-monitor-command',
                                'arguments': {'command-line': f'pmemsave {address:#x} 8 {json.dumps(str(dump))}'}})
                            if response.strip():
                                raise RuntimeError(f'PTE dump failed: {response}')
                            data = dump.read_bytes()
                            if len(data) != 8:
                                raise RuntimeError('short IST PTE dump')
                            pte = int.from_bytes(data, 'little')
                            expected = (symbols[guard][0] | 3 | (1 << 63)) if guard == 'nmi_stack' else 0
                            # Hardware may set accessed/dirty bits on the stack.
                            if pte & ~0x60 != expected:
                                raise RuntimeError(f'bad IST mapping {root}/{guard}: {pte:#x}')
                return {'kind': 'terminal', 'halted': True, 'root': expected_root, 'closed': not cleanup_failure, 'memory_sha256': hashes, 'completed_prefix': prefix, 'injected_nmi': injected_nmi, 'dedicated_ist': nmi}
            finally:
                process.terminate()
                try:
                    process.wait(timeout=2)
                except subprocess.TimeoutExpired:
                    process.kill()
                    process.wait()


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    report = OUT / 'results.json'
    report.unlink(missing_ok=True)
    cc = os.environ.get('LEANOS_CC', 'gcc')
    objects = []
    for name in ('reload', 'transfer'):
        obj = OUT / (name + '.o')
        subprocess.run([cc, '-m64', '-c', f'experiments/copy-roots/{name}.S', '-o', str(obj)], cwd=ROOT, check=True)
        objects.append(str(obj))
    constructor = OUT / 'construct-fixture.o'
    subprocess.run([cc, '-m64', '-std=c11', '-O1', '-Wall', '-Wextra', '-Werror',
                    '-ffreestanding', '-fno-stack-protector', '-fno-pie', '-mno-red-zone',
                    '-mgeneral-regs-only', '-fno-asynchronous-unwind-tables', '-c',
                    'experiments/copy-roots/construct-fixture.c', '-o', str(constructor)], cwd=ROOT, check=True)
    planner = OUT / 'operands-fixture.o'
    subprocess.run([cc, '-m64', '-std=c11', '-O1', '-Wall', '-Wextra', '-Werror',
                    '-ffreestanding', '-fno-stack-protector', '-fno-pie', '-mno-red-zone',
                    '-mgeneral-regs-only', '-fno-asynchronous-unwind-tables', '-c',
                    'experiments/copy-roots/operands-fixture.c', '-o', str(planner)], cwd=ROOT, check=True)
    host_test = OUT / 'operands-test'
    subprocess.run([cc, '-std=c11', '-O2', '-Wall', '-Wextra', '-Werror',
                    'experiments/copy-roots/operands-test.c', '-o', str(host_test)], cwd=ROOT, check=True)
    subprocess.run([str(host_test)], check=True)
    mutation = OUT / 'cleanup-failure.S'
    source = (ROOT / 'experiments/copy-roots/transfer.S').read_text()
    needle = '    mov %r12, %rdi'
    if source.count(needle) != 1:
        raise RuntimeError('cleanup operand mutation must target exactly one instruction')
    mutation.write_text(source.replace(needle, '    xor %edi, %edi'))
    cleanup_object = OUT / 'cleanup-failure.o'
    subprocess.run([cc, '-m64', '-c', str(mutation), '-o', str(cleanup_object)], check=True)
    nmi_source = OUT / 'nmi-transfer.S'
    checkpoint = '    inc %rbx'
    if source.count(checkpoint) != 1:
        raise RuntimeError('NMI checkpoint must target one completed byte increment')
    nmi_source.write_text(source.replace(checkpoint, checkpoint + """
    cmp $8, %rbx
    jne .Lnmi_continue
    push %rax
    mov $'W', %al
    out %al, $0xe9
    pop %rax
.global leanos_copy_transfer_nmi_wait
leanos_copy_transfer_nmi_wait:
    hlt
    jmp leanos_copy_transfer_nmi_wait
.global leanos_copy_transfer_nmi_wait_end
leanos_copy_transfer_nmi_wait_end:
.Lnmi_continue:
"""))
    nmi_object = OUT / 'nmi-transfer.o'
    subprocess.run([cc, '-m64', '-c', str(nmi_source), '-o', str(nmi_object)], check=True)
    results = []
    cases = ([(d, n, False, False, False) for d in (0, 1) for n in (0, 1, 8, 16, 17)]
             + [(d, 16, True, False, False) for d in (0, 1)]
             + [(d, 16, False, True, False) for d in (0, 1)]
             + [(d, 16, False, False, True) for d in (0, 1)])
    cases = [(*case, 0) for case in cases] + [
        (d, 16, False, False, False, root) for d in (0, 1) for root in (1, 2, 3)]
    for direction, count, fault, cleanup_failure, nmi, invalid_root in cases:
        directory = OUT / (f'{direction}-{count}' + ('-fault' if fault else '-cleanup' if cleanup_failure else '-nmi' if nmi else f'-root-{invalid_root}' if invalid_root else ''))
        grub = directory / 'iso/boot/grub'
        grub.mkdir(parents=True, exist_ok=True)
        elf = grub.parent / 'test.elf'
        obj = directory / 'fixture.o'
        subprocess.run([cc, '-m64', '-DFIXTURE=7', '-DTRANSFER_FIXTURE', '-DCONSTRUCT_FIXTURE', f'-DTRANSFER_COUNT={count}', f'-DCOPY_OUT={direction}', f'-DTRANSFER_FAULT={int(fault)}', f'-DTRANSFER_NMI={int(nmi)}', f'-DINVALID_COPY_ROOT={invalid_root}',
                        '-c', 'experiments/copy-roots/fixture.S', '-o', str(obj)], cwd=ROOT, check=True)
        linked_objects = [objects[0], str(cleanup_object) if cleanup_failure else str(nmi_object) if nmi else objects[1]]
        subprocess.run(['ld', '-nostdlib', '--build-id=none', '-T', 'experiments/copy-roots/fixture.ld',
                        '-o', str(elf), str(obj), *linked_objects, str(constructor), str(planner)], cwd=ROOT, check=True)
        if not cleanup_failure and not nmi:
            subprocess.run(['python3', str(ROOT / 'scripts/check-copy-root-transfer.py'), str(elf)], check=True)
        (grub / 'grub.cfg').write_text('set timeout=0\nmenuentry "copy transfer" {\n multiboot2 /boot/test.elf\n boot\n}\n')
        iso = directory / 'fixture.iso'
        with (directory / 'grub.log').open('w') as log:
            subprocess.run(['grub-mkrescue', '-o', str(iso), str(grub.parent.parent)], stdout=log, stderr=subprocess.STDOUT, check=True)
        capture = directory / 'debug.log'
        capture.unlink(missing_ok=True)
        command = ['qemu-system-x86_64', '-machine', 'q35,accel=tcg', '-cpu', 'max,smap=off',
                   '-m', '128', '-smp', '1', '-display', 'none', '-serial', 'none', '-monitor', 'none', '-nic', 'none',
                   '-debugcon', f'file:{capture}', '-device', 'isa-debug-exit,iobase=0xf4,iosize=4',
                   '-no-reboot', '-cdrom', str(iso)]
        (directory / 'command.json').write_text(json.dumps(command, indent=2)+'\n')
        if count > 16 or fault or cleanup_failure or nmi or invalid_root:
            observation = observe_rejection(command, directory, capture, elf, direction, fault, cleanup_failure, nmi)
        else:
            with (directory / 'qemu.log').open('w') as log:
                result = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT, timeout=20)
            raw = capture.read_bytes()
            if result.returncode != 33 or raw != b'RTP':
                raise RuntimeError(f'count {count}: exit {result.returncode}, capture {raw!r}')
            observation = {'kind': 'exit', 'exit': result.returncode}
        results.append({'direction': 'out' if direction else 'in', 'count': count, 'fault': fault, 'cleanup_failure': cleanup_failure, 'nmi': nmi, 'invalid_root': invalid_root,
                        'observation': observation, 'capture': capture.read_text(),
                        'elf_sha256': hashlib.sha256(elf.read_bytes()).hexdigest(),
                        'transfer_object_sha256': hashlib.sha256(Path(linked_objects[1]).read_bytes()).hexdigest(),
                        'planner_object_sha256': hashlib.sha256(planner.read_bytes()).hexdigest(),
                        'constructor_object_sha256': hashlib.sha256(constructor.read_bytes()).hexdigest()})
        print(f'copy-root transfer direction={direction} {count} bytes fault={fault} cleanup_failure={cleanup_failure} nmi={nmi} invalid_root={invalid_root}: PASS', flush=True)
    sources = ['experiments/copy-roots/'+name for name in ('fixture.S', 'fixture.ld', 'transfer-fixture.inc', 'reload.S', 'transfer.S', 'construct-fixture.c', 'construct.h', 'operands-fixture.c', 'operands.h')]
    report.write_text(json.dumps({'scope': 'isolated no-SMAP TCG copy-in/copy-out, post-return closure and terminal partial faults; no production admission',
        'cases': results, 'driver_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), 'sources': {p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sources},
        'compiler': subprocess.check_output([cc, '--version'], text=True),
        'qemu': subprocess.check_output(['qemu-system-x86_64', '--version'], text=True)}, indent=2)+'\n')


if __name__ == '__main__':
    main()
