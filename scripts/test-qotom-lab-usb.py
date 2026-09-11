#!/usr/bin/env python3
"""Exercise lab GRUB state and hash failures against a fake fallback boot disk."""
import argparse
from datetime import datetime
import hashlib
import json
import runpy
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import time
import uuid

from qotom_lab_protocol import record


def run(*args, **kwargs):
    return subprocess.run(list(args), check=True, stdout=subprocess.DEVNULL, **kwargs)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--image', type=Path, required=True)
    parser.add_argument('--freebsd-boot-uuid', required=True)
    parser.add_argument('--case', action='append', help='run only named cases; default runs every case')
    parser.add_argument('--kernel-hang-elf', type=Path, help='also test the deliberately stalled lab kernel')
    parser.add_argument('--pci-diagnostic', action='store_true',
                        help='test the protected PCI diagnostic image and replay its boot records')
    parser.add_argument('--handoff-capture', action='store_true')
    parser.add_argument('--acpi-capture', action='store_true')
    parser.add_argument('--pci-read-trace', action='store_true')
    parser.add_argument('--bootstrap-capture', action='store_true')
    parser.add_argument('--ecam-memory-capture', action='store_true')
    parser.add_argument('--dsdt-capture', action='store_true')
    args = parser.parse_args()
    if args.dsdt_capture and not args.acpi_capture:
        parser.error('--dsdt-capture requires --acpi-capture')
    if args.ecam_memory_capture and not args.bootstrap_capture:
        parser.error('--ecam-memory-capture requires --bootstrap-capture')
    if args.acpi_capture and not args.handoff_capture:
        parser.error('--acpi-capture requires --handoff-capture')
    if args.handoff_capture and not args.pci_diagnostic:
        parser.error('--handoff-capture requires --pci-diagnostic')
    if args.pci_read_trace and not args.pci_diagnostic:
        parser.error('--pci-read-trace requires --pci-diagnostic')
    if args.bootstrap_capture and not args.pci_diagnostic:
        parser.error('--bootstrap-capture requires --pci-diagnostic')
    boot_uuid = str(uuid.UUID(args.freebsd_boot_uuid))
    root = Path(__file__).resolve().parent.parent
    lab_directory = root / 'build' / ('qotom-pci-lab' if args.pci_diagnostic else 'qotom-lab')
    elf = lab_directory / 'leanos-qotom-lab.elf'
    output = lab_directory / 'usb-tests'
    output.mkdir(parents=True, exist_ok=True)
    report = output / 'results.json'
    report.unlink(missing_ok=True)
    results = []
    if args.pci_diagnostic:
        diagnostic = runpy.run_path(str(root / 'scripts/check-qotom-pci-diagnostic.py'))
        protocol = diagnostic['load_protocol'](root / 'build/boot/serial-protocol.tsv')
    digest = hashlib.sha256(elf.read_bytes()).hexdigest()
    with tempfile.TemporaryDirectory(prefix='qotom-grub-test-') as directory:
        tmp = Path(directory)
        sentinel = tmp / 'sentinel.img'
        with sentinel.open('wb') as stream:
            stream.truncate(16 * 1024 * 1024)
        run('sgdisk', '-n', '1:2048:+1M', '-n', '2:4096:+1M', '-u', '2:' + boot_uuid, str(sentinel))
        run('as', '--32', str(root / 'hardware/lab/chain-sentinel.S'), '-o', str(tmp / 'sentinel.o'))
        run('ld', '-m', 'elf_i386', '-Ttext', '0x7c00', '--oformat', 'binary',
            str(tmp / 'sentinel.o'), '-o', str(tmp / 'sentinel.bin'))
        code = (tmp / 'sentinel.bin').read_bytes()
        assert len(code) < 440
        with sentinel.open('r+b') as stream:
            stream.write(code)
        cases = [('default', 'none'), ('oneshot', 'reboot-test'),
                 ('rtc-probe', 'rtc-probe'),
                 ('rtc-missing-guard', 'rtc-probe'),
                 ('watchdog-expired', 'watchdog-test-2026-9-9-11-59'),
                 ('watchdog-arm-rejected', 'watchdog-test-2026-9-9-12-0'),
                 ('watchdog-missing-recipe', 'watchdog-test-2026-9-9-12-0'),
                 ('unknown', 'unknown'), ('watchdog-disabled', 'watchdog-test'), ('bad-env', 'none'), ('bad-image', 'leanos-' + digest),
                 ('leanos', 'leanos-' + digest)]
        window_cases = {
            'window-current': ('watchdog-test-2026-9-9-12-0', '2026-09-09T12:00:00', True),
            'window-stale-replay': ('watchdog-test-2026-9-9-12-0', '2026-09-09T12:02:00', False),
            'window-future': ('watchdog-test-2026-9-9-12-1', '2026-09-09T12:00:00', False),
            'window-old-date': ('watchdog-test-2025-9-9-12-0', '2026-09-09T12:00:00', False),
            'window-unbounded': ('watchdog-test', '2026-09-09T12:00:00', False),
            'window-malformed': ('watchdog-test-2026-09-09-12-00', '2026-09-09T12:00:00', False),
            'window-invalid-clock': ('watchdog-test-2000-9-9-12-0', '2000-09-09T12:00:00', False),
        }
        cases.extend((name, 'none') for name in window_cases)
        if args.kernel_hang_elf:
            cases.append(('kernel-hang', 'leanos-' + digest))
            hang_digest = hashlib.sha256(args.kernel_hang_elf.read_bytes()).hexdigest()
            for name in ('kernel-guard-hang', 'kernel-guard-bad-hash', 'kernel-guard-bad-elf', 'kernel-guard-wrong-digest'):
                cases.append((name, 'watchdog-kernel-' + hang_digest + '-2026-9-9-12-0'))
        for name in ('normal-guard-boot', 'normal-guard-bad-hash', 'normal-guard-bad-elf', 'normal-guard-wrong-digest'):
            cases.append((name, 'watchdog-leanos-' + digest + '-2026-9-9-12-0'))
        if args.case:
            unknown = set(args.case) - {name for name, _ in cases}
            if unknown:
                parser.error('unknown cases: ' + ', '.join(sorted(unknown)))
            cases = [(name, request) for name, request in cases if name in args.case]
        for name, request in cases:
            image = tmp / (name + '.img')
            shutil.copyfile(args.image, image)
            env = tmp / 'grubenv'
            run('grub-editenv', str(env), 'create')
            run('grub-editenv', str(env), 'set', 'request=' + request)
            if name == 'bad-env':
                env.write_bytes(b'invalid' + b'#' * 1017)
            run('mcopy', '-o', '-i', str(image) + '@@1048576', str(env), '::/boot/grub/grubenv')
            if name.startswith(('kernel-guard-', 'normal-guard-')):
                payload_digest = hang_digest if name.startswith('kernel-') else digest
                payload_name = 'leanos-qotom-kernel-hang.elf' if name.startswith('kernel-') else 'leanos-qotom-lab.elf'
                checksum_name = 'kernel-hang.sha256' if name.startswith('kernel-') else 'leanos.sha256'
                mock = tmp / 'watchdog-mock.cfg'
                mock.write_text('function qotom_watchdog_arm {\necho WATCHDOG-MOCK-ARM\ntrue\n}\n'
                                'function qotom_watchdog_stop {\necho WATCHDOG-MOCK-STOP\ntrue\n}\n')
                run('mcopy', '-o', '-i', str(image) + '@@1048576', str(mock), '::/boot/grub/watchdog.cfg')
                if name.endswith(('bad-hash', 'bad-elf')):
                    bad = tmp / 'bad-kernel.elf'
                    bad.write_bytes(b'not a multiboot ELF')
                    run('mcopy', '-o', '-i', str(image) + '@@1048576', str(bad), '::/boot/' + payload_name)
                if name.endswith('bad-elf'):
                    bad_digest = hashlib.sha256(bad.read_bytes()).hexdigest()
                    cfg = tmp / 'bad-kernel.cfg'
                    run('mcopy', '-o', '-i', str(image) + '@@1048576', '::/boot/grub/grub.cfg', str(cfg))
                    cfg.write_text(cfg.read_text().replace(payload_digest, bad_digest))
                    checksum = tmp / 'bad-kernel.sha256'
                    checksum.write_text(bad_digest + '  /boot/' + payload_name + '\n')
                    run('grub-editenv', str(env), 'set', 'request=' + request.replace(payload_digest, bad_digest))
                    for source, target in ((cfg, 'grub/grub.cfg'), (env, 'grub/grubenv'), (checksum, checksum_name)):
                        run('mcopy', '-o', '-i', str(image) + '@@1048576', str(source), '::/boot/' + target)
                if name.endswith('wrong-digest'):
                    run('grub-editenv', str(env), 'set', 'request=' + request.replace(payload_digest, '0' * 64))
                    run('mcopy', '-o', '-i', str(image) + '@@1048576', str(env), '::/boot/grub/grubenv')
            if name == 'kernel-hang':
                hang_digest = hashlib.sha256(args.kernel_hang_elf.read_bytes()).hexdigest()
                original = tmp / 'hang.cfg'
                run('mcopy', '-o', '-i', str(image) + '@@1048576', '::/boot/grub/grub.cfg', str(original))
                original.write_text(original.read_text().replace(digest, hang_digest))
                checksum = tmp / 'hang.sha256'
                checksum.write_text(hang_digest + '  /boot/leanos-qotom-lab.elf\n')
                run('grub-editenv', str(env), 'set', 'request=leanos-' + hang_digest)
                for source, target in ((original, 'grub/grub.cfg'), (env, 'grub/grubenv'),
                                       (checksum, 'leanos.sha256'), (args.kernel_hang_elf, 'leanos-qotom-lab.elf')):
                    run('mcopy', '-o', '-i', str(image) + '@@1048576', str(source), '::/boot/' + target)
            if name == 'rtc-missing-guard':
                run('mdel', '-i', str(image) + '@@1048576', '::/boot/grub/watchdog-window.cfg')
            if name == 'watchdog-missing-recipe':
                run('mdel', '-i', str(image) + '@@1048576', '::/boot/grub/watchdog.cfg')
            if name == 'bad-image':
                (tmp / 'bad.elf').write_bytes(b'unauthorized image')
                run('mcopy', '-o', '-i', str(image) + '@@1048576', str(tmp / 'bad.elf'),
                    '::/boot/leanos-qotom-lab.elf')
            rtc = '2026-09-09T12:00:00'
            if name in window_cases:
                token, rtc, accepted = window_cases[name]
                original = tmp / 'original.cfg'
                run('mcopy', '-o', '-i', str(image) + '@@1048576',
                    '::/boot/grub/grub.cfg', str(original))
                run('mcopy', '-o', '-i', str(image) + '@@1048576',
                    str(root / 'hardware/lab/grub-qotom-watchdog-window.cfg'),
                    '::/boot/grub/watchdog-window.cfg')
                # Run the candidate guard in actual GRUB, without I/O arming.
                # The same literal token is replayed with a later RTC above.
                prefix = (
                    'serial --unit=0 --speed=38400\nterminal_output serial\n'
                    'source ($root)/boot/grub/watchdog-window.cfg\n'
                    f'if qotom_watchdog_window "{token}"; then\n'
                    'echo WINDOW-ACCEPTED\nelse\necho WINDOW-REJECTED\nfi\n'
                )
                original.write_text(prefix + original.read_text())
                run('mcopy', '-o', '-i', str(image) + '@@1048576', str(original),
                    '::/boot/grub/grub.cfg')
            log = tmp / (name + '.log')
            cpu_args = ['-cpu', 'max,vendor=GenuineIntel,family=6,model=55,stepping=8,xsave=off,avx=off,smap=off'] if args.pci_diagnostic else []
            process = subprocess.Popen([
                'qemu-system-x86_64', '-machine', 'pc', '-m', '128', '-display', 'none',
                '-serial', 'file:' + str(log), '-monitor', 'none', *cpu_args,
                '-rtc', 'base=' + rtc + ',clock=vm',
                '-drive', 'file=' + str(image) + ',format=raw,if=ide,index=0',
                '-drive', 'file=' + str(sentinel) + ',format=raw,if=ide,index=1'],
                stderr=subprocess.DEVNULL)
            expected = b'FINAL status=FAIL reason=dma-identity' if name in ('leanos', 'normal-guard-boot') else b'FREEBSD-CHAIN-SENTINEL'
            if args.pci_diagnostic and name in ('leanos', 'normal-guard-boot'):
                expected = protocol['FINAL'].encode() + b' status=FAIL reason=qotom-platform-pending\n'
            if name in ('kernel-hang', 'kernel-guard-hang'):
                expected = b'LEANOS-LAB/1 KERNEL-HANG stage=before-boot-record interrupts=disabled\n'
            # ACPI may emit up to 196608 transport bytes at 38400 baud, 8N1
            # (3840 bytes/s). The original 15s loader allowance alone can
            # expire while a valid DSDT is still arriving. Keep a fixed bound
            # and require the same complete terminal record below.
            seconds = 90 if name == 'rtc-probe' else 15
            if args.acpi_capture and name in ('leanos', 'normal-guard-boot'):
                seconds += (196608 + 3839) // 3840
            deadline = time.monotonic() + seconds
            try:
                while time.monotonic() < deadline:
                    if log.exists() and expected in log.read_bytes():
                        break
                    time.sleep(0.1)
                else:
                    raise AssertionError((name, log.read_bytes()))
                if name in ('kernel-hang', 'kernel-guard-hang'):
                    before = log.read_bytes()
                    time.sleep(2)
                    assert process.poll() is None and log.read_bytes() == before
            finally:
                process.terminate()
                process.wait(timeout=5)
                if log.exists():
                    (output / (name + '.serial.log')).write_bytes(log.read_bytes())
            data = log.read_bytes()
            if name in ('kernel-hang', 'kernel-guard-hang'):
                assert data.count(expected) == 1 and data.endswith(expected), data
                assert b'LEANOS/' not in data and b'FREEBSD-CHAIN-SENTINEL' not in data, data
            if name.startswith(('kernel-guard-', 'normal-guard-')):
                assert b'WATCHDOG-ARMED' not in data, data
                if name.endswith('wrong-digest'):
                    assert b'WATCHDOG-MOCK-ARM' not in data and b'expired-or-invalid=1' in data, data
                else:
                    assert data.count(b'WATCHDOG-MOCK-ARM') == 1, data
                    if name not in ('kernel-guard-hang', 'normal-guard-boot'):
                        assert data.count(b'WATCHDOG-MOCK-STOP') == 1 and b'WATCHDOG-LOAD-FAILED' in data, data
            if name == 'rtc-probe':
                stamps = re.findall(rb'LEANOS-LAB/1 RTC-(?:BEGIN|END) ([0-9-]+)', data)
                assert len(stamps) == 2, data
                start, end = (datetime(*map(int, stamp.split(b'-'))) for stamp in stamps)
                assert 64 <= (end - start).total_seconds() <= 70, data
                assert b'RTC-CURRENT accepted=1' in data, data
                assert b'RTC-EXPIRED rejected=1' in data, data
                assert b'WATCHDOG-ARMED' not in data, data
            if name in window_cases:
                expected_window = b'WINDOW-ACCEPTED' if accepted else b'WINDOW-REJECTED'
                other_window = b'WINDOW-REJECTED' if accepted else b'WINDOW-ACCEPTED'
                assert expected_window in data and other_window not in data, (name, data)
                assert b'WATCHDOG-ARMED' not in data
            if name == 'oneshot':
                assert data.count(b'SELECT reboot-test consumed=1') == 1
            if name in ('default', 'oneshot'):
                assert data.count(b'DEFAULT request=none') == 1, data
            if name == 'watchdog-disabled':
                assert b'WATCHDOG-DISABLED fallback=freebsd' in data
                assert b'WATCHDOG-ARMED' not in data
            if name == 'rtc-missing-guard':
                assert b'RTC-UNAVAILABLE fallback=freebsd' in data, data
            if name.startswith('watchdog-'):
                assert b'WATCHDOG-ARMED' not in data, (name, data)
            if name == 'watchdog-expired':
                assert b'WATCHDOG-WINDOW expired-or-invalid=1' in data, data
                assert b'WATCHDOG-STATE' not in data, data
            if name in ('watchdog-arm-rejected', 'watchdog-missing-recipe'):
                assert b'WATCHDOG-WINDOW accepted=1' in data, data
            if name == 'watchdog-arm-rejected':
                assert b'WATCHDOG-ARM-REJECTED' in data, data
            if name == 'bad-image':
                assert b'HASH MISMATCH' in data and b'LOAD-FAILED' in data
            if name not in ('leanos', 'normal-guard-boot'):
                assert record(10, 'BOOT') not in data
                if args.pci_diagnostic:
                    assert protocol['BOOT'].encode() not in data
            else:
                assert b'LEANOS-LAB/1 MODE' in data
                if args.pci_diagnostic:
                    mode = b'LEANOS-LAB/1 MODE qotom-reset-after-final seconds=30\n'
                    assert data.count(mode) == 1
                    raw = data[data.index(mode) + len(mode):]
                    if args.handoff_capture:
                        handoff = runpy.run_path(str(root / 'scripts/check-qotom-handoff-capture.py'))
                        consumed, binary, metadata = handoff['parse_prefix'](raw)
                        assert metadata['status'] == 0 and metadata['tag_chain_valid']
                        (output / (name + '.multiboot2.bin')).write_bytes(binary)
                        (output / (name + '.handoff.json')).write_text(json.dumps(metadata, indent=2) + '\n')
                        raw = raw[consumed:]
                    if args.acpi_capture:
                        acpi = runpy.run_path(str(root / 'scripts/check-qotom-acpi-capture.py'))
                        raw, metadata, tables = acpi['extract'](raw, binary, dsdt=args.dsdt_capture)
                        assert metadata is not None
                        (output / (name + '.acpi')).mkdir(exist_ok=True)
                        for filename, content in tables.items():
                            (output / (name + '.acpi') / filename).write_bytes(content)
                        (output / (name + '.acpi.json')).write_text(json.dumps(metadata, indent=2) + '\n')
                    if args.ecam_memory_capture:
                        memory = runpy.run_path(str(root / 'scripts/check-qotom-ecam-memory-capture.py'))
                        raw, metadata = memory['extract'](raw, protocol)
                        (output / (name + '.ecam-memory.json')).write_text(json.dumps(metadata, indent=2) + '\n')
                    if args.bootstrap_capture:
                        bootstrap = runpy.run_path(str(root / 'scripts/check-qotom-bootstrap-capture.py'))
                        raw, metadata = bootstrap['extract'](raw, protocol)
                        if metadata is not None and (not metadata['available'] or not metadata['bsp']):
                            raise RuntimeError('QEMU did not identify executing BSP')
                        (output / (name + '.bootstrap.json')).write_text(json.dumps(metadata, indent=2) + '\n')
                    if args.pci_read_trace:
                        trace = runpy.run_path(str(root / 'scripts/check-qotom-pci-read-trace.py'))
                        raw, metadata = trace['extract'](raw, protocol)
                        assert metadata is not None and metadata['mismatches'] == 0
                        (output / (name + '.pci-read-trace.json')).write_text(json.dumps(metadata, indent=2) + '\n')
                    replay = diagnostic['classify'](raw, protocol,
                        root / 'build/j1900-cpu-host/host', root / 'build/qotom-pci-inventory-host/host')
                    assert replay['cpu_selection'] == 65536 and replay['msr_readback'] == 1
                    assert replay['pci_scan']['status'] == 0 and replay['pci_headers']
                    assert not replay['platform_admitted'] and not replay['cpl3_authorized']
                    (output / (name + '.replay.json')).write_text(json.dumps(replay, indent=2) + '\n')
            run('mcopy', '-o', '-i', str(image) + '@@1048576', '::/boot/grub/grubenv', str(env))
            if name == 'bad-env':
                assert b'DISARM-FAILED fallback=freebsd' in data
            else:
                state = subprocess.check_output(['grub-editenv', str(env), 'list'], text=True)
                assert state == 'request=none\n', (name, state)
            results.append({'case': name, 'serial_sha256': hashlib.sha256(data).hexdigest(),
                            'request_consumed': name != 'bad-env'})
            print(name, 'PASS', flush=True)
    report.write_text(json.dumps({'dsdt_capture': args.dsdt_capture, 'ecam_memory_capture': args.ecam_memory_capture, 'bootstrap_capture': args.bootstrap_capture, 'pci_read_trace': args.pci_read_trace, 'acpi_capture': args.acpi_capture, 'handoff_capture': args.handoff_capture, 'pci_diagnostic': args.pci_diagnostic,
        'usb_sha256': hashlib.sha256(args.image.read_bytes()).hexdigest(),
        'elf_sha256': digest, 'results': results}, indent=2) + '\n')


if __name__ == '__main__':
    main()
