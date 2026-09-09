#!/usr/bin/env python3
"""Exercise lab GRUB state and hash failures against a fake fallback boot disk."""
import argparse
from datetime import datetime
import hashlib
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
    args = parser.parse_args()
    boot_uuid = str(uuid.UUID(args.freebsd_boot_uuid))
    root = Path(__file__).resolve().parent.parent
    elf = root / 'build/qotom-lab/leanos-qotom-lab.elf'
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
            process = subprocess.Popen([
                'qemu-system-x86_64', '-machine', 'pc', '-m', '128', '-display', 'none',
                '-serial', 'file:' + str(log), '-monitor', 'none',
                '-rtc', 'base=' + rtc + ',clock=vm',
                '-drive', 'file=' + str(image) + ',format=raw,if=ide,index=0',
                '-drive', 'file=' + str(sentinel) + ',format=raw,if=ide,index=1'],
                stderr=subprocess.DEVNULL)
            expected = b'FINAL status=FAIL reason=dma-identity' if name == 'leanos' else b'FREEBSD-CHAIN-SENTINEL'
            if name == 'kernel-hang':
                expected = b'LEANOS-LAB/1 KERNEL-HANG stage=before-boot-record interrupts=disabled\n'
            deadline = time.monotonic() + (90 if name == 'rtc-probe' else 15)
            try:
                while time.monotonic() < deadline:
                    if log.exists() and expected in log.read_bytes():
                        break
                    time.sleep(0.1)
                else:
                    raise AssertionError((name, log.read_bytes()))
                if name == 'kernel-hang':
                    before = log.read_bytes()
                    time.sleep(2)
                    assert process.poll() is None and log.read_bytes() == before
            finally:
                process.terminate()
                process.wait(timeout=5)
            data = log.read_bytes()
            if name == 'kernel-hang':
                assert data.count(expected) == 1 and data.endswith(expected), data
                assert b'LEANOS/' not in data and b'FREEBSD-CHAIN-SENTINEL' not in data, data
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
            if name != 'leanos':
                assert record(10, 'BOOT') not in data
            else:
                assert b'LEANOS-LAB/1 MODE' in data
            run('mcopy', '-o', '-i', str(image) + '@@1048576', '::/boot/grub/grubenv', str(env))
            if name == 'bad-env':
                assert b'DISARM-FAILED fallback=freebsd' in data
            else:
                state = subprocess.check_output(['grub-editenv', str(env), 'list'], text=True)
                assert state == 'request=none\n', (name, state)
            print(name, 'PASS', flush=True)


if __name__ == '__main__':
    main()
