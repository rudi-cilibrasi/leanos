#!/usr/bin/env python3
"""Exercise lab GRUB state and hash failures against a fake fallback boot disk."""
import argparse
import hashlib
from pathlib import Path
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
                 ('unknown', 'unknown'), ('watchdog-disabled', 'watchdog-test'), ('bad-env', 'none'), ('bad-image', 'leanos-' + digest),
                 ('leanos', 'leanos-' + digest)]
        for name, request in cases:
            image = tmp / (name + '.img')
            shutil.copyfile(args.image, image)
            env = tmp / 'grubenv'
            run('grub-editenv', str(env), 'create')
            run('grub-editenv', str(env), 'set', 'request=' + request)
            if name == 'bad-env':
                env.write_bytes(b'invalid' + b'#' * 1017)
            run('mcopy', '-o', '-i', str(image) + '@@1048576', str(env), '::/boot/grub/grubenv')
            if name == 'bad-image':
                (tmp / 'bad.elf').write_bytes(b'unauthorized image')
                run('mcopy', '-o', '-i', str(image) + '@@1048576', str(tmp / 'bad.elf'),
                    '::/boot/leanos-qotom-lab.elf')
            log = tmp / (name + '.log')
            process = subprocess.Popen([
                'qemu-system-x86_64', '-machine', 'pc', '-m', '128', '-display', 'none',
                '-serial', 'file:' + str(log), '-monitor', 'none',
                '-drive', 'file=' + str(image) + ',format=raw,if=ide,index=0',
                '-drive', 'file=' + str(sentinel) + ',format=raw,if=ide,index=1'],
                stderr=subprocess.DEVNULL)
            expected = b'FINAL status=FAIL reason=dma-identity' if name == 'leanos' else b'FREEBSD-CHAIN-SENTINEL'
            deadline = time.monotonic() + 15
            try:
                while time.monotonic() < deadline:
                    if log.exists() and expected in log.read_bytes():
                        break
                    time.sleep(0.1)
                else:
                    raise AssertionError((name, log.read_bytes()))
            finally:
                process.terminate()
                process.wait(timeout=5)
            data = log.read_bytes()
            if name == 'oneshot':
                assert data.count(b'SELECT reboot-test consumed=1') == 1
            if name == 'watchdog-disabled':
                assert b'WATCHDOG-DISABLED fallback=freebsd' in data
                assert b'WATCHDOG-ARMED' not in data
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
