#!/usr/bin/env python3
"""Opt-in Qotom lab capture/reboot loop. Requires the prepared USB-first setup."""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import select
import shlex
import subprocess
import termios
import threading
import time

EXPECTED = (b'LEANOS-LAB/1 MODE qotom-reset-after-final seconds=30\n'
            b'LEANOS/10 BOOT target=x86_64-q35 subjects=2 schedule=blocking-ipc controls=wp,smep,smap\n'
            b'LEANOS/3 FINAL status=FAIL reason=dma-identity\n')
CHAIN = b'LEANOS-LAB/1 CHAIN freebsd disk='


def classify(events):
    data = b''.join(bytes.fromhex(e['hex']) for e in events)
    start = data.find(EXPECTED)
    if start < 0 or data.count(b'LEANOS/10 BOOT') != 1 or data.count(b'LEANOS/3 FINAL') != 1:
        raise ValueError('missing, changed, or duplicated lab rejection trace')
    end = start + len(EXPECTED)
    chain = data.find(CHAIN, end)
    if chain < 0:
        raise ValueError('missing subsequent FreeBSD chain marker')
    # The kernel observation closes before recovery/firmware bytes. Keep both.
    offset = 0
    terminal_time = None
    next_time = None
    for event in events:
        following = offset + len(bytes.fromhex(event['hex']))
        if offset < end <= following:
            if following != end:
                raise ValueError('post-terminal bytes without a quiet interval')
            terminal_time = event['elapsed']
        elif offset >= end and next_time is None:
            next_time = event['elapsed']
        offset = following
    if terminal_time is None or next_time is None or next_time - terminal_time < 10:
        raise ValueError('insufficient post-terminal quiet interval')
    suffix = data[end:]
    if b'LEANOS/' in suffix or b'LEANOS-LAB/1 SELECT leanos' in suffix:
        raise ValueError('unexpected kernel output during recovery')
    return {'scenario': 'expected-dma-identity-rejection', 'recovery': 'chain-observed',
            'quiet_seconds': next_time - terminal_time,
            'raw_sha256': hashlib.sha256(data).hexdigest()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--host', required=True)
    parser.add_argument('--host-key-alias', required=True)
    parser.add_argument('--ssh-prefix', default='ssh', help='argv prefix, e.g. "sshpass -e ssh"; no shell evaluation')
    parser.add_argument('--usb-serial', required=True)
    parser.add_argument('--serial-device', required=True)
    parser.add_argument('--elf', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--cycles', type=int, default=1, choices=range(1, 4))
    args = parser.parse_args()
    digest = hashlib.sha256(args.elf.read_bytes()).hexdigest()
    ssh = shlex.split(args.ssh_prefix) + ['-o', 'ConnectTimeout=3', '-o', 'StrictHostKeyChecking=yes',
                                        '-o', 'HostKeyAlias=' + args.host_key_alias, args.host]
    args.output.mkdir(parents=True, exist_ok=False)

    def remote(command, **kwargs):
        return subprocess.run(ssh + [command], capture_output=True, timeout=20, **kwargs)

    def boot_time():
        result = remote('sysctl -n kern.boottime', text=True)
        match = re.search(r'sec = (\d+)', result.stdout)
        return int(match.group(1)) if result.returncode == 0 and match else None

    for cycle in range(1, args.cycles + 1):
        before = boot_time()
        if before is None:
            raise SystemExit('FreeBSD SSH unavailable; no boot armed')
        env = args.output / 'request.env'
        subprocess.run(['grub-editenv', str(env), 'create'], check=True)
        subprocess.run(['grub-editenv', str(env), 'set', 'request=leanos-' + digest], check=True)
        # Remote names are fixed; arguments interpolated into shell are quoted.
        arm = '''set -e
cat > /var/tmp/leanos-lab-request.env
test "$(sudo -n camcontrol inquiry da0 -S)" = SERIAL
sudo -n mkdir -p /mnt/leanos-lab
sudo -n mount -t msdosfs /dev/da0s1 /mnt/leanos-lab
trap 'sudo -n umount /mnt/leanos-lab' EXIT
test "$(sha256 -q /mnt/leanos-lab/boot/leanos-qotom-lab.elf)" = DIGEST
sudo -n cp /var/tmp/leanos-lab-request.env /mnt/leanos-lab/boot/grub/grubenv
'''.replace('SERIAL', shlex.quote(args.usb_serial)).replace('DIGEST', shlex.quote(digest))
        directory = args.output / ('cycle-' + str(cycle))
        directory.mkdir()
        fd = os.open(args.serial_device, os.O_RDWR | os.O_NOCTTY | os.O_NONBLOCK)
        previous = termios.tcgetattr(fd)
        attrs = termios.tcgetattr(fd)
        attrs[0] = attrs[1] = attrs[3] = 0
        attrs[2] = termios.CLOCAL | termios.CREAD | termios.CS8
        attrs[4] = attrs[5] = termios.B38400
        attrs[6][termios.VMIN] = attrs[6][termios.VTIME] = 0
        termios.tcsetattr(fd, termios.TCSANOW, attrs)
        events, errors = [], []
        stop = threading.Event()
        started = time.monotonic()

        def capture():
            try:
                with (directory / 'serial.raw').open('wb') as raw, (directory / 'events.jsonl').open('w') as log:
                    while not stop.is_set():
                        if select.select([fd], [], [], 0.1)[0]:
                            chunk = os.read(fd, 65536)
                            if chunk:
                                if raw.tell() + len(chunk) > 1024 * 1024:
                                    raise ValueError('capture byte limit')
                                event = {'elapsed': time.monotonic() - started,
                                         'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'hex': chunk.hex()}
                                raw.write(chunk); raw.flush()
                                log.write(json.dumps(event) + '\n'); log.flush()
                                events.append(event)
            except Exception as error:
                errors.append(str(error))

        thread = threading.Thread(target=capture)
        thread.start()
        print('READY cycle=' + str(cycle), flush=True)
        after = None
        try:
            result = remote(arm, input=env.read_bytes())
            if result.returncode:
                raise ValueError('arming failed: ' + result.stderr.decode(errors='replace'))
            reboot = remote('sudo -n shutdown -r now', text=True)
            (directory / 'reboot.txt').write_text(reboot.stdout + reboot.stderr)
            if reboot.returncode:
                raise ValueError('SSH reboot request failed')
            while time.monotonic() - started < 180:
                if errors:
                    raise ValueError(errors)
                if CHAIN in b''.join(bytes.fromhex(e['hex']) for e in events):
                    after = boot_time()
                    if after is not None and after != before:
                        break
                stop.wait(2)
            else:
                raise ValueError('no verified FreeBSD recovery before timeout; manual recovery may be needed')
        finally:
            stop.set(); thread.join()
            termios.tcsetattr(fd, termios.TCSANOW, previous); os.close(fd)
        result = classify(events)
        result.update({'freebsd_boot_before': before, 'freebsd_boot_after': after,
                       'elf_sha256': digest, 'evidence_class': 'lab-recovery-experiment', 'hang_recovery': False})
        # Read consumed state only after FreeBSD has returned; do not arm again on failure.
        verify = remote('''set -e
sudo -n mount -t msdosfs -o ro /dev/da0s1 /mnt/leanos-lab
trap 'sudo -n umount /mnt/leanos-lab' EXIT
grep '^request=none$' /mnt/leanos-lab/boot/grub/grubenv
''', text=True)
        if verify.returncode:
            raise ValueError('one-shot request was not verified consumed')
        result['request_consumed'] = True
        result['recovery'] = 'freebsd-ssh-restored'
        (directory / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
        print('PASS cycle=' + str(cycle), json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
