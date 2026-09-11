#!/usr/bin/env python3
"""Opt-in Qotom lab capture/reboot loop. Requires the prepared USB-first setup."""
import argparse
import datetime
import hashlib
import importlib.util
import json
import math
import os
from pathlib import Path
import re
import select
import shlex
import subprocess
import termios
import threading
import time

from qotom_lab_protocol import EXPECTED_KERNEL, record

EXPECTED = b'LEANOS-LAB/1 MODE qotom-reset-after-final seconds=30\n' + EXPECTED_KERNEL
CHAIN = b'LEANOS-LAB/1 CHAIN freebsd disk='


def watchdog_request(clock_text, prefix='watchdog-test'):
    """Use the board's verified UTC RTC convention, never the observer's clock."""
    if prefix != 'watchdog-test' and not re.fullmatch(r'watchdog-(kernel|leanos)-[0-9a-f]{64}', prefix):
        raise ValueError('invalid watchdog request prefix')
    lines = clock_text.splitlines()
    if len(lines) != 2 or lines[0] != '0':
        raise ValueError('watchdog trial requires the verified UTC CMOS convention')
    stamp = datetime.datetime.strptime(lines[1], '%Y-%m-%dT%H:%M:%S')
    if not 2026 <= stamp.year <= 2099:
        raise ValueError('implausible board clock')
    if stamp.second > 25:
        return None
    return prefix + '-' + '-'.join(map(str, (stamp.year, stamp.month, stamp.day, stamp.hour, stamp.minute)))


def classify_watchdog(events, kernel_digest=None):
    if any(b['elapsed'] < a['elapsed'] for a, b in zip(events, events[1:])):
        raise ValueError('nonmonotonic capture timestamps')
    data = b''.join(bytes.fromhex(e['hex']) for e in events)
    armed = b'LEANOS-LAB/1 WATCHDOG-ARMED ticks=120'
    accepted = b'LEANOS-LAB/1 WATCHDOG-WINDOW accepted=1'
    expired = b'LEANOS-LAB/1 WATCHDOG-WINDOW expired-or-invalid=1 fallback=freebsd'
    consumed = b'LEANOS-LAB/1 DEFAULT request=none'
    recovery = expired if expired in data else consumed
    if (any(data.count(marker) != 1 for marker in (accepted, armed, recovery, CHAIN))
            or data.count(expired) + data.count(consumed) != 1
            or not data.find(accepted) < data.find(armed) < data.find(recovery) < data.find(CHAIN)
            or any(marker in data for marker in (b'WATCHDOG-NO-RESET', b'WATCHDOG-STOP-FAILED',
                                                  b'WATCHDOG-ARM-REJECTED', b'LEANOS/'))):
        raise ValueError('missing, repeated, or failed watchdog reset/expiry trace')
    def completed_at(marker):
        end = data.find(marker) + len(marker)
        offset = 0
        for event in events:
            offset += len(bytes.fromhex(event['hex']))
            if offset >= end:
                return event['elapsed']
        raise ValueError('incomplete watchdog marker')
    delay = completed_at(recovery) - completed_at(armed)
    if not 110 <= delay <= 170:
        raise ValueError('watchdog recovery outside the expected reset interval')
    result = {'scenario': 'watchdog-loader-stall', 'recovery': 'chain-observed',
            'arm_to_recovery_boot_seconds': delay, 'loader_hang_recovery': True,
            'recovery_guard': 'expired-token' if recovery == expired else 'consumed-request',
            'kernel_hang_recovery': False, 'raw_sha256': hashlib.sha256(data).hexdigest()}
    hang = b'LEANOS-LAB/1 KERNEL-HANG stage=before-boot-record interrupts=disabled\n'
    if kernel_digest is not None:
        if not re.fullmatch(r'[0-9a-f]{64}', kernel_digest):
            raise ValueError('invalid expected kernel digest')
        # GRUB's console formatter can wrap the digest on the serial sink too.
        # Permit only line breaks inside the exact digest; keep raw bytes intact.
        digest_pattern = rb'[\r\n]*'.join(bytes([ch]) for ch in kernel_digest.encode())
        load = re.search(rb'LEANOS-LAB/1 WATCHDOG-KERNEL-LOAD[ \r\n]+sha256=' + digest_pattern + rb'(?=[\r\n])', data)
        if (data.count(hang) != 1 or load is None
                or data.count(b'WATCHDOG-KERNEL-LOAD') != 1 or b'WATCHDOG-LOAD-FAILED' in data
                or not data.find(armed) < load.start() < load.end() <= data.find(hang) < data.find(recovery)):
            raise ValueError('missing, changed, or repeated kernel hang/load marker')
        end = data.find(hang) + len(hang)
        offset = 0
        hang_time = next_time = None
        for event in events:
            following = offset + len(bytes.fromhex(event['hex']))
            if offset < end <= following:
                if following != end:
                    raise ValueError('extra bytes immediately after kernel hang marker')
                hang_time = event['elapsed']
            elif offset >= end and next_time is None:
                next_time = event['elapsed']
            offset = following
        if hang_time is None or next_time is None or next_time - hang_time < 90:
            raise ValueError('insufficient quiet after the early-kernel hang')
        result.update(scenario='watchdog-early-kernel-stall', kernel_hang_recovery=True,
                      loader_hang_recovery=False, hang_scope='before-boot-record', kernel_sha256=kernel_digest,
                      kernel_quiet_seconds=next_time - hang_time)
    elif b'KERNEL-HANG' in data or b'WATCHDOG-KERNEL-LOAD' in data:
        raise ValueError('kernel launch in a loader-only trial')
    return result


def classify_rtc(events):
    if any(b['elapsed'] < a['elapsed'] for a, b in zip(events, events[1:])):
        raise ValueError('nonmonotonic capture timestamps')
    data = b''.join(bytes.fromhex(e['hex']) for e in events)
    newline = rb'(?:\r\n|\n\r|\n)'
    pattern = (rb'LEANOS-LAB/1 RTC-BEGIN ([0-9-]+)' + newline +
               rb'LEANOS-LAB/1 RTC-CURRENT accepted=1' + newline +
               rb'LEANOS-LAB/1 RTC-END ([0-9-]+)' + newline +
               rb'LEANOS-LAB/1 RTC-EXPIRED rejected=1' + newline)
    match = re.search(pattern, data)
    if (match is None or data.count(b'LEANOS-LAB/1 RTC-') != 4
            or b'WATCHDOG-ARMED' in data or b'LEANOS/' in data
            or data.count(CHAIN) != 1 or data.find(CHAIN) < match.end()):
        raise ValueError('missing, repeated, or invalid RTC expiry probe trace')
    start, end = (datetime.datetime(*map(int, stamp.split(b'-'))) for stamp in match.groups())
    advancement = (end - start).total_seconds()
    if not 64 <= advancement <= 75:
        raise ValueError('RTC did not advance by the bounded probe interval')
    return {'scenario': 'rtc-probe', 'recovery': 'chain-observed',
            'rtc_begin': start.isoformat(), 'rtc_end': end.isoformat(),
            'rtc_advance_seconds': advancement, 'stale_token_rejected': True,
            'raw_sha256': hashlib.sha256(data).hexdigest()}


def classify(events, expected=EXPECTED, boot_record=None):
    boot_record = record(10, 'BOOT') if boot_record is None else boot_record
    if any(type(e['elapsed']) not in (int, float) or not math.isfinite(e['elapsed'])
           or e['elapsed'] < 0 for e in events):
        raise ValueError('invalid capture timestamp')
    if any(b['elapsed'] < a['elapsed'] for a, b in zip(events, events[1:])):
        raise ValueError('nonmonotonic capture timestamps')
    data = b''.join(bytes.fromhex(e['hex']) for e in events)
    start = data.find(expected)
    if start < 0 or data.count(boot_record) != 1 or data.count(record(3, 'FINAL')) != 1:
        raise ValueError('missing, changed, or duplicated lab rejection trace')
    if b'LEANOS/' in data[:start]:
        raise ValueError('unexpected kernel output before selected trace')
    end = start + len(expected)
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


def classify_protected(events, digest, expected=EXPECTED, boot_record=None):
    result = classify(events, expected, boot_record)
    data = b''.join(bytes.fromhex(e['hex']) for e in events)
    accepted = b'LEANOS-LAB/1 WATCHDOG-WINDOW accepted=1'
    armed = b'LEANOS-LAB/1 WATCHDOG-ARMED ticks=120'
    default = b'LEANOS-LAB/1 DEFAULT request=none'
    if not re.fullmatch(r'[0-9a-f]{64}', digest):
        raise ValueError('invalid protected image digest')
    pattern = rb'[\r\n]*'.join(bytes([ch]) for ch in digest.encode())
    load = re.search(rb'LEANOS-LAB/1 WATCHDOG-LEANOS-LOAD[ \r\n]+sha256=' + pattern + rb'(?=[\r\n])', data)
    if (load is None or any(data.count(marker) != 1 for marker in (accepted, armed, default, b'WATCHDOG-LEANOS-LOAD'))
            or not data.find(accepted) < data.find(armed) < load.start() < load.end() <= data.find(expected)
            or data.find(default) < data.find(expected) + len(expected)
            or any(marker in data for marker in (b'WATCHDOG-LOAD-FAILED', b'WATCHDOG-STOP-FAILED',
                                                  b'WATCHDOG-NO-RESET', b'KERNEL-HANG', b'WATCHDOG-KERNEL-LOAD'))):
        raise ValueError('missing, repeated, or failed normal watchdog launch/recovery')
    if not 30 <= result['quiet_seconds'] <= 90:
        raise ValueError('protected completion outside its observation interval')
    result['watchdog_protected'] = True
    return result


def cpu_replay_module(pci=False):
    spec = importlib.util.spec_from_file_location(
        'boot_diagnostic', Path(__file__).with_name(
            'check-qotom-pci-diagnostic.py' if pci else 'check-j1900-diagnostic.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def cpu_diagnostic_bytes(events, protocol):
    data = b''.join(bytes.fromhex(e['hex']) for e in events)
    mode = EXPECTED[:-len(EXPECTED_KERNEL)]
    if data.count(mode) != 1:
        raise ValueError('missing or repeated recovery mode record')
    start = data.find(mode) + len(mode)
    if not data.startswith(protocol['BOOT'].encode('ascii'), start):
        raise ValueError('CPU diagnostic must immediately follow recovery mode')
    final = data.find(protocol['FINAL'].encode('ascii'), start)
    end = data.find(b'\n', final) if final >= 0 else -1
    if end < 0:
        raise ValueError('missing CPU diagnostic terminal')
    raw = data[start:end + 1]
    return mode + raw, raw


def cpu_replay_inputs(protocol_path, replay, pci_replay=None):
    result = {'protocol_sha256': hashlib.sha256(Path(protocol_path).read_bytes()).hexdigest(),
            'replay_executable_sha256': hashlib.sha256(Path(replay).read_bytes()).hexdigest()}
    if pci_replay is not None:
        result['pci_replay_executable_sha256'] = hashlib.sha256(Path(pci_replay).read_bytes()).hexdigest()
    return result


def classify_cpu_protected(events, digest, protocol_path, replay, pci_replay=None):
    module = cpu_replay_module(pci_replay is not None)
    protocol = module.load_protocol(protocol_path)
    expected, raw = cpu_diagnostic_bytes(events, protocol)
    result = classify_protected(events, digest, expected, protocol['BOOT'].encode('ascii'))
    replay_paths = [Path(replay).resolve()]
    if pci_replay is not None:
        replay_paths.append(Path(pci_replay).resolve())
    diagnostic = module.classify(raw, protocol, *replay_paths)
    diagnostic.update(cpu_replay_inputs(protocol_path, replay, pci_replay))
    result.update(scenario='qotom-pci-diagnostic' if pci_replay is not None else 'j1900-cpu-diagnostic',
                  diagnostic=diagnostic)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--host', required=True)
    parser.add_argument('--host-key-alias', required=True)
    parser.add_argument('--ssh-prefix', default='ssh', help='argv prefix, e.g. "sshpass -e ssh"; no shell evaluation')
    parser.add_argument('--usb-serial', required=True)
    parser.add_argument('--serial-device', required=True)
    parser.add_argument('--elf', type=Path, required=True)
    parser.add_argument('--kernel-hang-elf', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--cycles', type=int, default=1, choices=range(1, 4))
    parser.add_argument('--scenario', choices=('leanos', 'rtc-probe', 'watchdog-test', 'watchdog-kernel', 'watchdog-leanos'), default='watchdog-leanos')
    diagnostics = parser.add_mutually_exclusive_group()
    diagnostics.add_argument('--pci-diagnostic', action='store_true',
                             help='replay CPU/MSR/PCI records; only with watchdog-leanos')
    diagnostics.add_argument('--cpu-diagnostic', action='store_true',
                             help='replay J1900 CPU/MSR records; only with watchdog-leanos')
    parser.add_argument('--diagnostic-protocol', type=Path,
                        default=Path(__file__).resolve().parents[1] / 'build/boot/serial-protocol.tsv')
    parser.add_argument('--diagnostic-replay', type=Path,
                        default=Path(__file__).resolve().parents[1] / 'build/j1900-cpu-host/host')
    parser.add_argument('--pci-replay', type=Path,
                        default=Path(__file__).resolve().parents[1] / 'build/qotom-pci-inventory-host/host')
    args = parser.parse_args()
    has_diagnostic = args.cpu_diagnostic or args.pci_diagnostic
    pci_replay = args.pci_replay if args.pci_diagnostic else None
    if has_diagnostic:
        if args.scenario != 'watchdog-leanos':
            parser.error('diagnostic capture requires --scenario watchdog-leanos')
        cpu_replay_module(args.pci_diagnostic).load_protocol(args.diagnostic_protocol)
        # Establish that the native corpus self-test runs before any SSH/arming.
        selftest = subprocess.run([str(args.diagnostic_replay.resolve())], check=True,
                                  capture_output=True, timeout=30)
        if selftest.stdout != b'Hosted generated-C J1900 CPU replay passed\n':
            parser.error('diagnostic replay did not report its corpus self-test')
        if pci_replay is not None:
            selftest = subprocess.run([str(pci_replay.resolve())], check=True,
                                      capture_output=True, timeout=30)
            if not re.fullmatch(
                    rb'Hosted Qotom PCI inventory replay passed \([1-9][0-9]* cases\)\n'
                    rb'Collected PCI snapshots passed generated inventory admission and 32 negative cases\n',
                    selftest.stdout):
                parser.error('PCI replay did not report its corpus self-test')
            if cpu_replay_module().replay_words(pci_replay.resolve(), 'inventory', [0]) != 65536:
                parser.error('PCI replay lacks the bounded inventory interface')
        diagnostic_inputs = cpu_replay_inputs(args.diagnostic_protocol, args.diagnostic_replay, pci_replay)
    digest = hashlib.sha256(args.elf.read_bytes()).hexdigest()
    if args.scenario == 'watchdog-kernel' and args.kernel_hang_elf is None:
        parser.error('--scenario watchdog-kernel requires --kernel-hang-elf')
    kernel_digest = hashlib.sha256(args.kernel_hang_elf.read_bytes()).hexdigest() if args.kernel_hang_elf else None
    ssh = shlex.split(args.ssh_prefix) + ['-o', 'ConnectTimeout=3', '-o', 'StrictHostKeyChecking=yes',
                                        '-o', 'HostKeyAlias=' + args.host_key_alias, args.host]
    args.output.mkdir(parents=True, exist_ok=False)
    if has_diagnostic:
        (args.output / 'diagnostic-protocol.tsv').write_bytes(args.diagnostic_protocol.read_bytes())
        (args.output / 'diagnostic-replay-inputs.json').write_text(
            json.dumps(diagnostic_inputs, indent=2) + '\n')

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
        request = 'leanos-' + digest if args.scenario == 'leanos' else 'rtc-probe'
        if args.scenario.startswith('watchdog-'):
            deadline = time.monotonic() + 75
            while time.monotonic() < deadline:
                clock = remote("sysctl -n machdep.wall_cmos_clock; date -u +%Y-%m-%dT%H:%M:%S", text=True)
                if clock.returncode:
                    raise ValueError('cannot read board clock; no trial armed')
                prefix = {'watchdog-test': 'watchdog-test', 'watchdog-leanos': 'watchdog-leanos-' + digest,
                          'watchdog-kernel': 'watchdog-kernel-' + (kernel_digest or '')}[args.scenario]
                request = watchdog_request(clock.stdout, prefix)
                if request is not None:
                    break
                time.sleep(2)
            else:
                raise ValueError('no sufficiently early RTC minute; no trial armed')
        subprocess.run(['grub-editenv', str(env), 'set', 'request=' + request], check=True)
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
        if args.scenario == 'watchdog-kernel':
            # Check the installed payload before writing the dated request.
            check = 'test "$(sha256 -q /mnt/leanos-lab/boot/leanos-qotom-kernel-hang.elf)" = ' + shlex.quote(kernel_digest) + '\n'
            arm = arm.replace('sudo -n cp /var/tmp/leanos-lab-request.env', check + 'sudo -n cp /var/tmp/leanos-lab-request.env')
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
            while time.monotonic() - started < (420 if args.scenario.startswith('watchdog-') else 180):
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
        # Read consumed state only after FreeBSD has returned; do not arm again on failure.
        verify = remote('''set -e
test "$(sudo -n camcontrol inquiry da0 -S)" = SERIAL
sudo -n mount -t msdosfs -o ro /dev/da0s1 /mnt/leanos-lab
trap 'sudo -n umount /mnt/leanos-lab' EXIT
grep '^request=none$' /mnt/leanos-lab/boot/grub/grubenv
sha256 /mnt/leanos-lab/boot/grub/grub.cfg
'''.replace('SERIAL', shlex.quote(args.usb_serial)), text=True)
        (directory / 'verification.txt').write_text(verify.stdout + verify.stderr)
        recovery = {'freebsd_boot_before': before, 'freebsd_boot_after': after,
                    'elf_sha256': digest, 'evidence_class': 'lab-recovery-experiment',
                    'hang_recovery': False,
                    'request_consumed': verify.returncode == 0, 'recovery': 'freebsd-ssh-restored'}
        # Preserve recovery evidence even when an unfamiliar serial format fails
        # classification. Replaying a parser fix must not require another boot.
        (directory / 'recovery.json').write_text(json.dumps(recovery, indent=2) + '\n')
        if verify.returncode:
            raise ValueError('one-shot request was not verified consumed')
        if args.scenario == 'watchdog-kernel':
            result = classify_watchdog(events, kernel_digest)
        elif args.scenario == 'watchdog-leanos':
            if has_diagnostic:
                if cpu_replay_inputs(args.diagnostic_protocol, args.diagnostic_replay, pci_replay) != diagnostic_inputs:
                    raise ValueError('diagnostic replay inputs changed during capture')
                result = classify_cpu_protected(events, digest, args.diagnostic_protocol,
                                                args.diagnostic_replay, pci_replay)
                protocol = cpu_replay_module(args.pci_diagnostic).load_protocol(args.diagnostic_protocol)
                _, raw = cpu_diagnostic_bytes(events, protocol)
                (directory / 'diagnostic.raw').write_bytes(raw)
            else:
                result = classify_protected(events, digest)
        else:
            classifier = {'leanos': classify, 'rtc-probe': classify_rtc, 'watchdog-test': classify_watchdog}[args.scenario]
            result = classifier(events)
        result.update(recovery)
        if args.scenario == 'watchdog-leanos':
            result['hang_recovery'] = True
        (directory / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
        print('PASS cycle=' + str(cycle), json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
