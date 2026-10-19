#!/usr/bin/env python3
"""Negative fixtures for the separate lab recovery trace classifier."""
import importlib.util
import hashlib
import json
import re
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location('lab', Path(__file__).with_name('run-qotom-recovery-lab.py'))
lab = importlib.util.module_from_spec(spec)
spec.loader.exec_module(lab)


def event(data, elapsed):
    return {'hex': data.hex(), 'elapsed': elapsed}


class CaptureTests(unittest.TestCase):
    def test_retained_protected_cycles(self):
        root = Path(__file__).resolve().parent.parent / 'hardware/lab/observations/qotom-protected-normal-20260909'
        manifest = json.loads((root / 'manifest.json').read_text())
        for name, digest in manifest['files'].items():
            self.assertEqual(hashlib.sha256((root / name).read_bytes()).hexdigest(), digest, name)
        previous = None
        for cycle in sorted(root.glob('cycle-*')):
            recorded = json.loads((cycle / 'result.json').read_text())
            events = [json.loads(line) for line in (cycle / 'events.jsonl').read_text().splitlines()]
            self.assertEqual((cycle / 'serial.raw').read_bytes(), b''.join(bytes.fromhex(e['hex']) for e in events))
            for key, value in lab.classify_protected(events, recorded['elf_sha256']).items():
                if key != 'recovery':
                    self.assertEqual(value, recorded[key], key)
            self.assertTrue(recorded['request_consumed'] and recorded['hang_recovery'])
            self.assertNotEqual(recorded['freebsd_boot_before'], recorded['freebsd_boot_after'])
            if previous is not None:
                self.assertEqual(previous, recorded['freebsd_boot_before'])
            previous = recorded['freebsd_boot_after']
        self.assertEqual(len(list(root.glob('cycle-*'))), 3)

    def test_protected_normal_capture(self):
        digest = 'a' * 64
        prefix = (b'LEANOS-LAB/1 WATCHDOG-WINDOW accepted=1\n'
                  b'LEANOS-LAB/1 WATCHDOG-ARMED ticks=120\n'
                  b'LEANOS-LAB/1 WATCHDOG-LEANOS-LOAD\n\rsha256=' + b'a' * 30 + b'\n\r' + b'a' * 34 + b'\n')
        default = b'LEANOS-LAB/1 DEFAULT request=none\n'
        valid = [event(prefix, 1), event(lab.EXPECTED, 3), event(b'firmware\n', 37), event(default + lab.CHAIN, 38)]
        self.assertTrue(lab.classify_protected(valid, digest)['watchdog_protected'])
        for bad in (valid[1:], valid + [event(prefix, 39)],
                    [event(prefix.replace(b'ARMED ticks=120', b'ARM-REJECTED'), 1), *valid[1:]],
                    [*valid[:2], event(b'firmware', 120), event(default + lab.CHAIN, 125)],
                    [*valid[:3], event(lab.CHAIN, 38)], valid + [event(b'WATCHDOG-LOAD-FAILED', 39)],
                    [valid[0], event(lab.EXPECTED.replace(b'dma-identity', b'other'), 3), *valid[2:]]):
            with self.subTest(events=bad), self.assertRaises(ValueError):
                lab.classify_protected(bad, digest)
        with self.assertRaises(ValueError):
            lab.classify_protected(valid, 'b' * 64)

    def test_retained_kernel_watchdog(self):
        root = Path(__file__).resolve().parent.parent / 'hardware/lab/observations/qotom-kernel-watchdog-20260909'
        manifest = json.loads((root / 'manifest.json').read_text())
        for name, digest in manifest['files'].items():
            self.assertEqual(hashlib.sha256((root / name).read_bytes()).hexdigest(), digest, name)
        events = [json.loads(line) for line in (root / 'events.jsonl').read_text().splitlines()]
        self.assertEqual((root / 'serial.raw').read_bytes(), b''.join(bytes.fromhex(e['hex']) for e in events))
        recorded = json.loads((root / 'result.json').read_text())
        for key, value in lab.classify_watchdog(events, recorded['kernel_sha256']).items():
            if key != 'recovery':
                self.assertEqual(value, recorded[key], key)
        self.assertNotEqual(recorded['freebsd_boot_before'], recorded['freebsd_boot_after'])
        self.assertTrue(recorded['request_consumed'])
        self.assertTrue(recorded['kernel_hang_recovery'])

    def test_kernel_watchdog_capture(self):
        digest = 'a' * 64
        accepted = b'LEANOS-LAB/1 WATCHDOG-WINDOW accepted=1\n'
        armed = b'LEANOS-LAB/1 WATCHDOG-ARMED ticks=120\n'
        load = b'LEANOS-LAB/1 WATCHDOG-KERNEL-LOAD sha256=' + digest.encode() + b'\n'
        hang = b'LEANOS-LAB/1 KERNEL-HANG stage=before-boot-record interrupts=disabled\n'
        recovery = b'LEANOS-LAB/1 DEFAULT request=none\n' + lab.CHAIN
        valid = [event(accepted + armed, 14), event(load + hang, 16), event(b'firmware', 135), event(recovery, 142)]
        result = lab.classify_watchdog(valid, digest)
        self.assertTrue(result['kernel_hang_recovery'])
        self.assertEqual(result['kernel_quiet_seconds'], 119)
        wrapped = load.replace(b' sha256=', b'\n\rsha256=').replace(digest.encode(), b'a' * 30 + b'\n\r' + b'a' * 34)
        self.assertTrue(lab.classify_watchdog([valid[0], event(wrapped + hang, 16), *valid[2:]], digest)['kernel_hang_recovery'])
        self.assertEqual(lab.watchdog_request('0\n2026-09-09T20:05:00\n', 'watchdog-kernel-' + digest),
                         'watchdog-kernel-' + digest + '-2026-9-9-20-5')
        for bad in (valid[:1] + valid[2:], valid + [event(hang, 150)],
                    [valid[0], event(load + hang + b'extra', 16), *valid[2:]],
                    [*valid[:2], event(b'extra', 20), *valid[2:]],
                    [valid[0], event(load.replace(digest.encode(), b'b' * 64) + hang, 16), *valid[2:]]):
            with self.subTest(events=bad), self.assertRaises(ValueError):
                lab.classify_watchdog(bad, digest)
        with self.assertRaises(ValueError):
            lab.classify_watchdog(valid)

    def test_retained_loader_watchdog(self):
        root = Path(__file__).resolve().parent.parent / 'hardware/lab/observations/qotom-dated-watchdog-20260909'
        manifest = json.loads((root / 'manifest.json').read_text())
        for name, digest in manifest['files'].items():
            self.assertEqual(hashlib.sha256((root / name).read_bytes()).hexdigest(), digest, name)
        events = [json.loads(line) for line in (root / 'events.jsonl').read_text().splitlines()]
        self.assertEqual((root / 'serial.raw').read_bytes(), b''.join(bytes.fromhex(e['hex']) for e in events))
        recorded = json.loads((root / 'result.json').read_text())
        for key, value in lab.classify_watchdog(events).items():
            if key != 'recovery':
                self.assertEqual(value, recorded[key], key)
        self.assertNotEqual(recorded['freebsd_boot_before'], recorded['freebsd_boot_after'])
        self.assertTrue(recorded['request_consumed'])
        self.assertFalse(recorded['kernel_hang_recovery'])

    def test_watchdog_request_clock(self):
        self.assertEqual(lab.watchdog_request('0\n2026-09-09T20:05:25\n'), 'watchdog-test-2026-9-9-20-5')
        self.assertIsNone(lab.watchdog_request('0\n2026-09-09T20:05:26\n'))
        for clock in ('1\n2026-09-09T20:05:00\n', '0\n2000-09-09T20:05:00\n',
                      '0\ninvalid\n', '0\n2026-09-09T20:05:00\nextra\n'):
            with self.subTest(clock=clock), self.assertRaises(ValueError):
                lab.watchdog_request(clock)

    def test_watchdog_reset_classification(self):
        accepted = b'LEANOS-LAB/1 WATCHDOG-WINDOW accepted=1\n\r'
        armed = b'LEANOS-LAB/1 WATCHDOG-ARMED ticks=120\n\r'
        expired = b'LEANOS-LAB/1 WATCHDOG-WINDOW expired-or-invalid=1 fallback=freebsd\n\r'
        valid = [event(accepted + armed, 14), event(b'firmware\n', 135),
                 event(expired + lab.CHAIN + b'hd1\n\r', 142)]
        result = lab.classify_watchdog(valid)
        self.assertEqual(result['arm_to_recovery_boot_seconds'], 128)
        self.assertEqual(result['recovery_guard'], 'expired-token')
        consumed = [*valid[:2], event(b'LEANOS-LAB/1 DEFAULT request=none\n' + lab.CHAIN, 142)]
        self.assertEqual(lab.classify_watchdog(consumed)['recovery_guard'], 'consumed-request')
        self.assertTrue(result['loader_hang_recovery'])
        self.assertFalse(result['kernel_hang_recovery'])
        mutations = [valid[:2], valid + [event(armed, 145)],
                     valid[:2] + [event(expired + lab.CHAIN, 30)],
                     valid[:2] + [event(expired + lab.CHAIN, 320)],
                     valid + [event(b'WATCHDOG-NO-RESET', 150)],
                     valid + [event(lab.EXPECTED, 150)],
                     [event(expired + lab.CHAIN, 1), event(accepted + armed, 14)],
                     [valid[0], event(b'firmware\n', 1), valid[2]]]
        for events in mutations:
            with self.subTest(events=events), self.assertRaises(ValueError):
                lab.classify_watchdog(events)

    def test_rtc_probe_and_failures(self):
        raw = (b'LEANOS-LAB/1 RTC-BEGIN 2026-9-9-23-59-30\r\n'
               b'LEANOS-LAB/1 RTC-CURRENT accepted=1\r\n'
               b'LEANOS-LAB/1 RTC-END 2026-9-10-0-0-35\r\n'
               b'LEANOS-LAB/1 RTC-EXPIRED rejected=1\r\n' + lab.CHAIN + b'hd1\r\n')
        self.assertEqual(lab.classify_rtc([event(raw, 80)])['rtc_advance_seconds'], 65)
        for newline in (b'\n', b'\n\r'):
            self.assertEqual(lab.classify_rtc([event(raw.replace(b'\r\n', newline), 80)])['rtc_advance_seconds'], 65)
        for bad in (raw + raw, raw.replace(b'accepted=1', b'accepted=0'),
                    raw.replace(b'rejected=1', b'rejected=0'),
                    raw.replace(b'2026-9-10-0-0-35', b'2026-9-9-23-59-30'),
                    raw.replace(b'2026-9-10-0-0-35', b'2026-9-10-0-0-50'),
                    raw.replace(lab.CHAIN, b'no-chain'),
                    raw + b'WATCHDOG-ARMED', raw + lab.EXPECTED,
                    lab.CHAIN + b'hd1\n' + raw.split(lab.CHAIN)[0]):
            with self.subTest(raw=bad), self.assertRaises(ValueError):
                lab.classify_rtc([event(bad, 80)])

    def fixture(self):
        return [event(b'firmware\n', 1), event(lab.EXPECTED[:40], 2),
                event(lab.EXPECTED[40:], 3), event(b'firmware\n', 37),
                event(lab.CHAIN + b'hd1\n', 38)]

    def test_complete_recovery(self):
        result = lab.classify(self.fixture())
        self.assertEqual(result['quiet_seconds'], 34)
        self.assertEqual(result['scenario'], 'expected-dma-identity-rejection')

    def test_retained_physical_observations(self):
        root = Path(__file__).resolve().parent.parent / 'hardware/lab/observations/qotom-20260909'
        manifest = json.loads((root / 'manifest.json').read_text())
        for name, digest in manifest['files'].items():
            self.assertEqual(hashlib.sha256((root / name).read_bytes()).hexdigest(), digest, name)
        cycles = sorted(root.glob('cycle-*'))
        self.assertEqual(len(cycles), 3)
        for cycle in cycles:
            events = [json.loads(line) for line in (cycle / 'events.jsonl').read_text().splitlines()]
            raw = (cycle / 'serial.raw').read_bytes()
            self.assertEqual(raw, b''.join(bytes.fromhex(e['hex']) for e in events))
            computed = lab.classify(events)
            recorded = json.loads((cycle / 'result.json').read_text())
            for key in ('scenario', 'quiet_seconds', 'raw_sha256'):
                self.assertEqual(computed[key], recorded[key])
            self.assertNotEqual(recorded['freebsd_boot_before'], recorded['freebsd_boot_after'])
            self.assertTrue(recorded['request_consumed'])
            self.assertFalse(recorded['hang_recovery'])

    def test_failure_mutations(self):
        valid = self.fixture()
        mutations = {
            'earlier kernel output': [event(lab.record(4, 'PROBE') + b' unexpected\n', 0)] + valid,
            'nonmonotonic time': valid[:3] + [event(b'firmware\n', 2), valid[-1]],
            'wrong reason': [event(lab.EXPECTED.replace(b'dma-identity', b'other'), 3)] + valid[3:],
            'false success': [event(lab.EXPECTED.replace(b'status=FAIL', b'status=PASS'), 3)] + valid[3:],
            'partial trace': [event(lab.EXPECTED[:-2], 3)] + valid[3:],
            'extra terminal': valid[:3] + [event(lab.record(3, 'FINAL') + b' status=PASS\n', 4)] + valid[3:],
            'early reboot': valid[:3] + [event(b'firmware\n', 4), valid[-1]],
            'extra same chunk': [event(lab.EXPECTED + b'extra', 3)] + valid[3:],
            'missing chain': valid[:-1],
            'boot loop': valid + [event(b'LEANOS-LAB/1 SELECT leanos consumed=1\n', 40)],
            'post-terminal kernel output': valid + [event(lab.record(4, 'PROBE') + b' unexpected\n', 40)],
        }
        for name, events in mutations.items():
            with self.subTest(name=name), self.assertRaises(ValueError):
                lab.classify(events)

    def long_session(self, kicks=4, gap=45.0, recovery=110.0, budget=47, final='window',
                     stopped=None):
        """Arm at 10 s, the link reload at 70 s, then reloads `gap` apart;
        then, 2 s after the last reload, `final`: the FINAL of a session that
        ended at its serve window ('window') or at its budget ('budget', with
        the kernel's budget-end record first), an older image's FINAL without
        session-end ('legacy'), or none (None). `stopped` is a refusal
        reason printed 1 s after the last reload."""
        events = [event(b'LEANOS-LAB/1 WATCHDOG-ARMED ticks=120\n', 10.0)]
        when = 70.0
        for n in range(1, kicks + 1):
            what = b' event=link' if n == 1 else b' event=ticks ticks=40'
            events.append(event(b'LEANOS-LAB/1 WATCHDOG-KICK n=%d budget=%d' % (n, budget) +
                                what + b' ticks-timeout=120\n', when))
            when += gap
        last = events[-1]['elapsed']
        if stopped is not None:
            events.append(event(b'LEANOS-LAB/1 WATCHDOG-KICK stopped reason=%d kicks=%d count=0 '
                                b'timer=120\n' % (stopped, kicks), last + 1))
        if final is not None:
            head = (lab.record(10, 'FINAL') + b' status=PASS dhcp-subject=1 echo-subject=1 '
                    b'device-holder=2 dhcp-frames=5 lease=192.168.6.40 frames=900 fetches=900 '
                    b'replies=12 refusals=1 ipc-edges=3600 watchdog-kicks=%d' % kicks)
            if final == 'budget':
                events.append(event(b'LEANOS-LAB/1 WATCHDOG-KICK session-end reason=budget '
                                    b'kicks=%d budget=%d\n' % (kicks, budget), last + 2))
            tail = {'window': b' session-end=window unsent-replies=0\n',
                    'budget': b' session-end=budget unsent-replies=0\n',
                    'legacy': b'\n'}[final]
            events.append(event(head + tail, last + 2))
        events.append(event(lab.CHAIN + b'(hd1,gpt2)\n', last + recovery))
        return events

    def test_watchdog_kick_classification(self):
        result = lab.classify_watchdog_kicks(self.long_session(), 47)
        self.assertEqual(result['watchdog_kicks'], 4)
        self.assertEqual(result['longest_reload_gap_seconds'], 60.0)
        self.assertEqual(result['protected_seconds'], 195.0)
        self.assertEqual(result['recovery_after_last_reload_seconds'], 110.0)
        self.assertIsNone(result['kicks_stopped_reason'])
        self.assertEqual(result['outcome'], 'final-window')
        self.assertNotIn('error', result)
        legacy = lab.classify_watchdog_kicks(self.long_session(final='legacy'), 47)
        self.assertEqual((legacy['outcome'], legacy['unsent_replies']), ('final-window', None))
        # issue #567: the kernel ends the session at its last reload
        spent = lab.classify_watchdog_kicks(self.long_session(kicks=5, budget=5, final='budget'), 5)
        self.assertEqual((spent['outcome'], spent['final_session_end']), ('final-budget', 'budget'))
        self.assertNotIn('error', spent)
        # the #557 hardware run: the budget ran out before FINAL; safe, but failing
        for events, budget in ((self.long_session(kicks=5, budget=5, final=None, stopped=2), 5),
                               (self.long_session(kicks=5, budget=5, final=None), 5),
                               (self.long_session(kicks=4, final=None, stopped=2), 47)):
            exhausted = lab.classify_watchdog_kicks(events, budget)
            self.assertEqual(exhausted['outcome'], 'budget-exhausted-before-final')
            self.assertEqual(exhausted['error'], 'budget exhausted before FINAL')
        stopped = lab.classify_watchdog_kicks(self.long_session(final=None, stopped=4), 47)
        self.assertEqual((stopped['kicks_stopped_reason'], stopped['outcome']), (4, 'no-final'))
        self.assertIn('error', stopped)
        # no reload at all: the arm alone bounds the run
        bare = lab.classify_watchdog_kicks(self.long_session(kicks=0, final=None), 47)
        self.assertEqual((bare['watchdog_kicks'], bare['outcome']), (0, 'no-final'))
        valid = self.long_session()
        budget_end = self.long_session(kicks=5, budget=5, final='budget')
        mutations = {
            'late reload': self.long_session(gap=120.0),
            'late recovery': self.long_session(recovery=151.0),
            'over budget': self.long_session(kicks=4, budget=3),
            'wrong budget': [valid[0], valid[1]] + [
                event(bytes.fromhex(e['hex']).replace(b'budget=47', b'budget=46'), e['elapsed'])
                for e in valid[2:]],
            'skipped number': valid[:2] + valid[3:],
            'repeated arm': valid[:1] + valid,
            'missing arm': valid[1:],
            'missing chain': valid[:-1],
            'malformed kick': valid[:-1] + [event(b'LEANOS-LAB/1 WATCHDOG-KICK n=x\n', 400.0),
                                            valid[-1]],
            'nonmonotonic time': valid[:2] + [event(b'x\n', 1.0)] + valid[2:],
            'FINAL count differs': [event(bytes.fromhex(e['hex']).replace(
                b'watchdog-kicks=4', b'watchdog-kicks=3'), e['elapsed']) for e in valid],
            'repeated FINAL': valid[:-1] + [valid[-2], valid[-1]],
            'reload after FINAL': valid[:-3] + [event(bytes.fromhex(valid[-2]['hex']),
                                                     valid[-3]['elapsed']), valid[-3], valid[-1]],
            'budget end early': self.long_session(kicks=4, budget=5, final='budget'),
            'budget end without record': budget_end[:-3] + budget_end[-2:],
            'budget record with window FINAL': budget_end[:-2] + [event(bytes.fromhex(
                budget_end[-2]['hex']).replace(b'session-end=budget', b'session-end=window'),
                budget_end[-2]['elapsed'])] + budget_end[-1:],
            'budget record without FINAL': budget_end[:-2] + budget_end[-1:],
            'spent-budget refusal before FINAL':
                self.long_session(kicks=5, budget=5, final='budget', stopped=2),
        }
        for name, events in mutations.items():
            budget = {'over budget': 3, 'budget end early': 5}.get(
                name, 5 if events and b'budget=5' in bytes.fromhex(events[1]['hex']) else 47)
            with self.subTest(name=name), self.assertRaises(ValueError):
                lab.classify_watchdog_kicks(events, budget)
        with self.assertRaises(ValueError):
            lab.classify_watchdog_kicks(valid, 93)


redact_spec = importlib.util.spec_from_file_location(
    'redact', Path(__file__).with_name('redact-qotom-capture.py'))
redact = importlib.util.module_from_spec(redact_spec)
redact_spec.loader.exec_module(redact)
FIXTURES = Path(__file__).with_name('fixtures') / 'qotom-device-captures'
# Fixtures of plain --lab-program images (issue #595), and the scenario each
# classifies as.
LAB_PROGRAM_FIXTURES = {'rtl8168-arp-pass': 'qotom-rtl8168-arp'}


def replace_bytes(events, old, new, count=1):
    """The events with `old` replaced by `new` in the one chunk holding it."""
    out, done = [], 0
    for e in events:
        chunk = bytes.fromhex(e['hex'])
        if done < count and old in chunk:
            chunk = chunk.replace(old, new, count - done)
            done = count
        out.append({'elapsed': e['elapsed'], 'hex': chunk.hex()})
    if not done:
        raise AssertionError('mutation target not found: %r' % old)
    return out


class DeviceProgramTests(unittest.TestCase):
    """Issue #572: device-program captures (device stream, network subject,
    DHCP subject, long session) are classified PASS or FAIL from the
    scenario flags of the lab image's manifest."""

    def fixture(self, name):
        root = FIXTURES / name
        summary = json.loads((root / 'redaction.json').read_text())
        self.assertTrue(summary['fragment'])
        self.assertEqual(hashlib.sha256((root / 'serial.raw').read_bytes()).hexdigest(),
                         summary['raw_sha256'])
        self.assertEqual(hashlib.sha256((root / 'timing.tsv').read_bytes()).hexdigest(),
                         summary['timing_tsv_sha256'])
        raw = (root / 'serial.raw').read_bytes()
        self.assertFalse(any(redact.PAYLOAD.match(raw[s:e]) for s, e in redact.lines(raw)))
        events = redact.load(root)
        self.assertEqual(b''.join(bytes.fromhex(e['hex']) for e in events), raw)
        return events, json.loads((root / 'manifest.json').read_text())

    def classify(self, name, events=None, manifest=None):
        recorded, flags = self.fixture(name)
        flags = flags if manifest is None else manifest
        return lab.classify_device_program(recorded if events is None else events,
                                           flags['elf_sha256'], flags)

    def test_fixtures(self):
        expected = {
            'network-subject-pass': ('qotom-network-subject', 'PASS', []),
            'wifi-dhcp-subject-pass': ('qotom-dhcp-subject', 'PASS', []),
            'long-session-budget-end-pass': ('qotom-dhcp-subject', 'PASS', []),
            'wifi-lease-count-fail': ('qotom-dhcp-subject', 'FAIL', [
                'terminal: FINAL status=FAIL reason=qotom-net-lease-count',
                'service-end: device program ended with status=1 code=0x00007e04']),
            'long-session-budget-exhausted-fail': ('qotom-dhcp-subject', 'FAIL', [
                'terminal: no FINAL record',
                'long-session: budget-exhausted-before-final: budget exhausted before FINAL']),
        }
        self.assertEqual(sorted(p.name for p in FIXTURES.iterdir()),
                         sorted(list(expected) + list(LAB_PROGRAM_FIXTURES)))
        for name, (scenario, status, failures) in expected.items():
            with self.subTest(name=name):
                result = self.classify(name)
                self.assertEqual((result['scenario'], result['status'], result['failures']),
                                 (scenario, status, failures))
                self.assertTrue(result['watchdog_protected'])
                self.assertLessEqual(result['recovery_after_last_protection_seconds'], 150)
                json.dumps(result)
        result = self.classify('network-subject-pass')
        self.assertEqual(result['terminal']['fields']['frames'], 7)
        self.assertEqual(result['records']['net_refusals'], 2)
        self.assertTrue(result['records']['broadcom_assign_admitted'])
        result = self.classify('wifi-dhcp-subject-pass')
        self.assertEqual((result['records']['lease'], result['wifi']['gtk_installed_key_ids']),
                         ('192.168.6.30', [1]))
        result = self.classify('wifi-lease-count-fail')
        self.assertEqual(result['terminal']['reason'], 'qotom-net-lease-count')
        self.assertGreaterEqual(result['quiet_seconds'], 30)
        result = self.classify('long-session-budget-end-pass')
        self.assertEqual((result['watchdog_kicks']['outcome'], result['watchdog_kicks']['watchdog_kicks'],
                          result['terminal']['fields']['session-end']), ('final-budget', 3, 'budget'))
        result = self.classify('long-session-budget-exhausted-fail')
        self.assertEqual((result['watchdog_kicks']['watchdog_kicks'],
                          result['watchdog_kicks']['kicks_stopped_reason'],
                          result['wifi']['gtk_rotations']), (92, 2, 1))

    def test_retained_device_stream(self):
        # The 2026-10-07 keyboard stream: its records pass, but the retained
        # serial stream stops at FINAL, before the recovery.
        root = Path(__file__).resolve().parent.parent / 'hardware/lab/observations/qotom-device-stream-20261007'
        events = [json.loads(line) for line in (root / 'cycle-1/events.jsonl').read_text().splitlines()]
        digest = (root / 'leanos.sha256').read_text().split()[0]
        result = lab.classify_device_program(events, digest, json.loads((root / 'manifest.json').read_text()))
        self.assertEqual((result['scenario'], result['status']), ('qotom-device-stream', 'FAIL'))
        self.assertEqual(result['failures'],
                         ['recovery: missing consumed-request default or FreeBSD chain after the run'])
        self.assertEqual(result['records']['ipc_deliveries'], 232)
        self.assertEqual(result['terminal']['fields'], {'status': 'PASS', 'events': 231,
                                                        'blocks': 233, 'deliveries': 232})

    def test_mutations_fail(self):
        events, _ = self.fixture('network-subject-pass')
        dhcp, _ = self.fixture('wifi-dhcp-subject-pass')
        final = re.search(rb'LEANOS/[0-9]+ FINAL [^\n]*\n',
                          b''.join(bytes.fromhex(e['hex']) for e in events)).group(0)
        mutations = {
            'assignment refused': ('network-subject-pass', replace_bytes(
                events, b'device-status=25 admitted=1\n', b'device-status=25 admitted=0\n'),
                'broadcom-assign'),
            'no service grant': ('network-subject-pass', replace_bytes(
                events, b'SERVICE grant subject=1', b'SERVICE gone subject=1'), 'service-grant'),
            'program failed': ('network-subject-pass', replace_bytes(
                events, b'SERVICE end subject=1 status=0', b'SERVICE end subject=1 status=2'), 'service-end'),
            'frame count': ('network-subject-pass', replace_bytes(
                events, b' frames=7 fetches=7', b' frames=8 fetches=8'), 'net'),
            'reply count': ('network-subject-pass', replace_bytes(
                events, b' replies=3 ', b' replies=4 '), 'net'),
            'refusal count': ('network-subject-pass', replace_bytes(
                events, b' refusals=2 ', b' refusals=1 '), 'net'),
            'changed FINAL': ('network-subject-pass', replace_bytes(
                events, b'network-subject=1 device-holder=2', b'network-subject=1 device-holder=1'), 'terminal'),
            'repeated FINAL': ('network-subject-pass', replace_bytes(events, final, final + final), 'terminal'),
            'no arm': ('network-subject-pass', replace_bytes(
                events, b'WATCHDOG-ARMED ticks=120', b'WATCHDOG-ARMED ticks=60'), 'watchdog-arm'),
            'no chain': ('network-subject-pass', replace_bytes(
                events, b'LEANOS-LAB/1 CHAIN freebsd', b'LEANOS-LAB/1 HALT freebsd'), 'recovery'),
            'bytes after FINAL': ('network-subject-pass', replace_bytes(
                events, final, final + b'x'), 'recovery'),
            'handoff lease': ('wifi-dhcp-subject-pass', replace_bytes(
                dhcp, b'frame=5 lease=192.168.6.30', b'frame=5 lease=192.168.6.31'), 'net-handoff'),
            'no lease delivery': ('wifi-dhcp-subject-pass', replace_bytes(
                dhcp, b'payload=lease', b'payload=other'), 'lease-delivery'),
        }
        for name, (fixture, mutated, check) in mutations.items():
            with self.subTest(name=name):
                result = self.classify(fixture, mutated)
                self.assertEqual(result['status'], 'FAIL')
                self.assertTrue(any(f.startswith(check + ':') for f in result['failures']),
                                result['failures'])

    def test_manifest_flags(self):
        _, flags = self.fixture('network-subject-pass')
        # The capture of another scenario's image fails its records.
        for other in (dict(flags, network_subject=False),
                      dict(flags, dhcp_subject=True),
                      dict(flags, dhcp_subject=True, long_session_seconds=40, watchdog_kick_budget=3)):
            with self.subTest(flags=other):
                self.assertEqual(self.classify('network-subject-pass', manifest=other)['status'], 'FAIL')
        for bad in (dict(flags, ipc_device_stream=False), dict(flags, mode='kernel-hang'),
                    dict(flags, network_subject=False, dhcp_subject=True),
                    dict(flags, long_session_seconds=40, watchdog_kick_budget=3),
                    dict(flags, dhcp_subject=True, long_session_seconds=40, watchdog_kick_budget=4),
                    dict(flags, watchdog_kick_budget=3),
                    dict(flags, network_subject=False, production_network=True)):
            with self.subTest(flags=bad), self.assertRaises(ValueError):
                self.classify('network-subject-pass', manifest=bad)
        events = self.fixture('network-subject-pass')[0]
        digest = flags['elf_sha256']
        for bad_digest, bad_flags in (('b' * 63, flags), (digest, dict(flags, elf_sha256='b' * 64))):
            with self.assertRaises(ValueError):
                lab.classify_device_program(events, bad_digest, bad_flags)
        # A manifest without the ELF binding (older builds) still classifies;
        # a different image's digest fails the protected load.
        unbound = {k: v for k, v in flags.items() if k != 'elf_sha256'}
        self.assertEqual(lab.classify_device_program(events, digest, unbound)['status'], 'PASS')
        result = lab.classify_device_program(events, 'b' * 64, unbound)
        self.assertEqual(result['failures'], ['watchdog-load: missing or changed'])

    def test_redaction(self):
        payload = b'WIFI 0e24 0x45000054\nWIFI 0e26 0xc0a80601\n'
        events = [event(b'LEANOS-LAB/1 NET event=deliver frame=1 bytes=60\nWIFI 0e2', 1.0),
                  event(b'4 0x45000054\n', 1.2), event(b'WIFI 0e26 0xc0a80601\nWIFI 0f12 0x0000003c\n', 1.4),
                  event(b'\rWIFI 0e26 0xdeadbeef\n', 2.6), event(payload, 5.0),
                  event(b'LEANOS-LAB/1 NET event=fetch frame=1 bytes=60 copy-roots=bounded16 model=accepted\n', 5.1)]
        out, raw, removed = redact.redact(events)
        self.assertEqual(removed, {'payload': 5, 'fragment': 0})
        self.assertEqual([e['elapsed'] for e in out], [1.0, 1.4, 5.1])
        self.assertNotIn(b'0e24', raw)
        self.assertNotIn(b'0e26', raw)
        self.assertEqual(raw, b'LEANOS-LAB/1 NET event=deliver frame=1 bytes=60\nWIFI 0f12 0x0000003c\n'
                              b'LEANOS-LAB/1 NET event=fetch frame=1 bytes=60 copy-roots=bounded16 model=accepted\n')
        out, raw, removed = redact.redact(events, fragment=True)
        self.assertEqual(removed, {'payload': 5, 'fragment': 2})
        self.assertEqual([e['elapsed'] for e in out], [1.0])
        self.assertEqual(raw, b'LEANOS-LAB/1 NET event=deliver frame=1 bytes=60\n')
        # The rtl8168-arp program's value records (tags 40xx-42xx) are read
        # by the lab-program classifier (issue #595): a fragment keeps them.
        rtl = b'WIFI 4004 0x0000008b\nWIFI 4237 0x00000000\nWIFI 42e8 0x00000000\n'
        out, raw, removed = redact.redact([event(rtl + b'WIFI 4300 0x00000000\n', 1.0)],
                                          fragment=True)
        self.assertEqual((raw, removed), (rtl, {'payload': 0, 'fragment': 1}))
        # Events within a second join at the first one's time, never longer.
        spread = [event(b'LEANOS-LAB/1 NET event=send frame=%d\n' % n, 0.4 * n) for n in range(6)]
        self.assertEqual([round(e['elapsed'], 6) for e in redact.redact(spread, fragment=True)[0]],
                         [0.0, 1.2])

class LabProgramTests(unittest.TestCase):
    """Issue #595: the capture of a plain --lab-program image is classified
    PASS or FAIL against its program's records. For rtl8168-arp these are
    step 2 of "Maintainer hardware steps" in docs/net-rtl8168.md."""

    fixture = DeviceProgramTests.fixture

    def classify(self, events=None, manifest=None, name='rtl8168-arp-pass'):
        recorded, flags = self.fixture(name)
        flags = flags if manifest is None else manifest
        return lab.classify_lab_program(recorded if events is None else events,
                                        flags['elf_sha256'], flags)

    def test_fixtures(self):
        for name, scenario in LAB_PROGRAM_FIXTURES.items():
            with self.subTest(name=name):
                result = self.classify(name=name)
                self.assertEqual((result['scenario'], result['status'], result['failures']),
                                 (scenario, 'PASS', []))
                self.assertEqual(result['terminal']['reason'], 'qotom-platform-pending')
                self.assertTrue(result['watchdog_protected'])
                self.assertGreaterEqual(result['quiet_seconds'], 30)
                self.assertLessEqual(result['recovery_after_last_protection_seconds'], 150)
                json.dumps(result)
        # The 2026-10-19 run (#577): the router's address as FreeBSD's
        # neighbour table has it, one probe and one frame.
        records = self.classify()['records']
        self.assertEqual((records['device_id'], records['wifi_end']),
                         ('0x816810ec', {'status': '0', 'code': '0x00000000'}))
        self.assertEqual((records['link_media'], records['transmit_status'], records['router_address'],
                          records['frames']), ('0x8b', ['0x70000000'], '70:13:01:5f:32:0f', 1))
        self.assertEqual([len(records['before_dump']), len(records['after_dump'])], [23, 23])
        # 9346CR reads 0x10 before and after: bit 4 stays set on this chip,
        # and the EEM bits 7:6 are clear.
        self.assertEqual((records['before_dump']['50'], records['after_dump']['50']),
                         ('0x00000010', '0x00000010'))
        self.assertEqual((records['after_dump']['37'], records['after_dump']['3c'],
                          records['after_dump']['e4']), ('0x00000000', '0x00000000', '0x001b0000'))

    def test_named_failures(self):
        events, _ = self.fixture('rtl8168-arp-pass')
        cases = {
            'missing after-dump record': (
                replace_bytes(events, b'WIFI 42e8 0x00000000\n', b''), ['after-dump: missing 42e8']),
            'reset timeout': (
                replace_bytes(events, b'WIFI 4237 ', b'WIFI 400e 0x00000000\nWIFI 4237 '),
                ['teardown: 400e: the reset did not complete']),
            'engines still on': (
                replace_bytes(events, b'WIFI 4237 0x00000000', b'WIFI 4237 0x0000000c'),
                ['after-command: 4237 = 0x0c, not 0: TE, RE or RST still set']),
        }
        for name, (mutated, failures) in cases.items():
            with self.subTest(name=name):
                result = self.classify(mutated)
                self.assertEqual((result['status'], result['failures']), ('FAIL', failures))

    def test_mutations_fail(self):
        events, _ = self.fixture('rtl8168-arp-pass')
        link_first = replace_bytes(replace_bytes(events, b'WIFI 4004 0x0000008b\n', b''),
                                   b'WIFI 4137 ', b'WIFI 4004 0x0000008b\nWIFI 4137 ')
        cases = [
            ('before-dump', replace_bytes(events, b'WIFI 4150 0x00000010\n', b'')),
            ('before-dump', replace_bytes(events, b'WIFI 4158 ', b'WIFI 4158 0x00000000\nWIFI 4158 ')),
            ('after-dump', replace_bytes(events, b'WIFI 4250 ', b'WIFI 4251 ')),
            ('link', replace_bytes(events, b'WIFI 4004 0x0000008b', b'WIFI 4004 0x00000089')),
            ('transmit', replace_bytes(events, b'WIFI 400c 0x70000000', b'WIFI 400c 0xf0000000')),
            ('transmit', replace_bytes(events, b'WIFI 400c 0x70000000\n', b'')),
            ('router-address', replace_bytes(events, b'WIFI 4007 0x5f011370\n', b'')),
            ('frames', replace_bytes(events, b'WIFI 4009 0x00000001', b'WIFI 4009 0x00000000')),
            ('teardown', replace_bytes(events, b'WIFI 4237 ', b'WIFI 400d 0x00000000\nWIFI 4237 ')),
            ('after-imr', replace_bytes(events, b'WIFI 423c 0x00000000', b'WIFI 423c 0x00000085')),
            ('after-9346cr', replace_bytes(events, b'WIFI 4250 0x00000010', b'WIFI 4250 0x000000d0')),
            ('done', replace_bytes(events, b'WIFI 40ff 0x00000000\n', b'')),
            ('records', replace_bytes(events, b'WIFI 4006 0x00000000', b'WIFI 4006 0x0000')),
            ('wifi-end', replace_bytes(events, b'WIFI-END status=0 code=0x00000000',
                                       b'WIFI-END status=1 code=0x00007b07')),
            ('wifi-end', replace_bytes(events, b'LEANOS-LAB/1 WIFI-END status=0 code=0x00000000\n', b'')),
            ('wifi-begin', replace_bytes(events, b'WIFI-BEGIN id=', b'WIFI-BEGAN id=')),
            ('terminal', replace_bytes(events, b'reason=qotom-platform-pending',
                                       b'reason=j1900-msr-readback')),
            ('order', link_first),
            ('watchdog-arm', replace_bytes(events, b'WATCHDOG-ARMED ticks=120', b'WATCHDOG-ARMED ticks=60')),
            ('recovery', replace_bytes(events, b'LEANOS-LAB/1 CHAIN freebsd', b'LEANOS-LAB/1 HALT freebsd')),
            ('recovery', replace_bytes(events, b'qotom-platform-pending\n',
                                       b'qotom-platform-pending\nx')),
        ]
        for check, mutated in cases:
            with self.subTest(check=check):
                result = self.classify(mutated)
                self.assertEqual(result['status'], 'FAIL')
                self.assertTrue(any(f.startswith(check + ':') for f in result['failures']),
                                result['failures'])
        # Without WIFI-BEGIN the program is unknown, and so are its records.
        result = self.classify(replace_bytes(events, b'WIFI-BEGIN id=', b'WIFI-BEGAN id='))
        self.assertEqual((result['scenario'], result['failures']),
                         ('qotom-lab-program', ['wifi-begin: missing or changed']))

    def test_manifest(self):
        events, flags = self.fixture('rtl8168-arp-pass')
        digest = flags['elf_sha256']
        for bad in (dict(flags, lab_program_sha256=[]),
                    dict(flags, lab_program_sha256=flags['lab_program_sha256'] * 2),
                    {k: v for k, v in flags.items() if k != 'lab_program_sha256'},
                    dict(flags, wifi_program_sha256='d' * 64), dict(flags, ipc_device_stream=True),
                    dict(flags, production_network=True), dict(flags, mode='kernel-hang'),
                    dict(flags, pci_diagnostic=True), dict(flags, realtek_bme=True),
                    dict(flags, long_session_seconds=40)):
            with self.subTest(flags=bad), self.assertRaises(ValueError):
                lab.classify_lab_program(events, digest, bad)
        # source_dirty records the build, not a stage.
        self.assertEqual(lab.classify_lab_program(events, digest, dict(flags, source_dirty=True))
                         ['status'], 'PASS')
        for bad_digest, bad_flags in (('b' * 63, flags), (digest, dict(flags, elf_sha256='b' * 64))):
            with self.assertRaises(ValueError):
                lab.classify_lab_program(events, bad_digest, bad_flags)
        unbound = {k: v for k, v in flags.items() if k != 'elf_sha256'}
        self.assertEqual(lab.classify_lab_program(events, 'b' * 64, unbound)['failures'],
                         ['watchdog-load: missing or changed'])
        # A program whose records the runner does not know is not classified.
        other = replace_bytes(events, b'WIFI-BEGIN id=0x816810ec', b'WIFI-BEGIN id=0x435314e4')
        with self.assertRaisesRegex(ValueError, 'no classifier for the lab program on device 0x435314e4'):
            lab.classify_lab_program(other, digest, flags)
        # Not a device-program image (issue #572).
        with self.assertRaises(ValueError):
            lab.classify_device_program(events, digest, flags)

    def test_program_source(self):
        # The classifier's tags and dump offsets are LeanOS/Net/Rtl8168.lean's.
        source = (Path(__file__).resolve().parent.parent / 'LeanOS/Net/Rtl8168.lean').read_text()

        def constants(text):
            return {name: int(value, 16) for name, value in
                    re.findall(r'^def (\w+) : UInt32 := (0x[0-9A-Fa-f]+)', text, re.M)}

        registers = constants(source[source.index('## Registers'):source.index('## Scratch layout')])
        tags = constants(source[source.index('namespace Tag'):source.index('end Tag')])
        self.assertEqual({k: tags[k] for k in ('media', 'routerMacLo', 'routerMacHi', 'frames',
                                               'txStatus', 'stopTimeout', 'resetTimeout', 'done',
                                               'before', 'after')},
                         {'media': 0x4004, 'routerMacLo': 0x4007, 'routerMacHi': 0x4008,
                          'frames': 0x4009, 'txStatus': 0x400c, 'stopTimeout': 0x400d,
                          'resetTimeout': 0x400e, 'done': 0x40ff, 'before': 0x4100, 'after': 0x4200})
        dump = re.search(r'def dumpRegs : List \(UInt32 × Nat\) :=\n(.*?)\n\n', source, re.S).group(1)
        offsets = tuple(registers[name] + int(plus or 0)
                        for name, plus in re.findall(r'\((\w+)(?: \+ (\d+))?, [124]\)', dump))
        self.assertEqual(offsets, lab.RTL8168_DUMP)
        self.assertEqual((registers['command'], registers['imr'], registers['eecmd']), (0x37, 0x3c, 0x50))
        self.assertIn('target : Target :=\n  { bus := 1, dev := 0, fn := 0, id := 0x816810ec,', source)
        self.assertEqual(lab._LAB_PROGRAMS, {0x816810ec: 'rtl8168-arp'})


class SimulatedRun:
    """A run as wait_for_recovery sees it (issue #595): the capture's events
    arrive at their times, the runner polls every 2 seconds, and FreeBSD
    answers over SSH, with a new boot time, from `freebsd_at` on."""

    def __init__(self, events, freebsd_at):
        self.events, self.freebsd_at, self.now, self.prompts = events, freebsd_at, 0.0, []

    def wait(self, **options):
        def captured():
            return b''.join(bytes.fromhex(e['hex']) for e in self.events if e['elapsed'] <= self.now)

        def pause():
            self.now += 2

        return lab.wait_for_recovery(lambda: self.now, captured,
                                     lambda: 2 if self.now >= self.freebsd_at else None, 1, pause,
                                     prompt=lambda: self.prompts.append(self.now), **options)


class ProductionTests(unittest.TestCase):
    """The production network capture (issue #569): no watchdog, an
    absorbing halt after FINAL, and FreeBSD after the maintainer's power
    cycle."""
    DIGEST = 'c' * 64
    MANIFEST = {'production_network': True, 'evidence_class': 'production-candidate',
                'ipc_device_stream': True, 'mode': 'completion'}
    WINDOWS = (b'LEANOS-LAB/1 PRODUCTION-WINDOWS profile=qotom-network-v1 holders=1,3 '
               b'a-window-pages=2 c-window-pages=1 fetch-root=writable send-root=read-only '
               b'protected=8 roots=5 scan=exact operand=agree root-c=exact\n')

    def records(self):
        lines = [b'LEANOS-LAB/1 SELECT leanos consumed=1\n',
                 b'LEANOS-LAB/1 MODE qotom-production final=halt watchdog=none\n',
                 lab.record(10, 'BOOT') + b' target=x86_64-qotom\n', self.WINDOWS,
                 b'LEANOS-LAB/1 PLATFORM-ADMISSION profile=qotom-j1900-clbtm210-v2 version=2 '
                 b'status=PASS cpl3-authority=1\n',
                 b'LEANOS-LAB/1 BROADCOM-ASSIGN profile=qotom-j1900-pci-trust-v1-bcm43224-assign-v1 '
                 b'device=2:0.0 status=0 contract=1 polls=2 admitted=1\n',
                 b'LEANOS-LAB/1 SERVICE grant subject=1 device=0:20.0 bind=accepted policy=admitted\n',
                 b'LEANOS-LAB/1 QOTOM-IPC-READY profile=qotom-blocking-ipc-v1 subjects=2\n',
                 b'LEANOS-LAB/1 PRODUCTION-READY profile=qotom-network-v1 subjects=3 '
                 b'address-spaces=3 frames=copy-window watchdog=none final=halt\n',
                 b'LEANOS-LAB/1 NET event=refuse subject=3 op=device-invoke '
                 b'reason=no-device-capability model=refused\n',
                 b'LEANOS-LAB/1 NET event=refuse subject=3 op=fetch reason=not-routed model=refused\n',
                 b'LEANOS-LAB/1 NET event=refuse subject=1 op=device-invoke '
                 b'reason=no-device-capability model=refused\n',
                 b'LEANOS-LAB/1 NET event=refuse subject=2 op=fetch reason=not-holder model=refused\n']
        for frame, size, sent in ((1, 6, 342), (2, 342, 342), (3, 342, 0)):
            lines += [b'LEANOS-LAB/1 NET event=deliver frame=%d bytes=%d port=dhcp\n' % (frame, size),
                      b'LEANOS-LAB/1 NET event=fetch subject=1 frame=%d bytes=%d copy=fetch-root '
                      b'model=accepted\n' % (frame, size)]
            if sent:
                lines.append(b'LEANOS-LAB/1 NET event=send subject=1 frame=%d bytes=%d '
                             b'copy=send-root model=accepted\n' % (frame, sent))
        lines += [b'LEANOS-LAB/1 NET event=handoff from=1 to=3 frame=3 lease=192.168.6.57 '
                  b'route=echo address-spaces=separate model=accepted\n',
                  b'LEANOS-LAB/1 NET event=deliver frame=4 bytes=98 port=echo\n',
                  b'LEANOS-LAB/1 NET event=fetch subject=3 frame=4 bytes=98 copy=fetch-root '
                  b'model=accepted\n',
                  b'LEANOS-LAB/1 NET event=send subject=3 frame=4 bytes=98 copy=send-root '
                  b'model=accepted\n',
                  b'LEANOS-LAB/1 SERVICE end subject=1 status=0 code=0x00000000\n',
                  lab.record(10, 'FINAL') + b' status=PASS profile=qotom-network-v1 subjects=3 dhcp-subject=1 '
                  b'echo-subject=3 device-holder=2 address-spaces=3 lease=192.168.6.57 frames=4 '
                  b'dhcp-frames=3 echo-frames=1 fetches=4 sends=3 refusals=4 ipc-edges=22 '
                  b'window-copies=7\n']
        return lines

    def capture(self, lines=None, after=None, start=1.0, tail_at=400.0):
        lines = self.records() if lines is None else lines
        events = [event(line, start + 0.002 * i) for i, line in enumerate(lines)]
        tail = (b'LEANOS-LAB/1 DEFAULT request=none\nLEANOS-LAB/1 CHAIN freebsd disk=hd1\n'
                if after is None else after)
        return events + [event(tail, tail_at)]

    def test_power_cycle_wait(self):
        # Issue #595: the wait for the maintainer's power cycle runs from the
        # POWER-CYCLE prompt (15 minutes by default), not from the start.
        # FINAL at 199 s of a 120-second serve window; the board is power-
        # cycled 14 minutes after the prompt, more than 15 minutes after the
        # start (and after the former SECONDS + 900 deadline).
        events = self.capture(start=199.0, tail_at=1045.0)
        run = SimulatedRun(events, freebsd_at=1080.0)
        self.assertEqual(run.wait(bound=180, production_seconds=120), 2)
        self.assertEqual(run.prompts, [200.0])
        self.assertGreater(run.now, 15 * 60)
        self.assertGreater(run.now, 120 + 900)
        self.assertLess(run.now - run.prompts[0], 15 * 60)
        result = lab.classify_production(events, self.DIGEST, self.MANIFEST)
        self.assertEqual(result['status'], 'PASS', result['failures'])
        # Past the window after the prompt, the runner gives up.
        run = SimulatedRun(events, freebsd_at=1110.0)
        with self.assertRaisesRegex(ValueError, 'no verified FreeBSD recovery before timeout'):
            run.wait(bound=180, production_seconds=120)
        self.assertEqual((run.prompts, run.now), ([200.0], 1100.0))
        # --power-cycle-minutes 30 widens the window, still from the prompt.
        late = self.capture(start=199.0, tail_at=1870.0)
        run = SimulatedRun(late, freebsd_at=1900.0)
        self.assertEqual(run.wait(bound=180, production_seconds=120, power_cycle_seconds=30 * 60), 2)
        self.assertEqual(lab.classify_production(late, self.DIGEST, self.MANIFEST)['status'], 'PASS')
        # Without FINAL the prompt comes SECONDS + 180 seconds after the
        # start, and the window runs from there; the capture fails.
        hung = self.capture(self.records()[:-1], start=1.0, tail_at=1100.0)
        run = SimulatedRun(hung, freebsd_at=1150.0)
        self.assertEqual(run.wait(bound=180, production_seconds=120), 2)
        self.assertEqual(run.prompts, [302.0])
        self.assertIn('terminal: no FINAL record',
                      lab.classify_production(hung, self.DIGEST, self.MANIFEST)['failures'])
        run = SimulatedRun(hung, freebsd_at=1210.0)
        with self.assertRaises(ValueError):
            run.wait(bound=180, production_seconds=120)
        # A lab image recovers by itself: its bound runs from the start and
        # nothing asks for a power cycle.
        reset = self.capture(tail_at=60.0)
        run = SimulatedRun(reset, freebsd_at=400.0)
        self.assertEqual(run.wait(bound=420), 2)
        self.assertEqual(run.prompts, [])
        run = SimulatedRun(reset, freebsd_at=430.0)
        with self.assertRaises(ValueError):
            run.wait(bound=420)
        self.assertEqual((run.prompts, run.now), ([], 420.0))

    def test_pass(self):
        result = lab.classify_production(self.capture(), self.DIGEST, self.MANIFEST)
        self.assertEqual(result['status'], 'PASS', result['failures'])
        self.assertEqual(result['records']['lease'], '192.168.6.57')
        self.assertEqual(result['echo_service_ms']['frames'], 1)
        self.assertGreaterEqual(result['quiet_seconds'], 10)
        self.assertFalse(result['watchdog_protected'])

    def test_mutations_fail(self):
        lines = self.records()
        final = len(lines) - 1
        cases = [
            ('watchdog', lines[:1] + [b'LEANOS-LAB/1 WATCHDOG-ARMED ticks=120\n'] + lines[1:]),
            ('production-mode', [l for l in lines if b'MODE' not in l]),
            ('copy-windows', [l.replace(b'scan=exact', b'scan=partial') for l in lines]),
            ('broadcom-assign', [l.replace(b'admitted=1', b'admitted=0') for l in lines]),
            ('net', [l.replace(b'refusals=4', b'refusals=5') for l in lines]),
            ('net-handoff', [l.replace(b'frame=3 lease=', b'frame=2 lease=') for l in lines]),
            ('terminal', lines[:final] + [lines[final].replace(b'address-spaces=3 ', b'')]),
            ('net', lines[:final] + [lines[final].replace(b'window-copies=7', b'window-copies=6')]),
            ('order', lines[:3] + lines[4:5] + lines[3:4] + lines[5:]),
        ]
        for check, mutated in cases:
            with self.subTest(check=check):
                result = lab.classify_production(self.capture(mutated), self.DIGEST, self.MANIFEST)
                self.assertEqual(result['status'], 'FAIL')
                self.assertTrue(any(f.startswith(check) for f in result['failures']),
                                result['failures'])
        result = lab.classify_production(self.capture(after=b''), self.DIGEST, self.MANIFEST)
        self.assertTrue(any(f.startswith('recovery') for f in result['failures']))

    def test_lease_window(self):
        # A connect program's lease signal record (issue #573) follows the
        # hand-off once; a lease window that ran out fails the capture.
        lines = self.records()
        handoff = next(i for i, l in enumerate(lines) if b'NET event=handoff' in l)
        signal = b'LEANOS-LAB/1 WIFI-LEASE signalled after-ms=4210\n'
        signalled = lines[:handoff + 1] + [signal] + lines[handoff + 1:]
        result = lab.classify_production(self.capture(signalled), self.DIGEST, self.MANIFEST)
        self.assertEqual(result['status'], 'PASS', result['failures'])
        self.assertEqual(result['records']['lease_signalled_after_ms'], 4210)
        self.assertIsNone(lab.classify_production(self.capture(), self.DIGEST, self.MANIFEST)
                          ['records']['lease_signalled_after_ms'])
        over = b'LEANOS-LAB/1 WIFI-LEASE window-over without-lease window-ms=60000\n'
        for mutated in (lines[:handoff] + [signal] + lines[handoff:],
                        lines[:handoff + 1] + [signal, signal] + lines[handoff + 1:],
                        lines[:handoff + 1] + [over] + lines[handoff + 1:]):
            with self.subTest(mutated=mutated[handoff:handoff + 3]):
                result = lab.classify_production(self.capture(mutated), self.DIGEST, self.MANIFEST)
                self.assertEqual(result['status'], 'FAIL')
                self.assertTrue(any(f.startswith('lease-window') for f in result['failures']),
                                result['failures'])

    def test_manifest(self):
        for bad in (dict(self.MANIFEST, production_network=False),
                    dict(self.MANIFEST, evidence_class='lab-recovery-experiment'),
                    dict(self.MANIFEST, elf_sha256='d' * 64)):
            with self.subTest(manifest=bad), self.assertRaises(ValueError):
                lab.classify_production(self.capture(), self.DIGEST, bad)

if __name__ == '__main__':
    unittest.main()
