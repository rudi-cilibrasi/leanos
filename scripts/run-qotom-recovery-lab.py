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
import runpy
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


def cpu_diagnostic_bytes(events, protocol, handoff=False):
    data = b''.join(bytes.fromhex(e['hex']) for e in events)
    mode = EXPECTED[:-len(EXPECTED_KERNEL)]
    if data.count(mode) != 1:
        raise ValueError('missing or repeated recovery mode record')
    start = data.find(mode) + len(mode)
    prelude = b''
    if handoff:
        decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-handoff-capture.py')))
        consumed, _, _ = decoder['parse_prefix'](data[start:])
        prelude = data[start:start + consumed]
        start += consumed
    if not data.startswith(protocol['BOOT'].encode('ascii'), start):
        raise ValueError('CPU diagnostic must immediately follow recovery mode')
    final = data.find(protocol['FINAL'].encode('ascii'), start)
    end = data.find(b'\n', final) if final >= 0 else -1
    if end < 0:
        raise ValueError('missing CPU diagnostic terminal')
    raw = data[start:end + 1]
    return mode + prelude + raw, raw


def cpu_replay_inputs(protocol_path, replay, pci_replay=None, handoff=False, acpi=False, pci_read_trace=False, bootstrap=False, ecam_memory=False, dsdt=False, ecam_read=False, native_inventory=False, native_kernel=False, bsp_replay=None, pci_capabilities=False, af_observation=False, ehci_capabilities=False, ehci_legacy=False, ehci_handoff=False, ehci_smi=False, ehci_operational=False, ehci_bme=False, xhci_capabilities=False, xhci_legacy=False, xhci_handoff=False, xhci_smi=False, xhci_operational=False, xhci_bme=False, pcie_device_observation=False, ahci_capabilities=False, ahci_port=False, ahci_interrupts=False, ahci_bme=False, hda_observation=False, hda_state=False, hda_bme=False, txe_status=False, rootport_bme=False, realtek_state=False, realtek_bme=False):
    result = {'protocol_sha256': hashlib.sha256(Path(protocol_path).read_bytes()).hexdigest(),
             'replay_executable_sha256': hashlib.sha256(Path(replay).read_bytes()).hexdigest()}
    if realtek_bme:
        result['realtek_bme_decoder_sha256'] = hashlib.sha256(Path(__file__).with_name('check-qotom-realtek-bme-capture.py').read_bytes()).hexdigest()
    if realtek_state:
        result['realtek_state_decoder_sha256'] = hashlib.sha256(Path(__file__).with_name('check-qotom-realtek-state-capture.py').read_bytes()).hexdigest()
    if rootport_bme:
        result['rootport_bme_decoder_sha256'] = hashlib.sha256(Path(__file__).with_name('check-qotom-rootport-bme-capture.py').read_bytes()).hexdigest()
    if txe_status:
        result['txe_status_decoder_sha256'] = hashlib.sha256(Path(__file__).with_name('check-qotom-txe-status-capture.py').read_bytes()).hexdigest()
    if hda_bme:
        result['hda_bme_decoder_sha256'] = hashlib.sha256(Path(__file__).with_name('check-qotom-hda-bme-capture.py').read_bytes()).hexdigest()
    if hda_state:
        result['hda_state_decoder_sha256'] = hashlib.sha256(Path(__file__).with_name('check-qotom-hda-state-capture.py').read_bytes()).hexdigest()
    if hda_observation:
        result['hda_decoder_sha256'] = hashlib.sha256(Path(__file__).with_name('check-qotom-hda-capture.py').read_bytes()).hexdigest()
    if ahci_bme:
        result['ahci_bme_decoder_sha256'] = hashlib.sha256(Path(__file__).with_name('check-qotom-ahci-bme-capture.py').read_bytes()).hexdigest()
    if ahci_interrupts:
        result['ahci_interrupt_decoder_sha256'] = hashlib.sha256(Path(__file__).with_name('check-qotom-ahci-interrupt-capture.py').read_bytes()).hexdigest()
    if ahci_port:
        result['ahci_port_decoder_sha256'] = hashlib.sha256(Path(__file__).with_name('check-qotom-ahci-port-capture.py').read_bytes()).hexdigest()
    if ahci_capabilities:
        result['ahci_decoder_sha256'] = hashlib.sha256(Path(__file__).with_name('check-qotom-ahci-capture.py').read_bytes()).hexdigest()
    if pcie_device_observation:
        result['pcie_device_decoder_sha256'] = hashlib.sha256(Path(__file__).with_name('check-qotom-pcie-device-capture.py').read_bytes()).hexdigest()
    if xhci_bme:
        result['xhci_bme_decoder_sha256'] = hashlib.sha256(Path(__file__).with_name('check-qotom-xhci-bme-capture.py').read_bytes()).hexdigest()
    if xhci_operational:
        result['xhci_operational_decoder_sha256'] = hashlib.sha256(Path(__file__).with_name('check-qotom-xhci-operational-capture.py').read_bytes()).hexdigest()
    if xhci_smi:
        result['xhci_smi_decoder_sha256'] = hashlib.sha256(Path(__file__).with_name('check-qotom-xhci-smi-capture.py').read_bytes()).hexdigest()
    if xhci_handoff:
        result['xhci_handoff_decoder_sha256'] = hashlib.sha256(Path(__file__).with_name('check-qotom-xhci-handoff-capture.py').read_bytes()).hexdigest()
    if xhci_legacy:
        result['xhci_legacy_decoder_sha256'] = hashlib.sha256(Path(__file__).with_name('check-qotom-xhci-legacy-capture.py').read_bytes()).hexdigest()
    if xhci_capabilities:
        result['xhci_capabilities_decoder_sha256'] = hashlib.sha256(Path(__file__).with_name('check-qotom-xhci-capture.py').read_bytes()).hexdigest()
    if ehci_bme:
        result['ehci_bme_decoder_sha256'] = hashlib.sha256(Path(__file__).with_name('check-qotom-ehci-bme-capture.py').read_bytes()).hexdigest()
    if ehci_operational:
        result['ehci_operational_decoder_sha256'] = hashlib.sha256(Path(__file__).with_name('check-qotom-ehci-operational-capture.py').read_bytes()).hexdigest()
    if ehci_smi:
        result['ehci_smi_decoder_sha256'] = hashlib.sha256(Path(__file__).with_name('check-qotom-ehci-smi-capture.py').read_bytes()).hexdigest()
    if ehci_handoff:
        result['ehci_handoff_decoder_sha256'] = hashlib.sha256(Path(__file__).with_name('check-qotom-ehci-handoff-capture.py').read_bytes()).hexdigest()
    if ehci_legacy:
        result['ehci_legacy_decoder_sha256'] = hashlib.sha256(Path(__file__).with_name('check-qotom-ehci-legacy-capture.py').read_bytes()).hexdigest()
    if ehci_capabilities:
        result['ehci_decoder_sha256'] = hashlib.sha256(Path(__file__).with_name('check-qotom-ehci-capture.py').read_bytes()).hexdigest()
    if af_observation:
        result['af_decoder_sha256'] = hashlib.sha256(Path(__file__).with_name('check-qotom-af-capture.py').read_bytes()).hexdigest()
    if pci_capabilities:
        result['pci_capabilities_decoder_sha256'] = hashlib.sha256(Path(__file__).with_name('check-qotom-pci-capabilities-capture.py').read_bytes()).hexdigest()
    if bsp_replay is not None:
        result['bsp_replay_executable_sha256'] = hashlib.sha256(Path(bsp_replay).read_bytes()).hexdigest()
        result['bsp_decoder_sha256'] = hashlib.sha256(Path(__file__).with_name('check-qotom-bsp-capture.py').read_bytes()).hexdigest()
    if native_kernel:
        result['native_kernel_inventory_enabled'] = True
    if native_inventory:
        result['inventory_profile'] = 'qotom-native-ecam-v1'
        result['inventory_profile_decoder_sha256'] = hashlib.sha256(
            Path(__file__).with_name('check-qotom-pci-diagnostic.py').read_bytes()).hexdigest()
    if dsdt:
        result['dsdt_capture'] = True
    if ecam_read:
        result['ecam_decoder_sha256'] = hashlib.sha256(
            Path(__file__).with_name('check-qotom-ecam-capture.py').read_bytes()).hexdigest()
        result['ecam_cpu_decoder_sha256'] = hashlib.sha256(
            Path(__file__).with_name('check-j1900-diagnostic.py').read_bytes()).hexdigest()
        result['ecam_firmware_manifest_sha256'] = hashlib.sha256(
            (Path(__file__).resolve().parents[1] /
             'hardware/lab/observations/qotom-dsdt-20260911/manifest.json').read_bytes()).hexdigest()
    if pci_replay is not None:
        result['pci_replay_executable_sha256'] = hashlib.sha256(Path(pci_replay).read_bytes()).hexdigest()
    if handoff:
        result['handoff_decoder_sha256'] = hashlib.sha256(
            Path(__file__).with_name('check-qotom-handoff-capture.py').read_bytes()).hexdigest()
    if acpi:
        result['acpi_decoder_sha256'] = hashlib.sha256(
            Path(__file__).with_name('check-qotom-acpi-capture.py').read_bytes()).hexdigest()
    if pci_read_trace:
        result['pci_read_decoder_sha256'] = hashlib.sha256(
            Path(__file__).with_name('check-qotom-pci-read-trace.py').read_bytes()).hexdigest()
    if bootstrap:
        result['bootstrap_decoder_sha256'] = hashlib.sha256(
            Path(__file__).with_name('check-qotom-bootstrap-capture.py').read_bytes()).hexdigest()
    if ecam_memory:
        result['ecam_memory_decoder_sha256'] = hashlib.sha256(
            Path(__file__).with_name('check-qotom-ecam-memory-capture.py').read_bytes()).hexdigest()
    return result


def classify_cpu_protected(events, digest, protocol_path, replay, pci_replay=None, handoff=False, acpi=False, pci_read_trace=False, bootstrap=False, ecam_memory=False, dsdt=False, ecam_read=False, native_inventory=False, native_kernel=False, bsp_replay=None, pci_capabilities=False, af_observation=False, ehci_capabilities=False, ehci_legacy=False, ehci_handoff=False, ehci_smi=False, ehci_operational=False, ehci_bme=False, xhci_capabilities=False, xhci_legacy=False, xhci_handoff=False, xhci_smi=False, xhci_operational=False, xhci_bme=False, pcie_device_observation=False, ahci_capabilities=False, ahci_port=False, ahci_interrupts=False, ahci_bme=False, hda_observation=False, hda_state=False, hda_bme=False, txe_status=False, rootport_bme=False, realtek_state=False, realtek_bme=False):
    if realtek_bme and not realtek_state:
        raise ValueError('--realtek-bme requires --realtek-state')
    if realtek_state and not rootport_bme:
        raise ValueError('--realtek-state requires --rootport-bme')
    if rootport_bme and not txe_status:
        raise ValueError('--rootport-bme requires --txe-status')
    if txe_status and not hda_bme:
        raise ValueError('--txe-status requires --hda-bme')
    if hda_bme and not hda_state:
        raise ValueError('--hda-bme requires --hda-state')
    if hda_state and not hda_observation:
        raise ValueError('--hda-state requires --hda-observation')
    if hda_observation and not ahci_bme:
        raise ValueError('--hda-observation requires --ahci-bme')
    if ahci_bme and not ahci_interrupts:
        raise ValueError('--ahci-bme requires --ahci-interrupts')
    if ahci_interrupts and not ahci_port:
        raise ValueError('--ahci-interrupts requires --ahci-port')
    if ahci_port and not ahci_capabilities:
        raise ValueError('--ahci-port requires --ahci-capabilities')
    if ahci_capabilities and not pcie_device_observation:
        raise ValueError('--ahci-capabilities requires --pcie-device-observation')
    if pcie_device_observation and not xhci_bme:
        raise ValueError('--pcie-device-observation requires --xhci-bme')
    if xhci_bme and not xhci_operational:
        raise ValueError('xHCI BME requires operational observation')
    if xhci_operational and not xhci_smi:
        raise ValueError('xHCI operational requires SMI')
    if xhci_smi and not xhci_handoff:
        raise ValueError('xHCI SMI requires handoff')
    if xhci_handoff and not xhci_legacy:
        raise ValueError('xHCI handoff requires legacy observations')
    if xhci_legacy and not xhci_capabilities:
        raise ValueError('xHCI legacy requires capability observations')
    if xhci_capabilities and not ehci_bme:
        raise ValueError('xHCI observation requires EHCI BME capture')
    if ehci_bme and not ehci_operational:
        raise ValueError('BME observation requires operational capture')
    if ehci_operational and not ehci_smi:
        raise ValueError('operational observation requires SMI capture')
    if ehci_smi and not ehci_handoff:
        raise ValueError('EHCI SMI disable requires handoff capture')
    if ehci_handoff and not ehci_legacy:
        raise ValueError('EHCI handoff requires legacy capture')
    if ehci_legacy and not ehci_capabilities:
        raise ValueError('EHCI legacy requires EHCI capabilities')
    if ehci_capabilities and not af_observation:
        raise ValueError('EHCI capture requires AF observation')
    if af_observation and not pci_capabilities:
        raise ValueError('AF observation requires capability capture')
    if pci_capabilities and not native_kernel:
        raise ValueError('capability capture requires native kernel inventory')
    if bsp_replay is not None and not native_kernel:
        raise ValueError('native BSP replay requires kernel native inventory')
    if native_kernel and not native_inventory:
        raise ValueError('kernel native inventory requires native replay selection')
    if native_inventory and not ecam_read:
        raise ValueError('native inventory requires ECAM capture')
    if ecam_read and (not dsdt or not ecam_memory or pci_read_trace):
        raise ValueError('ECAM read requires DSDT/memory capture and excludes PCI trace')
    if dsdt and not acpi:
        raise ValueError('DSDT capture requires ACPI capture')
    if ecam_memory and not bootstrap:
        raise ValueError('ECAM memory capture requires bootstrap capture')
    if bootstrap and pci_replay is None:
        raise ValueError('bootstrap capture requires PCI replay')
    if pci_read_trace and pci_replay is None:
        raise ValueError('PCI read trace requires PCI replay')
    if acpi and not handoff:
        raise ValueError('ACPI capture requires raw handoff')
    module = cpu_replay_module(pci_replay is not None)
    protocol = module.load_protocol(protocol_path)
    expected, raw = cpu_diagnostic_bytes(events, protocol, handoff)
    result = classify_protected(events, digest, expected, protocol['BOOT'].encode('ascii'))
    replay_paths = [Path(replay).resolve()]
    if pci_replay is not None:
        replay_paths.append(Path(pci_replay).resolve())
    if handoff:
        decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-handoff-capture.py')))
        mode = EXPECTED[:-len(EXPECTED_KERNEL)]
        _, handoff_bytes, result['handoff'] = decoder['parse_prefix'](expected[len(mode):])
    if acpi:
        decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-acpi-capture.py')))
        raw, result['acpi'], tables = decoder['extract'](raw, handoff_bytes, dsdt=dsdt)
    bsp_rejected = False
    if bsp_replay is not None:
        decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-bsp-capture.py')))
        raw, result['native_bsp'] = decoder['extract'](raw, protocol, result['acpi'], tables, Path(bsp_replay).resolve())
        bsp_rejected = result['native_bsp'] is not None and result['native_bsp']['observation']['status'] != 0
    if realtek_bme:
        decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-realtek-bme-capture.py')))
        raw, result['realtek_bme'] = decoder['extract'](raw, protocol)
    if realtek_state:
        decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-realtek-state-capture.py')))
        raw, result['realtek_state'] = decoder['extract'](raw, protocol)
    if rootport_bme:
        decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-rootport-bme-capture.py')))
        raw, result['rootport_bme'] = decoder['extract'](raw, protocol)
    if txe_status:
        decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-txe-status-capture.py')))
        raw, result['txe_status'] = decoder['extract'](raw, protocol)
    if hda_bme:
        decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-hda-bme-capture.py')))
        raw, result['hda_bme'] = decoder['extract'](raw, protocol)
    if hda_state:
        decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-hda-state-capture.py')))
        raw, result['hda_state'] = decoder['extract'](raw, protocol)
    if hda_observation:
        decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-hda-capture.py')))
        raw, result['hda'] = decoder['extract'](raw, protocol)
    if ahci_bme:
        decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-ahci-bme-capture.py')))
        raw, result['ahci_bme'] = decoder['extract'](raw, protocol)
    if ahci_interrupts:
        decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-ahci-interrupt-capture.py')))
        raw, result['ahci_interrupts'] = decoder['extract'](raw, protocol)
    if ahci_port:
        decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-ahci-port-capture.py')))
        raw, result['ahci_port'] = decoder['extract'](raw, protocol)
    if ahci_capabilities:
        decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-ahci-capture.py')))
        raw, result['ahci_capabilities'] = decoder['extract'](raw, protocol)
    if pcie_device_observation:
        decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-pcie-device-capture.py')))
        raw, result['pcie_device'] = decoder['extract'](raw, protocol)
    if xhci_bme:
        decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-xhci-bme-capture.py')))
        raw, result['xhci_bme'] = decoder['extract'](raw, protocol)
    if xhci_operational:
        decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-xhci-operational-capture.py')))
        raw, result['xhci_operational'] = decoder['extract'](raw, protocol)
    if xhci_smi:
        decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-xhci-smi-capture.py')))
        raw, result['xhci_smi'] = decoder['extract'](raw, protocol)
    if xhci_handoff:
        decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-xhci-handoff-capture.py')))
        raw, result['xhci_handoff'] = decoder['extract'](raw, protocol)
    if xhci_legacy:
        decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-xhci-legacy-capture.py')))
        raw, result['xhci_legacy'] = decoder['extract'](raw, protocol)
    if xhci_capabilities:
        decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-xhci-capture.py')))
        raw, result['xhci_capabilities'] = decoder['extract'](raw, protocol)
    if ehci_bme:
        decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-ehci-bme-capture.py')))
        raw, result['ehci_bme'] = decoder['extract'](raw, protocol)
    if ehci_operational:
        decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-ehci-operational-capture.py')))
        raw, result['ehci_operational'] = decoder['extract'](raw, protocol)
    if ehci_smi:
        decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-ehci-smi-capture.py')))
        raw, result['ehci_smi'] = decoder['extract'](raw, protocol)
    if ehci_handoff:
        decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-ehci-handoff-capture.py')))
        raw, result['ehci_handoff'] = decoder['extract'](raw, protocol)
    if ehci_legacy:
        decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-ehci-legacy-capture.py')))
        raw, result['ehci_legacy'] = decoder['extract'](raw, protocol)
    if ehci_capabilities:
        decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-ehci-capture.py')))
        raw, result['ehci_capabilities'] = decoder['extract'](raw, protocol)
    if af_observation:
        decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-af-capture.py')))
        raw, result['af_observation'] = decoder['extract'](raw, protocol)
    if pci_capabilities:
        decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-pci-capabilities-capture.py')))
        raw, result['pci_capabilities'] = decoder['extract'](raw, protocol)
    if ecam_read:
        decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-ecam-capture.py')))
        raw, result['ecam'] = decoder['extract'](raw, protocol, result['acpi'], tables, bsp_failure=bsp_rejected)
    if ecam_memory:
        decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-ecam-memory-capture.py')))
        raw, result['ecam_memory'] = decoder['extract'](raw, protocol, ecam_failure=ecam_read, bsp_failure=bsp_rejected)
    if bootstrap:
        decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-bootstrap-capture.py')))
        raw, result['bootstrap'] = decoder['extract'](raw, protocol, ecam_failure=ecam_read, bsp_failure=bsp_rejected)
    if pci_read_trace:
        decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-pci-read-trace.py')))
        raw, result['pci_read_trace'] = decoder['extract'](raw, protocol)
    ecam_terminal = ecam_read and any(raw.endswith(protocol['FINAL'].encode() +
        b' status=FAIL reason=' + reason + b'\n') for reason in
        (b'qotom-ecam-arm', b'qotom-ecam-transaction'))
    if ecam_terminal or bsp_rejected:
        # Replay only the CPU/MSR prefix; retain the actual BSP/ECAM terminal.
        projection = raw.replace(b'phase=pci-inventory-diagnostic', b'phase=cpu-diagnostic', 1)
        diagnostic = module.CPU.classify(projection, protocol, replay_paths[0], ecam_failure=ecam_terminal, bsp_failure=bsp_rejected)
        diagnostic['capture_sha256'] = hashlib.sha256(raw).hexdigest()
        diagnostic['replay_scope'] = 'cpu-msr-before-bsp-failure' if bsp_rejected else 'cpu-msr-before-ecam-failure'
    else:
        diagnostic = (module.classify(raw, protocol, *replay_paths, native_inventory=True, native_kernel=native_kernel)
                      if native_inventory else module.classify(raw, protocol, *replay_paths))
    diagnostic.update(cpu_replay_inputs(protocol_path, replay, pci_replay, handoff, acpi, pci_read_trace, bootstrap, ecam_memory, dsdt, ecam_read, native_inventory, native_kernel, bsp_replay, pci_capabilities, af_observation, ehci_capabilities, ehci_legacy, ehci_handoff, ehci_smi, ehci_operational, ehci_bme, xhci_capabilities, xhci_legacy, xhci_handoff, xhci_smi, xhci_operational, xhci_bme, pcie_device_observation, ahci_capabilities, ahci_port, ahci_interrupts, ahci_bme, hda_observation, hda_state, hda_bme, txe_status, rootport_bme, realtek_state, realtek_bme))
    if pci_capabilities and result['pci_capabilities'] is not None:
        diagnostic['terminal_reason'] = result['pci_capabilities']['terminal_reason']
        diagnostic['replay_scope'] = 'cpu-msr-native-inventory-and-capability-links'
    if af_observation and result['af_observation'] is not None:
        diagnostic['terminal_reason'] = result['af_observation']['terminal_reason']
        diagnostic['replay_scope'] = 'cpu-msr-native-inventory-capability-links-and-af-framing'
    if ehci_capabilities and result['ehci_capabilities'] is not None:
        diagnostic['terminal_reason'] = result['ehci_capabilities']['terminal_reason']
        diagnostic['replay_scope'] = 'native-inventory-capability-links-af-and-ehci-framing'
    if ehci_legacy and result['ehci_legacy'] is not None:
        diagnostic['terminal_reason'] = result['ehci_legacy']['terminal_reason']
        diagnostic['replay_scope'] = 'native-inventory-capabilities-af-ehci-and-legacy-links'
    if ehci_handoff and result['ehci_handoff'] is not None:
        diagnostic['terminal_reason'] = result['ehci_handoff']['terminal_reason']
        diagnostic['replay_scope'] = 'native-inventory-with-handoff-observation'
    if ehci_smi and result['ehci_smi'] is not None:
        diagnostic['terminal_reason'] = result['ehci_smi']['terminal_reason']
        diagnostic['replay_scope'] = 'native-inventory-with-handoff-and-smi-observations'
    if ehci_operational and result['ehci_operational'] is not None:
        diagnostic['terminal_reason'] = result['ehci_operational']['terminal_reason']
        diagnostic['replay_scope'] = 'native-inventory-with-ehci-operational-observations'
    if ehci_bme and result['ehci_bme'] is not None:
        diagnostic['terminal_reason'] = result['ehci_bme']['terminal_reason']
        diagnostic['replay_scope'] = 'native-inventory-with-ehci-bme-observations'
    if xhci_capabilities and result['xhci_capabilities'] is not None:
        diagnostic['terminal_reason'] = result['xhci_capabilities']['terminal_reason']
        diagnostic['replay_scope'] = 'native-inventory-with-xhci-capability-observations'
    if xhci_legacy and result['xhci_legacy'] is not None:
        diagnostic['terminal_reason'] = result['xhci_legacy']['terminal_reason']
        diagnostic['replay_scope'] = 'native-inventory-with-xhci-legacy-observations'
    if xhci_handoff and result['xhci_handoff'] is not None:
        diagnostic['terminal_reason'] = result['xhci_handoff']['terminal_reason']
        diagnostic['replay_scope'] = 'native-inventory-with-xhci-handoff-observation'
    if xhci_smi and result['xhci_smi'] is not None:
        diagnostic['terminal_reason'] = result['xhci_smi']['terminal_reason']
        diagnostic['replay_scope'] = 'native-inventory-with-xhci-smi-observation'
    if xhci_operational and result['xhci_operational'] is not None:
        diagnostic['terminal_reason'] = result['xhci_operational']['terminal_reason']
        diagnostic['replay_scope'] = 'native-inventory-with-xhci-operational-observation'
    if xhci_bme and result['xhci_bme'] is not None:
        diagnostic['terminal_reason'] = result['xhci_bme']['terminal_reason']
        diagnostic['replay_scope'] = 'native-inventory-with-xhci-bme-observation'
    if pcie_device_observation and result['pcie_device'] is not None:
        diagnostic['terminal_reason'] = result['pcie_device']['terminal_reason']
        diagnostic['replay_scope'] = 'native-inventory-with-pcie-device-observations'
    if ahci_capabilities and result['ahci_capabilities'] is not None:
        diagnostic['terminal_reason'] = result['ahci_capabilities']['terminal_reason']
        diagnostic['replay_scope'] = 'native-inventory-with-ahci-capability-observation'
    if ahci_port and result['ahci_port'] is not None:
        diagnostic['terminal_reason'] = result['ahci_port']['terminal_reason']
        diagnostic['replay_scope'] = 'native-inventory-with-ahci-port-observation'
    if ahci_interrupts and result['ahci_interrupts'] is not None:
        diagnostic['terminal_reason'] = result['ahci_interrupts']['terminal_reason']
        diagnostic['replay_scope'] = 'native-inventory-with-ahci-interrupt-observation'
    if ahci_bme and result['ahci_bme'] is not None:
        diagnostic['terminal_reason'] = result['ahci_bme']['terminal_reason']
        diagnostic['replay_scope'] = 'native-inventory-with-ahci-bme-observation'
    if hda_observation and result['hda'] is not None:
        diagnostic['terminal_reason'] = result['hda']['terminal_reason']
        diagnostic['replay_scope'] = 'native-inventory-with-hda-observation'
    if hda_state and result['hda_state'] is not None:
        diagnostic['terminal_reason'] = result['hda_state']['terminal_reason']
        diagnostic['replay_scope'] = 'native-inventory-with-hda-state-observation'
    if hda_bme and result['hda_bme'] is not None:
        diagnostic['terminal_reason'] = result['hda_bme']['terminal_reason']
        diagnostic['replay_scope'] = 'native-inventory-with-hda-bme-observation'
    if txe_status and result['txe_status'] is not None:
        diagnostic['terminal_reason'] = result['txe_status']['terminal_reason']
        diagnostic['replay_scope'] = 'native-inventory-with-txe-status-observation'
    if rootport_bme and result['rootport_bme'] is not None:
        diagnostic['terminal_reason'] = result['rootport_bme']['terminal_reason']
        diagnostic['replay_scope'] = 'native-inventory-with-rootport-bme-observation'
    if realtek_state and result['realtek_state'] is not None:
        diagnostic['terminal_reason'] = result['realtek_state']['terminal_reason']
        diagnostic['replay_scope'] = 'native-inventory-with-realtek-state-observation'
    if realtek_bme and result['realtek_bme'] is not None:
        diagnostic['terminal_reason'] = result['realtek_bme']['terminal_reason']
        diagnostic['replay_scope'] = 'native-inventory-with-realtek-bme-observation'
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
    parser.add_argument('--handoff-capture', action='store_true')
    parser.add_argument('--acpi-capture', action='store_true')
    parser.add_argument('--pci-read-trace', action='store_true')
    parser.add_argument('--bootstrap-capture', action='store_true')
    parser.add_argument('--ecam-memory-capture', action='store_true')
    parser.add_argument('--dsdt-capture', action='store_true')
    parser.add_argument('--ecam-read', action='store_true')
    parser.add_argument('--native-inventory', action='store_true')
    parser.add_argument('--native-kernel', action='store_true')
    parser.add_argument('--pci-capabilities', action='store_true')
    parser.add_argument('--af-observation', action='store_true')
    parser.add_argument('--realtek-bme', action='store_true')
    parser.add_argument('--realtek-state', action='store_true')
    parser.add_argument('--rootport-bme', action='store_true')
    parser.add_argument('--txe-status', action='store_true')
    parser.add_argument('--hda-bme', action='store_true')
    parser.add_argument('--hda-state', action='store_true')
    parser.add_argument('--hda-observation', action='store_true')
    parser.add_argument('--ahci-bme', action='store_true')
    parser.add_argument('--ahci-interrupts', action='store_true')
    parser.add_argument('--ahci-port', action='store_true')
    parser.add_argument('--ahci-capabilities', action='store_true')
    parser.add_argument('--pcie-device-observation', action='store_true')
    parser.add_argument('--xhci-bme', action='store_true')
    parser.add_argument('--xhci-operational', action='store_true')
    parser.add_argument('--xhci-smi', action='store_true')
    parser.add_argument('--xhci-handoff', action='store_true')
    parser.add_argument('--xhci-legacy', action='store_true')
    parser.add_argument('--xhci-capabilities', action='store_true')
    parser.add_argument('--ehci-bme', action='store_true')
    parser.add_argument('--ehci-operational', action='store_true')
    parser.add_argument('--ehci-smi', action='store_true')
    parser.add_argument('--ehci-handoff', action='store_true')
    parser.add_argument('--ehci-capabilities', action='store_true')
    parser.add_argument('--ehci-legacy', action='store_true')
    parser.add_argument('--bsp-replay', type=Path, help='enable native BSP capture and provide its generated replay executable')
    args = parser.parse_args()
    if args.realtek_bme and not args.realtek_state:
        parser.error('--realtek-bme requires --realtek-state')
    if args.realtek_state and not args.rootport_bme:
        parser.error('--realtek-state requires --rootport-bme')
    if args.rootport_bme and not args.txe_status:
        parser.error('--rootport-bme requires --txe-status')
    if args.txe_status and not args.hda_bme:
        parser.error('--txe-status requires --hda-bme')
    if args.hda_bme and not args.hda_state:
        parser.error('--hda-bme requires --hda-state')
    if args.hda_state and not args.hda_observation:
        parser.error('--hda-state requires --hda-observation')
    if args.hda_observation and not args.ahci_bme:
        parser.error('--hda-observation requires --ahci-bme')
    if args.ahci_bme and not args.ahci_interrupts:
        parser.error('--ahci-bme requires --ahci-interrupts')
    if args.ahci_interrupts and not args.ahci_port:
        parser.error('--ahci-interrupts requires --ahci-port')
    if args.ahci_port and not args.ahci_capabilities:
        parser.error('--ahci-port requires --ahci-capabilities')
    if args.ahci_capabilities and not args.pcie_device_observation:
        parser.error('--ahci-capabilities requires --pcie-device-observation')
    if args.pcie_device_observation and not args.xhci_bme:
        parser.error('--pcie-device-observation requires --xhci-bme')
    if args.xhci_bme and not args.xhci_operational:
        parser.error('--xhci-bme requires --xhci-operational')
    if args.xhci_operational and not args.xhci_smi:
        parser.error('--xhci-operational requires --xhci-smi')
    if args.xhci_smi and not args.xhci_handoff:
        parser.error('--xhci-smi requires --xhci-handoff')
    if args.xhci_handoff and not args.xhci_legacy:
        parser.error('--xhci-handoff requires --xhci-legacy')
    if args.xhci_legacy and not args.xhci_capabilities:
        parser.error('--xhci-legacy requires --xhci-capabilities')
    if args.xhci_capabilities and not args.ehci_bme:
        parser.error('--xhci-capabilities requires --ehci-bme')
    if args.ehci_bme and not args.ehci_operational:
        parser.error('--ehci-bme requires --ehci-operational')
    if args.ehci_operational and not args.ehci_smi:
        parser.error('--ehci-operational requires --ehci-smi')
    if args.ehci_smi and not args.ehci_handoff:
        parser.error('--ehci-smi requires --ehci-handoff')
    if args.ehci_handoff and not args.ehci_legacy:
        parser.error('--ehci-handoff requires --ehci-legacy')
    if args.ehci_legacy and not args.ehci_capabilities:
        parser.error('--ehci-legacy requires --ehci-capabilities')
    if args.ehci_capabilities and not args.af_observation:
        parser.error('--ehci-capabilities requires --af-observation')
    if args.af_observation and not args.pci_capabilities:
        parser.error('--af-observation requires --pci-capabilities')
    if args.pci_capabilities and not args.native_kernel:
        parser.error('--pci-capabilities requires --native-kernel')
    if args.bsp_replay is not None and not args.native_kernel:
        parser.error('--bsp-replay requires --native-kernel')
    if args.native_kernel and not args.native_inventory:
        parser.error('--native-kernel requires --native-inventory')
    if args.native_inventory and not args.ecam_read:
        parser.error('--native-inventory requires --ecam-read')
    if args.ecam_read and (not args.dsdt_capture or not args.ecam_memory_capture or args.pci_read_trace):
        parser.error('--ecam-read requires DSDT/memory capture and excludes PCI trace')
    if args.dsdt_capture and not args.acpi_capture:
        parser.error('--dsdt-capture requires --acpi-capture')
    if args.ecam_memory_capture and not args.bootstrap_capture:
        parser.error('--ecam-memory-capture requires --bootstrap-capture')
    if args.bootstrap_capture and not args.pci_diagnostic:
        parser.error('--bootstrap-capture requires --pci-diagnostic')
    if args.pci_read_trace and not args.pci_diagnostic:
        parser.error('--pci-read-trace requires --pci-diagnostic')
    if args.acpi_capture and not args.handoff_capture:
        parser.error('--acpi-capture requires --handoff-capture')
    if args.handoff_capture and not args.pci_diagnostic:
        parser.error('--handoff-capture requires --pci-diagnostic')
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
            if not args.native_inventory and not re.fullmatch(
                    rb'Hosted Qotom PCI inventory replay passed \([1-9][0-9]* cases\)\n'
                    rb'Collected PCI snapshots passed generated inventory admission and 32 negative cases\n',
                    selftest.stdout):
                parser.error('PCI replay did not report its corpus self-test')
            if args.native_inventory and selftest.stdout != b'Hosted native Qotom inventory replay passed\n':
                parser.error('native inventory replay did not report its corpus self-test')
            if cpu_replay_module().replay_words(pci_replay.resolve(), 'inventory', [0]) != 65536:
                parser.error('PCI replay lacks the bounded inventory interface')
        if args.bsp_replay is not None:
            identity = subprocess.run([str(args.bsp_replay.resolve()), '--identity'], capture_output=True, check=True, timeout=30)
            if identity.stdout != b'LeanOS native BSP replay v1\n':
                parser.error('native BSP replay identity mismatch')
        diagnostic_inputs = cpu_replay_inputs(args.diagnostic_protocol, args.diagnostic_replay, pci_replay, args.handoff_capture, args.acpi_capture, args.pci_read_trace, args.bootstrap_capture, args.ecam_memory_capture, args.dsdt_capture, args.ecam_read, args.native_inventory, args.native_kernel, args.bsp_replay, args.pci_capabilities, args.af_observation, args.ehci_capabilities, args.ehci_legacy, args.ehci_handoff, args.ehci_smi, args.ehci_operational, args.ehci_bme, args.xhci_capabilities, args.xhci_legacy, args.xhci_handoff, args.xhci_smi, args.xhci_operational, args.xhci_bme, args.pcie_device_observation, args.ahci_capabilities, args.ahci_port, args.ahci_interrupts, args.ahci_bme, args.hda_observation, args.hda_state, args.hda_bme, args.txe_status, args.rootport_bme, args.realtek_state, args.realtek_bme)
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
                if cpu_replay_inputs(args.diagnostic_protocol, args.diagnostic_replay, pci_replay, args.handoff_capture, args.acpi_capture, args.pci_read_trace, args.bootstrap_capture, args.ecam_memory_capture, args.dsdt_capture, args.ecam_read, args.native_inventory, args.native_kernel, args.bsp_replay, args.pci_capabilities, args.af_observation, args.ehci_capabilities, args.ehci_legacy, args.ehci_handoff, args.ehci_smi, args.ehci_operational, args.ehci_bme, args.xhci_capabilities, args.xhci_legacy, args.xhci_handoff, args.xhci_smi, args.xhci_operational, args.xhci_bme, args.pcie_device_observation, args.ahci_capabilities, args.ahci_port, args.ahci_interrupts, args.ahci_bme, args.hda_observation, args.hda_state, args.hda_bme, args.txe_status, args.rootport_bme, args.realtek_state, args.realtek_bme) != diagnostic_inputs:
                    raise ValueError('diagnostic replay inputs changed during capture')
                result = classify_cpu_protected(events, digest, args.diagnostic_protocol,
                                                args.diagnostic_replay, pci_replay, args.handoff_capture, args.acpi_capture, args.pci_read_trace, args.bootstrap_capture, args.ecam_memory_capture, args.dsdt_capture, args.ecam_read, args.native_inventory, args.native_kernel, args.bsp_replay, args.pci_capabilities, args.af_observation, args.ehci_capabilities, args.ehci_legacy, args.ehci_handoff, args.ehci_smi, args.ehci_operational, args.ehci_bme, args.xhci_capabilities, args.xhci_legacy, args.xhci_handoff, args.xhci_smi, args.xhci_operational, args.xhci_bme, args.pcie_device_observation, args.ahci_capabilities, args.ahci_port, args.ahci_interrupts, args.ahci_bme, args.hda_observation, args.hda_state, args.hda_bme, args.txe_status, args.rootport_bme, args.realtek_state, args.realtek_bme)
                protocol = cpu_replay_module(args.pci_diagnostic).load_protocol(args.diagnostic_protocol)
                expected, raw = cpu_diagnostic_bytes(events, protocol, args.handoff_capture)
                if args.handoff_capture:
                    decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-handoff-capture.py')))
                    mode = EXPECTED[:-len(EXPECTED_KERNEL)]
                    _, binary, metadata = decoder['parse_prefix'](expected[len(mode):])
                    (directory / 'multiboot2.bin').write_bytes(binary)
                    (directory / 'handoff.json').write_text(json.dumps(metadata, indent=2) + '\n')
                if args.acpi_capture:
                    decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-acpi-capture.py')))
                    raw, metadata, tables = decoder['extract'](raw, binary, dsdt=args.dsdt_capture)
                    (directory / 'acpi').mkdir()
                    for filename, content in tables.items():
                        (directory / 'acpi' / filename).write_bytes(content)
                    (directory / 'acpi.json').write_text(json.dumps(metadata, indent=2) + '\n')
                bsp_rejected = False
                if args.bsp_replay is not None:
                    decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-bsp-capture.py')))
                    raw, bsp_metadata = decoder['extract'](raw, protocol, metadata, tables, args.bsp_replay.resolve())
                    bsp_rejected = bsp_metadata is not None and bsp_metadata['observation']['status'] != 0
                    (directory / 'native-bsp.json').write_text(json.dumps(bsp_metadata, indent=2) + '\n')
                if args.realtek_bme:
                    decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-realtek-bme-capture.py')))
                    raw, realtek_bme_metadata = decoder['extract'](raw, protocol)
                    (directory / 'realtek-bme.json').write_text(json.dumps(realtek_bme_metadata, indent=2) + '\n')
                if args.realtek_state:
                    decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-realtek-state-capture.py')))
                    raw, realtek_state_metadata = decoder['extract'](raw, protocol)
                    (directory / 'realtek-state.json').write_text(json.dumps(realtek_state_metadata, indent=2) + '\n')
                if args.rootport_bme:
                    decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-rootport-bme-capture.py')))
                    raw, rootport_bme_metadata = decoder['extract'](raw, protocol)
                    (directory / 'rootport-bme.json').write_text(json.dumps(rootport_bme_metadata, indent=2) + '\n')
                if args.txe_status:
                    decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-txe-status-capture.py')))
                    raw, txe_status_metadata = decoder['extract'](raw, protocol)
                    (directory / 'txe-status.json').write_text(json.dumps(txe_status_metadata, indent=2) + '\n')
                if args.hda_bme:
                    decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-hda-bme-capture.py')))
                    raw, hda_bme_metadata = decoder['extract'](raw, protocol)
                    (directory / 'hda-bme.json').write_text(json.dumps(hda_bme_metadata, indent=2) + '\n')
                if args.hda_state:
                    decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-hda-state-capture.py')))
                    raw, hda_state_metadata = decoder['extract'](raw, protocol)
                    (directory / 'hda-state.json').write_text(json.dumps(hda_state_metadata, indent=2) + '\n')
                if args.hda_observation:
                    decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-hda-capture.py')))
                    raw, hda_metadata = decoder['extract'](raw, protocol)
                    (directory / 'hda.json').write_text(json.dumps(hda_metadata, indent=2) + '\n')
                if args.ahci_bme:
                    decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-ahci-bme-capture.py')))
                    raw, ahci_bme_metadata = decoder['extract'](raw, protocol)
                    (directory / 'ahci-bme.json').write_text(json.dumps(ahci_bme_metadata, indent=2) + '\n')
                if args.ahci_interrupts:
                    decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-ahci-interrupt-capture.py')))
                    raw, ahci_interrupt_metadata = decoder['extract'](raw, protocol)
                    (directory / 'ahci-interrupts.json').write_text(json.dumps(ahci_interrupt_metadata, indent=2) + '\n')
                if args.ahci_port:
                    decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-ahci-port-capture.py')))
                    raw, ahci_port_metadata = decoder['extract'](raw, protocol)
                    (directory / 'ahci-port.json').write_text(json.dumps(ahci_port_metadata, indent=2) + '\n')
                if args.ahci_capabilities:
                    decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-ahci-capture.py')))
                    raw, ahci_metadata = decoder['extract'](raw, protocol)
                    (directory / 'ahci-capabilities.json').write_text(json.dumps(ahci_metadata, indent=2) + '\n')
                if args.pcie_device_observation:
                    decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-pcie-device-capture.py')))
                    raw, pcie_device_metadata = decoder['extract'](raw, protocol)
                    (directory / 'pcie-device.json').write_text(json.dumps(pcie_device_metadata, indent=2) + '\n')
                if args.xhci_bme:
                    decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-xhci-bme-capture.py')))
                    raw, xhci_bme_metadata = decoder['extract'](raw, protocol)
                    (directory / 'xhci-bme.json').write_text(json.dumps(xhci_bme_metadata, indent=2) + '\n')
                if args.xhci_operational:
                    decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-xhci-operational-capture.py')))
                    raw, xhci_operational_metadata = decoder['extract'](raw, protocol)
                    (directory / 'xhci-operational.json').write_text(json.dumps(xhci_operational_metadata, indent=2) + '\n')
                if args.xhci_smi:
                    decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-xhci-smi-capture.py')))
                    raw, xhci_smi_metadata = decoder['extract'](raw, protocol)
                    (directory / 'xhci-smi.json').write_text(json.dumps(xhci_smi_metadata, indent=2) + '\n')
                if args.xhci_handoff:
                    decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-xhci-handoff-capture.py')))
                    raw, xhci_handoff_metadata = decoder['extract'](raw, protocol)
                    (directory / 'xhci-handoff.json').write_text(json.dumps(xhci_handoff_metadata, indent=2) + '\n')
                if args.xhci_legacy:
                    decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-xhci-legacy-capture.py')))
                    raw, xhci_legacy_metadata = decoder['extract'](raw, protocol)
                    (directory / 'xhci-legacy.json').write_text(json.dumps(xhci_legacy_metadata, indent=2) + '\n')
                if args.xhci_capabilities:
                    decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-xhci-capture.py')))
                    raw, xhci_metadata = decoder['extract'](raw, protocol)
                    (directory / 'xhci-capabilities.json').write_text(json.dumps(xhci_metadata, indent=2) + '\n')
                if args.ehci_bme:
                    decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-ehci-bme-capture.py')))
                    raw, bme_metadata = decoder['extract'](raw, protocol)
                    (directory / 'ehci-bme.json').write_text(json.dumps(bme_metadata, indent=2) + '\n')
                if args.ehci_operational:
                    decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-ehci-operational-capture.py')))
                    raw, operational_metadata = decoder['extract'](raw, protocol)
                    (directory / 'ehci-operational.json').write_text(json.dumps(operational_metadata, indent=2) + '\n')
                if args.ehci_smi:
                    decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-ehci-smi-capture.py')))
                    raw, smi_metadata = decoder['extract'](raw, protocol)
                    (directory / 'ehci-smi.json').write_text(json.dumps(smi_metadata, indent=2) + '\n')
                if args.ehci_handoff:
                    decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-ehci-handoff-capture.py')))
                    raw, handoff_metadata = decoder['extract'](raw, protocol)
                    (directory / 'ehci-handoff.json').write_text(json.dumps(handoff_metadata, indent=2) + '\n')
                if args.ehci_legacy:
                    decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-ehci-legacy-capture.py')))
                    raw, legacy_metadata = decoder['extract'](raw, protocol)
                    (directory / 'ehci-legacy.json').write_text(json.dumps(legacy_metadata, indent=2) + '\n')
                if args.ehci_capabilities:
                    decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-ehci-capture.py')))
                    raw, ehci_metadata = decoder['extract'](raw, protocol)
                    (directory / 'ehci-capabilities.json').write_text(json.dumps(ehci_metadata, indent=2) + '\n')
                if args.af_observation:
                    decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-af-capture.py')))
                    raw, af_metadata = decoder['extract'](raw, protocol)
                    (directory / 'af-observation.json').write_text(json.dumps(af_metadata, indent=2) + '\n')
                if args.pci_capabilities:
                    decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-pci-capabilities-capture.py')))
                    raw, caps_metadata = decoder['extract'](raw, protocol)
                    (directory / 'pci-capabilities.json').write_text(json.dumps(caps_metadata, indent=2) + '\n')
                if args.ecam_read:
                    decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-ecam-capture.py')))
                    raw, ecam_metadata = decoder['extract'](raw, protocol, metadata, tables, bsp_failure=bsp_rejected)
                    (directory / 'ecam.json').write_text(json.dumps(ecam_metadata, indent=2) + '\n')
                if args.ecam_memory_capture:
                    decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-ecam-memory-capture.py')))
                    raw, metadata = decoder['extract'](raw, protocol, ecam_failure=args.ecam_read, bsp_failure=bsp_rejected)
                    (directory / 'ecam-memory.json').write_text(json.dumps(metadata, indent=2) + '\n')
                if args.bootstrap_capture:
                    decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-bootstrap-capture.py')))
                    raw, metadata = decoder['extract'](raw, protocol, ecam_failure=args.ecam_read, bsp_failure=bsp_rejected)
                    (directory / 'bootstrap.json').write_text(json.dumps(metadata, indent=2) + '\n')
                if args.pci_read_trace:
                    decoder = runpy.run_path(str(Path(__file__).with_name('check-qotom-pci-read-trace.py')))
                    raw, metadata = decoder['extract'](raw, protocol)
                    (directory / 'pci-read-trace.json').write_text(json.dumps(metadata, indent=2) + '\n')
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
