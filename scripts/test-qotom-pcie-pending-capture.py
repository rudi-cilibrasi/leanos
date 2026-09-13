#!/usr/bin/env python3
import runpy
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
D=runpy.run_path(str(Path(__file__).with_name('check-qotom-pcie-pending-capture.py')))
PCI=runpy.run_path(str(Path(__file__).with_name('check-qotom-pci-diagnostic.py')))
P=PCI['load_protocol'](ROOT/'hardware/lab/observations/qotom-native-pcie-pending-20260912/diagnostic-protocol.tsv')
BASE=b'prefix\n'
BASE_STATUS=(17,17,17,16,25,25)
PD=b''.join((f'LEANOS-LAB/1 PCIE-DEVICE profile=qotom-pcie-device-v1 index={index} '
    f'status=0 offset=64 capability=32768 control-status={status << 16}\n').encode()
    for index,status in zip(D['INDICES'],BASE_STATUS))
RB=(b'LEANOS-LAB/1 REALTEK-BME profile=qotom-realtek-bme-v1 index=13 status=0 attempted=1 before=7 after=3\n'
    b'LEANOS-LAB/1 REALTEK-BME profile=qotom-realtek-bme-v1 index=15 status=0 attempted=1 before=7 after=3\n')
RS=(b'LEANOS-LAB/1 REALTEK-STATE profile=qotom-realtek-state-v1 index=13 status=0 transmit-before=797969664 command-before=0 interrupt-mask=0 receive=196366 command-after=0 transmit-after=797969664\n'
    b'LEANOS-LAB/1 REALTEK-STATE profile=qotom-realtek-state-v1 index=15 status=0 transmit-before=797969664 command-before=0 interrupt-mask=0 receive=196366 command-after=0 transmit-after=797969664\n')

# Build a syntactically valid predecessor by replacing the nested decoder used
# here; its exact state/BME framing is covered by the predecessor's own suite.
class Prior:
    @staticmethod
    def extract(raw,protocol):
        final=protocol['FINAL'].encode()+b' status=FAIL reason=qotom-platform-pending\n'
        if not raw.endswith(final):raise ValueError('prior terminal')
        return raw,{'functions':[{'status':0},{'status':0}]}
D['D']['extract']=Prior.extract

def line(slot,status=0,polls=2,device=None):
    index=D['INDICES'][slot];base=BASE_STATUS[slot]
    if device is None:device=base
    return (f'LEANOS-LAB/1 PCIE-PENDING profile=qotom-pcie-pending-v1 index={index} '
        f'status={status} polls={polls} device-status={device}\n').encode()

pending=P['FINAL'].encode()+b' status=FAIL reason=qotom-platform-pending\n'
success=BASE+PD+RS+RB+b''.join(line(i) for i in range(6))+pending
projection,metadata=D['extract'](success,P)
assert projection==BASE+PD+RS+RB+pending
assert metadata['nonposted_quiet_observed'] and not metadata['transaction_drain_established']
assert [f['index'] for f in metadata['functions']]==[6,7,8,9,13,15]
for slot in range(6):
    failure=BASE+PD+RS+RB+b''.join(line(i) for i in range(slot))+line(slot,7,100,BASE_STATUS[slot]|0x20)+P['FINAL'].encode()+b' status=FAIL reason=qotom-pcie-pending\n'
    _,m=D['extract'](failure,P);assert m['functions'][-1]['transactions_pending']
mutations=[
    success.replace(b'index=6 ',b'index=5 ',1),
    success.replace(b'polls=2 ',b'polls=1 ',1),
    success.replace(b'device-status=17',b'device-status=49',1),
    success.replace(line(0),line(0).replace(b'status=0 ',b'status=1 '),1),
    success.replace(line(1),b'',1),
    success.replace(line(0),line(0)+line(0),1),
    success.replace(b'qotom-platform-pending',b'qotom-pcie-pending',1),
]
mutations += [
    success.replace(PD.splitlines(keepends=True)[0],b'',1),
    success.replace(b'control-status=1114112',b'control-status=1048576',1),
]
for number,raw in enumerate(mutations):
    try:D['extract'](raw,P)
    except ValueError:pass
    else:raise AssertionError(f'accepted mutated PCIe pending capture {number}')
print('PASS PCIe pending decoder: exact six-function order, failure prefix and scalar bounds')
