#!/usr/bin/env python3
import runpy
from pathlib import Path

D=runpy.run_path(str(Path(__file__).with_name('check-qotom-pcie-pending-capture.py')))
P={'FINAL':'LEANOS/3 FINAL'}
BASE=b'prefix\n'
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
    index=D['INDICES'][slot];base=D['BASE_STATUS'][slot]
    if device is None:device=base
    return (f'LEANOS-LAB/1 PCIE-PENDING profile=qotom-pcie-pending-v1 index={index} '
        f'status={status} polls={polls} device-status={device}\n').encode()

pending=P['FINAL'].encode()+b' status=FAIL reason=qotom-platform-pending\n'
success=BASE+RS+RB+b''.join(line(i) for i in range(6))+pending
projection,metadata=D['extract'](success,P)
assert projection==BASE+RS+RB+pending
assert metadata['nonposted_quiet_observed'] and not metadata['transaction_drain_established']
assert [f['index'] for f in metadata['functions']]==[6,7,8,9,13,15]
for slot in range(6):
    failure=BASE+RS+RB+b''.join(line(i) for i in range(slot))+line(slot,7,100,D['BASE_STATUS'][slot]|0x20)+P['FINAL'].encode()+b' status=FAIL reason=qotom-pcie-pending\n'
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
for number,raw in enumerate(mutations):
    try:D['extract'](raw,P)
    except ValueError:pass
    else:raise AssertionError(f'accepted mutated PCIe pending capture {number}')
print('PASS PCIe pending decoder: exact six-function order, failure prefix and scalar bounds')
