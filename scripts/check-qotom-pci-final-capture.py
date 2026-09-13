#!/usr/bin/env python3
"""Validate the final Qotom PCI observation and explicit assumption checkpoint."""
import re
import runpy
from pathlib import Path

D=runpy.run_path(str(Path(__file__).with_name('check-qotom-txe-bme-capture.py')))
PREFIX=b'LEANOS-LAB/1 PCI-FINAL '
DEC=rb'(0|[1-9][0-9]{0,9})'
COMMANDS=(7,3,3,2,258,2,3,3,3,3,1026,7,3,3,0,3)

def extract(raw,protocol,trust_contract=False):
    if len(raw)>131072 or not raw.endswith(b'\n'):raise ValueError('PCI final capture bounds')
    lines=raw.splitlines(keepends=True)
    positions=[i for i,line in enumerate(lines) if line.startswith(PREFIX)]
    terminal_reason=b'qotom-nosmap-pending' if trust_contract else b'qotom-pci-assumptions'
    assumptions=protocol['FINAL'].encode()+b' status=FAIL reason='+terminal_reason+b'\n'
    prior_terminal=protocol['FINAL'].encode()+b' status=FAIL reason=qotom-platform-pending\n'
    if positions!=[len(lines)-2] or lines[-1]!=assumptions:
        raise ValueError('PCI final record order or terminal')
    contract=(rb' contract=qotom-j1900-pci-trust-v1 contract-accepted='+DEC
              if trust_contract else b'')
    pattern=(PREFIX+rb'profile=qotom-pci-final-v1 status='+DEC+rb' index='+DEC+
        rb' count='+DEC+rb' commands-accepted='+DEC+rb' assumption-mask='+DEC+
        rb' admitted='+DEC+contract+rb' commands='+rb'([0-9]+(?:,[0-9]+){15})'+
        rb' vtd=not-applicable platform-admitted='+DEC+rb'\n')
    match=re.fullmatch(pattern,lines[-2])
    if not match:raise ValueError('PCI final framing')
    status,index,count,commands_accepted,assumption_mask,admitted=map(int,match.groups()[:6])
    contract_accepted=int(match.group(7)) if trust_contract else 0
    commands=tuple(map(int,match.group(8 if trust_contract else 7).split(b',')))
    platform_admitted=int(match.group(9 if trust_contract else 8))
    expected=(0,16,16,1,31,1) if trust_contract else (6,16,16,1,3,0)
    if ((status,index,count,commands_accepted,assumption_mask,admitted)!=expected or
            commands!=COMMANDS or contract_accepted!=(1 if trust_contract else 0) or
            platform_admitted!=(1 if trust_contract else 0)):
        raise ValueError('PCI final result')
    projection=b''.join(lines[:-2])+prior_terminal
    _,previous=D['extract'](projection,protocol)
    if previous is None or previous['status']!=0 or not previous['host_visible_bme_cleared']:
        raise ValueError('PCI final without successful TXE BME')
    metadata={
        'schema':'leanos-qotom-pci-final-observation-v1','status':status,
        'index':index,'count':count,'commands':list(commands),
        'commands_accepted':True,'assumption_mask':assumption_mask,
        'fixed_infrastructure_noninitiating_assumed':True,'lpc_no_dma_assumed':True,
        'posted_writes_drained':False,'txe_private_dma_quiescent':False,
        'firmware_and_smm_noninterference':False,'vtd_applicable':False,
        'platform_admitted':bool(platform_admitted),
        'terminal_reason':terminal_reason.decode(),
        'hardware_operations_replayed':False,'fresh_complete_rescan_observed':True}
    if trust_contract:
        metadata.update(
            posted_writes_drained_assumed=True,
            txe_private_dma_quiescent_assumed=True,
            firmware_and_smm_noninterference_assumed=True,
            trust_contract='qotom-j1900-pci-trust-v1',
            trust_contract_accepted=bool(contract_accepted),
            dma_quarantine_admitted_under_contract=bool(admitted))
    return projection,metadata
