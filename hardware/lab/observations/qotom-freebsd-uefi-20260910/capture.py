from pathlib import Path
import datetime,hashlib,json,os,struct,subprocess
out=Path('/home/ruclaw/fun/serial/evidence/qotom-freebsd-uefi-firmware-20260910')
out.mkdir()
commands=[]
def run(command,name):
 p=subprocess.run(['sshpass','-e','ssh','-o','ConnectTimeout=8','-o','StrictHostKeyChecking=yes','-o','HostKeyAlias=freebsd.lan','freebsd@192.168.6.21',command],capture_output=True,timeout=30)
 commands.append(dict(command=command,file=name,returncode=p.returncode,sha256=hashlib.sha256(p.stdout).hexdigest(),stderr=p.stderr.decode(errors='replace')))
 (out/'commands.json').write_text(json.dumps(commands,indent=2)+'\n')
 if p.returncode: raise RuntimeError(command+': '+p.stderr.decode(errors='replace'))
 path=out/name; path.parent.mkdir(parents=True,exist_ok=True); path.write_bytes(p.stdout)
 return p.stdout
before=run('uname -sr; sysctl -n machdep.bootmethod kern.boottime','system-before.txt')
assert b'UEFI\n' in before
raw=run('sysctl -b machdep.efi_map','efi-map.bin')
size,stride,version=struct.unpack_from('<QQI',raw)
assert version==1 and 40<=stride<=256 and 0<size<=65536 and size%stride==0 and len(raw)==32+size
regions=[]
for i in range(size//stride):
 kind,base,virtual,pages,attr=struct.unpack_from('<I4xQQQQ',raw,32+i*stride)
 assert pages>0 and base%4096==0 and base+pages*4096<=2**64
 regions.append(dict(index=i,type=kind,base=base,length=pages*4096,virtual=virtual,attributes=attr))
(out/'efi-map.json').write_text(json.dumps(regions,indent=2)+'\n')
root_addr=int(run('sysctl -n machdep.acpi_root','acpi-root-address.txt').strip(),0)
total=0
def read(addr,count,name):
 global total
 assert 0<count<=65536 and total+count<=1048576
 assert any(r['type'] in (9,10) and r['base']<=addr and addr+count<=r['base']+r['length'] for r in regions),hex(addr)
 total+=count
 b=run(f'sudo -n dd if=/dev/mem bs=1 skip={addr} count={count} status=none',name)
 assert len(b)==count
 return b
rsdp=read(root_addr,36,'acpi/RSDP.bin')
assert rsdp[:8]==b'RSD PTR ' and sum(rsdp[:20])%256==0 and rsdp[15]==2 and struct.unpack_from('<I',rsdp,20)[0]==36 and sum(rsdp)%256==0
rsdt=struct.unpack_from('<I',rsdp,16)[0]; xsdt=struct.unpack_from('<Q',rsdp,24)[0]
tables={}
def table(addr,name):
 header=read(addr,36,'headers/'+name+'.bin')
 size=struct.unpack_from('<I',header,4)[0]
 assert 36<=size<=65536
 b=read(addr,size,'acpi/'+name+'.bin')
 assert b[:36]==header and sum(b)%256==0
 tables[str(addr)]=dict(signature=b[:4].decode('ascii'),length=size,file='acpi/'+name+'.bin',sha256=hashlib.sha256(b).hexdigest())
 return b
refs=set()
for addr,sig,width in ((rsdt,'RSDT',4),(xsdt,'XSDT',8)):
 if not addr: continue
 b=table(addr,sig)
 assert b[:4]==sig.encode() and (len(b)-36)%width==0 and (len(b)-36)//width<=256
 refs.update(int.from_bytes(b[i:i+width],'little') for i in range(36,len(b),width))
for addr in sorted(refs):
 assert addr>0
 table(addr,'root-tables/'+f'{addr:016x}')
for addr,meta in tables.items():
 b=read(int(addr),meta['length'],'repeat/'+Path(meta['file']).name)
 assert hashlib.sha256(b).hexdigest()==meta['sha256']
assert read(root_addr,36,'repeat/RSDP.bin')==rsdp
assert run('sysctl -b machdep.efi_map','repeat/efi-map.bin')==raw
assert run('uname -sr; sysctl -n machdep.bootmethod kern.boottime','system-after.txt')==before
run('sysctl -n kern.smp.cpus','processor-count.txt')
run('sudo -n acpidump -t -T APIC','apic-decoded.txt')
(out/'capture.json').write_text(json.dumps(dict(captured_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),source='Live FreeBSD UEFI loader metadata and read-only ACPI physical memory; not a GRUB handoff',capture_tool_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),rsdp_address=root_addr,rsdt_address=rsdt,xsdt_address=xsdt,tables=tables,physical_bytes_read=total,files={str(p.relative_to(out)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(out.rglob('*')) if p.is_file()}),indent=2)+'\n')
print('Captured',len(regions),'EFI descriptors and',len(tables),'ACPI SDTs; all checksums/repeated reads matched')
