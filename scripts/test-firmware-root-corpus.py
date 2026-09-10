#!/usr/bin/env python3
"""Exercise normalization using the checked raw root captures."""
import importlib.util
import json
import hashlib
import sys
from pathlib import Path
import shutil
import tempfile
import subprocess
import unittest
import firmware_root_corpus as roots

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('corpus', ROOT/'scripts/firmware-corpus.py')
corpus = importlib.util.module_from_spec(spec)
spec.loader.exec_module(corpus)

class RootCorpusTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.case = Path(self.temp.name)/'capture'
        shutil.copytree(ROOT/'firmware-corpus/qemu-seabios-q35-roots-1cpu', self.case)
        self.info = corpus.multiboot2_information(corpus.read_memmap(self.case/'memmap.tsv'))

    def replay(self): return roots.from_capture(self.case, self.info)

    def manifest(self):
        manifest=json.loads((ROOT/'firmware-corpus/manifest.json').read_text())
        case=next(c for c in manifest['cases'] if c['id']=='qemu-seabios-q35-roots-1cpu')
        case['id']='capture';manifest['cases']=[case]
        return manifest

    def run_manifest(self, manifest, command='validate'):
        path=Path(self.temp.name)/'manifest.json';path.write_text(json.dumps(manifest))
        args=[sys.executable,str(ROOT/'scripts/firmware-corpus.py'),'--manifest',str(path),command]
        if command=='normalize':args+=['--out',str(Path(self.temp.name)/'normalized')]
        return subprocess.run(args,text=True,capture_output=True)

    def test_source_hash_drift_has_case_local_failure(self):
        path=self.case/'acpi/RSDT.bin';path.write_bytes(path.read_bytes()+b'\0')
        result=self.run_manifest(self.manifest())
        self.assertNotEqual(result.returncode,0)
        self.assertIn('case capture',result.stderr)
        self.assertIn('does not match its recorded sha256',result.stderr)

    def test_root_reason_drift_rejected(self):
        manifest=self.manifest()
        manifest['cases'][0]['root_mutations']['root-checksum']['words'][3]=3
        result=self.run_manifest(manifest)
        self.assertNotEqual(result.returncode,0)
        self.assertIn('root result disagrees with words',result.stderr)

    def test_missing_root_mutation_rejected(self):
        manifest=self.manifest();del manifest['cases'][0]['root_mutations']['root-checksum']
        result=self.run_manifest(manifest)
        self.assertNotEqual(result.returncode,0)
        self.assertIn('must pin every derived root mutation',result.stderr)

    def test_normalized_mutation_digest_drift_rejected(self):
        manifest=self.manifest()
        manifest['cases'][0]['root_mutations']['root-checksum']['normalized_sha256']='0'*64
        result=self.run_manifest(manifest,'normalize')
        self.assertNotEqual(result.returncode,0)
        self.assertIn('case capture: normalized root-checksum bytes differ',result.stderr)


    def test_abi_renderer_limits_supported_array_shapes(self):
        prefix='leanos-abi\t1\nexport\tleanos_scalar\t1\ttest\tTest.scalar\n'
        for shape, accepted in [('Array.{0} UInt64',True),('Array.{0} ByteArray',True),
                                ('Array.{0} Nat',False),('Array.{0} UInt32',False)]:
            with self.subTest(shape=shape):
                data=prefix+f'object-export\tleanos_object\t{shape},u64\ttest\tTest.object\n'
                result=subprocess.run(['awk','-f',str(ROOT/'scripts/render-boundary-abi.awk')],
                                      input=data,text=True,capture_output=True)
                self.assertEqual(result.returncode==0,accepted,result.stderr)

    def test_same_bytes_independent_of_output_directory(self):
        a, b = self.replay(), self.replay()
        self.assertEqual(a.digest(), b.digest())
        for target in ('one', 'two'): a.write(Path(self.temp.name)/target)
        for p in (Path(self.temp.name)/'one').glob('*.bin'):
            self.assertEqual(p.read_bytes(), (Path(self.temp.name)/'two'/p.name).read_bytes())

    def test_root_vector_order_and_exact_copies_preserved(self):
        r = self.replay()
        vector = [int.from_bytes(r.root[o:o+4], 'little') for o in range(36,len(r.root),4)]
        self.assertEqual([a for a,_ in r.tables],vector)
        for a,b in r.tables:
            self.assertEqual(b,(self.case/f'acpi/root-tables/{a:016x}.bin').read_bytes())

    def test_copy_drift_changes_normalized_digest(self):
        before=self.replay().digest()
        p=next((self.case/'acpi/root-tables').glob('*.bin'))
        b=bytearray(p.read_bytes());b[-1]^=1;p.write_bytes(b)
        self.assertNotEqual(before,self.replay().digest())

    def test_missing_copy_rejected(self):
        next((self.case/'acpi/root-tables').glob('*.bin')).unlink()
        with self.assertRaises(OSError):self.replay()

    def test_symlinked_copy_rejected(self):
        p=next((self.case/'acpi/root-tables').glob('*.bin'))
        p.unlink();p.symlink_to(self.case/'acpi/APIC.bin')
        with self.assertRaises(ValueError):self.replay()

    def test_duplicate_physical_summary_rejected(self):
        p=self.case/'acpi/addresses.txt';s=p.read_text();p.write_text(s+s)
        with self.assertRaises(ValueError):self.replay()

    def test_mutations_do_not_modify_the_captured_input(self):
        base=self.replay(); before=base.digest()
        variants=roots.mutations(base)
        self.assertEqual(base.digest(),before)
        self.assertEqual(before,self.replay().digest())
        self.assertTrue(all(v.digest()!=before for v in variants.values()))
        self.assertEqual(len({v.digest() for v in variants.values()}),len(variants))

    def test_bsp_override_is_part_of_the_normalized_identity(self):
        from dataclasses import replace
        base=self.replay()
        self.assertNotEqual(base.digest(),replace(base,executing_override=255).digest())
        self.assertIn('255',roots.lean_query(replace(base,executing_override=255),0))

    def test_cpu_mutations_reach_topology_with_valid_tables(self):
        import struct

        def records(data):
            offset, result = 44, []
            while offset < len(data):
                size = data[offset+1]
                self.assertGreaterEqual(size, 2)
                self.assertLessEqual(offset+size, len(data))
                result.append(data[offset:offset+size])
                offset += size
            return result

        manifest = json.loads((ROOT/'firmware-corpus/manifest.json').read_text())
        for case in manifest['cases']:
            if case['root_tables'] not in ('acpidump', 'freebsd-physical'):
                continue
            with self.subTest(case=case['id']):
                directory = ROOT/'firmware-corpus'/case['id']
                info = corpus.multiboot2_information(corpus.read_memmap(directory/'memmap.tsv'))
                base = roots.from_capture(directory, info)
                before = base.digest()
                address, original = next((a,b) for a,b in base.tables if b[:4] == b'APIC')
                original_records = records(original)
                first_cpu = next(r for r in original_records if r[0] == 0)
                variants = roots.mutations(base)
                for name in ('root-duplicate-cpu', 'root-missing-cpus'):
                    reason, code = (('duplicateApicId', 4) if name == 'root-duplicate-cpu'
                                    else ('noEnabledProcessor', 6))
                    pinned = case['root_mutations'][name]
                    self.assertEqual(pinned['result'], 'admission-rejected:' + reason)
                    self.assertEqual(pinned['words'], [1, 3, code, 0, 0])
                    mutated = variants[name]
                    data = dict(mutated.tables)[address]
                    self.assertEqual(sum(data) % 256, 0)
                    self.assertEqual(struct.unpack_from('<I', data, 4)[0], len(data))
                    self.assertEqual(mutated.info, base.info)
                    self.assertEqual(mutated.root, base.root)
                    self.assertEqual([(a,b) for a,b in mutated.tables if a != address],
                                     [(a,b) for a,b in base.tables if a != address])
                    expected = (original_records + [first_cpu] if name == 'root-duplicate-cpu'
                                else [r for r in original_records if r[0] != 0])
                    self.assertEqual(records(data), expected)
                self.assertEqual(base.digest(), before)

    def test_root_sdt_reason_is_not_collapsed_to_generic_code(self):
        self.assertEqual(roots.rejection_name([1,2,25,5,0]),
                         'decoder-rejected:madtSelection.root.invalidChecksum')
        self.assertNotEqual(roots.rejection_name([1,2,25,3,0]),
                            roots.rejection_name([1,2,25,5,0]))
        with self.assertRaises(ValueError):roots.rejection_name([1,2,25,99,0])

    def test_memory_variants_preserve_all_rows(self):
        import struct
        variants=corpus.handoff_variants(self.info)
        entry_bytes=self.info[24:-8]
        reversed_entries=b''.join(reversed([entry_bytes[o:o+24] for o in range(0,len(entry_bytes),24)]))
        self.assertEqual(variants['handoff-order-reversed'][24:-8],reversed_entries)
        overlap=variants['handoff-overlapping-entry']
        self.assertEqual(len(overlap),len(self.info))
        first_base,first_length=struct.unpack_from('<QQ',overlap,24)
        second_base=struct.unpack_from('<Q',overlap,48)[0]
        self.assertTrue(first_base <= second_base < first_base+first_length)
        self.assertEqual(overlap[56:],self.info[56:])

    def test_unencodable_memory_range_rejected_before_packing(self):
        p=self.case/'memmap.tsv'
        for start,end in [('-0x1','0x1000'),('0x0','0xffffffffffffffff')]:
            p.write_text(f'index\tstart\tend\ttype\n0\t{start}\t{end}\tSystem RAM\n')
            with self.assertRaises(corpus.CorpusError):corpus.read_memmap(p)

    def test_symlink_diagnostic_names_the_case(self):
        p=next((self.case/'acpi/root-tables').glob('*.bin'))
        p.unlink();p.symlink_to(self.case/'acpi/APIC.bin')
        result=self.run_manifest(self.manifest())
        self.assertNotEqual(result.returncode,0)
        self.assertIn('case capture: unsupported physical table file',result.stderr)

    def test_memory_source_order_and_count_drift_rejected(self):
        path=self.case/'memmap.tsv';original=path.read_text().splitlines()
        provenance_path=self.case/'provenance.json'
        original_provenance=provenance_path.read_text()
        for rows in [list(reversed(original[1:])),original[1:-1]]:
            with self.subTest(rows=len(rows)):
                renumbered=[str(i)+'\t'+line.split('\t',1)[1] for i,line in enumerate(rows)]
                path.write_text(original[0]+'\n'+'\n'.join(renumbered)+'\n')
                digest=hashlib.sha256(path.read_bytes()).hexdigest()
                provenance=json.loads(original_provenance);provenance['files']['memmap.tsv']=digest
                provenance_path.write_text(json.dumps(provenance))
                manifest=self.manifest();case=manifest['cases'][0]
                case['inputs']['memmap.tsv']=digest
                case['inputs']['provenance.json']=hashlib.sha256(provenance_path.read_bytes()).hexdigest()
                result=self.run_manifest(manifest,'normalize')
                self.assertNotEqual(result.returncode,0)
                self.assertIn('case capture: normalized handoff bytes differ',result.stderr)

    def test_oversized_table_rejected(self):
        next((self.case/'acpi/root-tables').glob('*.bin')).write_bytes(bytes(65537))
        with self.assertRaises(ValueError):self.replay()

if __name__=='__main__':unittest.main()
