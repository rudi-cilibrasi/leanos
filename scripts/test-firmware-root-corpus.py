#!/usr/bin/env python3
"""Exercise normalization using the checked raw root captures."""
import importlib.util
import json
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

    def test_root_sdt_reason_is_not_collapsed_to_generic_code(self):
        self.assertEqual(roots.rejection_name([1,2,25,5,0]),
                         'decoder-rejected:madtSelection.root.invalidChecksum')
        self.assertNotEqual(roots.rejection_name([1,2,25,3,0]),
                            roots.rejection_name([1,2,25,5,0]))
        with self.assertRaises(ValueError):roots.rejection_name([1,2,25,99,0])

    def test_oversized_table_rejected(self):
        next((self.case/'acpi/root-tables').glob('*.bin')).write_bytes(bytes(65537))
        with self.assertRaises(ValueError):self.replay()

if __name__=='__main__':unittest.main()
