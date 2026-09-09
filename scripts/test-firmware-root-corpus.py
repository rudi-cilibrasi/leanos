#!/usr/bin/env python3
"""Exercise normalization using the checked raw root captures."""
import importlib.util
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

    def test_oversized_table_rejected(self):
        next((self.case/'acpi/root-tables').glob('*.bin')).write_bytes(bytes(65537))
        with self.assertRaises(ValueError):self.replay()

if __name__=='__main__':unittest.main()
