#!/usr/bin/env python3
"""Mutation controls for the restricted WRMSR-site audit; never executes fixtures."""
from pathlib import Path
import runpy
import subprocess
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[1]
A=runpy.run_path(str(ROOT/'scripts/audit-qotom-msr-writes.py'))


class Audit(unittest.TestCase):
    def fixture(self,directory,block,extra=b'\x90'):
        p=Path(directory)
        text='.section .text,"ax"\n.global normalize_fast_entry_msrs\nnormalize_fast_entry_msrs:\n'
        text+='.byte '+','.join(map(str,block))+'\n'
        text+='.global normalize_extended_state_cr0\nnormalize_extended_state_cr0:\nret\n'
        text+='.section .extra,"ax"\n.byte '+','.join(map(str,extra))+'\n'
        (p/'probe.S').write_text(text)
        subprocess.run(['as','--64',str(p/'probe.S'),'-o',str(p/'probe.o')],check=True)
        subprocess.run(['ld','-e','normalize_fast_entry_msrs',str(p/'probe.o'),'-o',str(p/'probe.elf')],check=True)
        return p/'probe.elf'

    def test_reviewed_block(self):
        with tempfile.TemporaryDirectory() as tmp:
            result=A['audit'](self.fixture(tmp,A['BLOCK']))
            self.assertEqual([r['selector_on_normal_entry'] for r in result['sites']],list(A['SELECTORS']))
            self.assertFalse(result['control_flow_integrity_established'])

    def test_selector_drift(self):
        with tempfile.TemporaryDirectory() as tmp:
            block=bytearray(A['BLOCK']);block[1:5]=(0x830).to_bytes(4,'little')
            with self.assertRaises(ValueError): A['audit'](self.fixture(tmp,block))

    def test_extra_write_encoding(self):
        with tempfile.TemporaryDirectory() as tmp:
            with self.assertRaises(ValueError): A['audit'](self.fixture(tmp,A['BLOCK'],b'\x90\x0f\x30'))

    def test_changed_instruction(self):
        with tempfile.TemporaryDirectory() as tmp:
            block=bytearray(A['BLOCK']);block[9]^=1
            with self.assertRaises(ValueError): A['audit'](self.fixture(tmp,block))

    def test_truncated_section_table(self):
        with tempfile.TemporaryDirectory() as tmp:
            p=self.fixture(tmp,A['BLOCK']);p.write_bytes(p.read_bytes()[:-1])
            with self.assertRaises(ValueError): A['audit'](p)


if __name__=='__main__': unittest.main()
