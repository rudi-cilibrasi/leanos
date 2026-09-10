#!/usr/bin/env python3
"""Boundary checks for the conservative FreeBSD EFI corpus conversion."""
import importlib.util
from pathlib import Path
import struct
import unittest

spec = importlib.util.spec_from_file_location('projection', Path(__file__).with_name('project-freebsd-efi-map.py'))
projection = importlib.util.module_from_spec(spec)
spec.loader.exec_module(projection)


def capture(entries, stride=48):
    descriptors = b''.join(struct.pack('<I4xQQQQ', kind, base, 0, pages, attributes)
                           + bytes(stride-40) for kind, base, pages, attributes in entries)
    return struct.pack('<QQI', len(descriptors), stride, 1) + bytes(12) + descriptors


class ProjectionTests(unittest.TestCase):
    def test_only_conventional_memory_is_usable(self):
        rows = projection.project(capture([(kind, 0x1000*kind, 1, 0) for kind in range(15)]))
        self.assertEqual([kind for _, _, kind in rows], [2,2,2,2,2,2,2,1,5,3,4,2,2,2,2])

    def test_runtime_attribute_overrides_type(self):
        rows = projection.project(capture([(kind, 0x1000*kind, 1, 1 << 63) for kind in (7,8,9,10)]))
        self.assertEqual([kind for _, _, kind in rows], [2]*4)

    def test_preserves_order_overlap_and_inclusive_end(self):
        raw = capture([(7, 0x3000, 2, 0), (10, 0x1000, 3, 0)])
        self.assertEqual(projection.render(projection.project(raw)),
                         'index\tstart\tend\ttype\n0\t0x3000\t0x4fff\tSystem RAM\n'
                         '1\t0x1000\t0x3fff\tACPI Non-volatile Storage\n')

    def test_truncations_and_trailing_bytes_reject(self):
        raw = capture([(7, 0x1000, 1, 0)])
        for end in range(len(raw)):
            with self.subTest(end=end), self.assertRaises(ValueError):
                projection.project(raw[:end])
        with self.assertRaises(ValueError): projection.project(raw+b'\0')

    def test_bad_header_and_empty_vector_reject(self):
        raw = capture([(7, 0x1000, 1, 0)])
        for offset,fmt,value in [(0,'Q',0),(0,'Q',49),(8,'Q',0),(8,'Q',39),(8,'Q',257),(16,'I',2)]:
            bad=bytearray(raw);struct.pack_into('<'+fmt,bad,offset,value)
            with self.subTest(offset=offset,value=value), self.assertRaises(ValueError):
                projection.project(bad)
        with self.assertRaises(ValueError): projection.project(capture([]))
        with self.assertRaises(ValueError): projection.project(bytes(65569))

    def test_invalid_ranges_and_types_reject(self):
        for entry in [(15,0x1000,1,0),(7,0x1001,1,0),(7,0x1000,0,0),(7,0xfffffffffffff000,2,0)]:
            with self.subTest(entry=entry), self.assertRaises(ValueError):
                projection.project(capture([entry]))
        self.assertEqual(projection.project(capture([(7,0xfffffffffffff000,1,0)])),
                         [(0xfffffffffffff000,4096,1)])

    def test_padding_and_descriptor_extensions_do_not_change_projection(self):
        raw=bytearray(capture([(7,0x1000,1,0)]))
        expected=projection.project(raw)
        raw[20:32]=b'P'*12;raw[36:40]=b'P'*4;raw[72:80]=b'P'*8
        self.assertEqual(projection.project(raw),expected)


if __name__ == '__main__': unittest.main()
