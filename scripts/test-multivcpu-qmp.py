#!/usr/bin/env python3
import importlib.util
from pathlib import Path
import unittest


PATH = Path(__file__).with_name("check-multivcpu-qmp.py")
SPEC = importlib.util.spec_from_file_location("check_multivcpu_qmp", PATH)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


def transcript(cpus):
    return [
        {"direction": "qemu-to-host", "message": {"QMP": {"version": {}}}},
        {"direction": "host-to-qemu", "message": {"execute": "qmp_capabilities"}},
        {"direction": "qemu-to-host", "message": {"return": {}}},
        {"direction": "host-to-qemu", "message": {"execute": "query-cpus-fast"}},
        {"direction": "qemu-to-host", "message": {"return": cpus}},
    ]


def cpu(index, core):
    return {
        "cpu-index": index,
        "qom-path": f"/machine/unattached/device[{index}]",
        "props": {"socket-id": 0, "core-id": core, "thread-id": 0},
    }


class QmpInventoryTest(unittest.TestCase):
    def test_accepts_exact_two_core_shape_and_normalizes_order(self):
        result = MODULE.normalize(transcript([cpu(1, 1), cpu(0, 0)]))
        self.assertEqual([0, 1], [item["cpu-index"] for item in result])

    def test_rejects_singleton_and_extra_processors(self):
        for cpus in ([cpu(0, 0)], [cpu(0, 0), cpu(1, 1), cpu(2, 2)]):
            with self.assertRaisesRegex(MODULE.InventoryError, "exactly two"):
                MODULE.normalize(transcript(cpus))

    def test_rejects_implicit_or_drifted_topology(self):
        for cpus in (
            [cpu(0, 0), cpu(1, 0)],
            [cpu(0, 0), {**cpu(1, 1), "props": {"socket-id": 1, "core-id": 0, "thread-id": 0}}],
        ):
            with self.assertRaisesRegex(MODULE.InventoryError, "drifted"):
                MODULE.normalize(transcript(cpus))

    def test_rejects_missing_inventory_query(self):
        with self.assertRaisesRegex(MODULE.InventoryError, "record count"):
            MODULE.normalize(transcript([cpu(0, 0), cpu(1, 1)])[:-2])

    def test_rejects_extra_qmp_record(self):
        records = transcript([cpu(0, 0), cpu(1, 1)])
        records.insert(1, {"direction": "qemu-to-host", "message": {"event": "STOP"}})
        with self.assertRaisesRegex(MODULE.InventoryError, "record count"):
            MODULE.normalize(records)

    def test_rejects_reordered_qmp_exchange(self):
        records = transcript([cpu(0, 0), cpu(1, 1)])
        records[1], records[3] = records[3], records[1]
        with self.assertRaisesRegex(MODULE.InventoryError, "record sequence"):
            MODULE.normalize(records)


if __name__ == "__main__":
    unittest.main()
