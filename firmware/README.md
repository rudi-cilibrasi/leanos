# Real firmware decoder corpus (#292, in progress)

The first source is an owner-controlled Intel NUC10i7FNH with Intel FNCML357.0053
firmware. `memory-corpus.json` binds the exact capture inventory, deterministic
conversion, synthetic wrapper inputs, and all 68 expected handoff projection
words. The initial Lean evaluation and ordinary/sanitized generated-C replay
agreed: 18 entries, three normalized regions. This is decoder evidence, not a
claim that LeanOS booted or admitted the source machine.

The [Linux sysfs firmware-map ABI](https://github.com/torvalds/linux/blob/master/Documentation/ABI/testing/sysfs-firmware-memmap)
defines numeric directories in firmware order, hexadecimal start addresses,
inclusive end addresses and named memory types. The converter preserves that
order, translates each inclusive range to base/length, and builds a single
Multiboot2 mmap tag with 24-byte entries, version zero, reserved fields zero,
and an end tag. It never sorts by address, merges entries, drops unsupported
types or repairs inputs. Unknown types fail as unsupported captures. The
magic and input address in the manifest belong to the replay wrapper; they
are not recorded bootloader observations.

To regenerate the input from a clean checkout (Python standard library only):

```sh
python3 - <<'PY'
import importlib.util, json
from pathlib import Path
spec = importlib.util.spec_from_file_location('converter', 'scripts/convert-firmware-memory-map.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
row = json.loads(Path('firmware/memory-corpus.json').read_text())['cases'][0]
data = module.convert(Path('firmware') / row['capture'], row['inventory_sha256'])
import hashlib
assert hashlib.sha256(data).hexdigest() == row['converted_sha256']
print(len(data), 'verified bytes')
PY
python3 scripts/test-firmware-memory-map-converter.py
```

The capture keeps the exact sysfs start/end/type bytes and the 244-byte raw MADT.
Its declared MADT length and checksum agree. No serial number, UUID, MAC address,
DSDT or unrelated ACPI table was collected. Only the local host nickname was
removed from descriptive metadata; decoder input bytes were not redacted.
Linux denied `/dev/mem` access to the ACPI root pointer. Root tables and executing
BSP identity are unavailable: no substitute roots or BSP values were invented.

This branch is incomplete: repository-owned live capture, clean-checkout Lean
and generated-C replay integration, MADT replay, further corpus mutations, and
at least three distinct source machines are still required. The observed
projection is retained for those tests; hashes alone do not establish decoder
agreement. Firmware, Linux exposure, the collecting operator and toolchain
remain trusted, and Linux's view is not a claim about GRUB handoff timing.
