#!/usr/bin/env python3
"""Exercise manifest-driven runner discovery with fake QEMU, not guest evidence."""

import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent


def main():
    with tempfile.TemporaryDirectory(prefix="leanos-assigned-manifest-") as directory:
        root = Path(directory)
        scripts = root / "scripts"
        boot = root / "build/boot"
        scripts.mkdir()
        boot.mkdir(parents=True)
        for name in ("run-assigned-edu-negatives.sh", "scenario-manifest.py", "q35-platform.sh"):
            shutil.copy2(ROOT / "scripts" / name, scripts / name)
        manifest = json.loads((ROOT / "scripts/scenario-manifest.json").read_text())
        variants = manifest["scenarios"]["assigned-edu-inventory"]["negative_variants"]
        variants.append({"fixture": "new-fixture", "macro": "LEANOS_NEW_FIXTURE", "reason": "new-reason"})
        manifest_path = scripts / "scenario-manifest.json"
        manifest_path.write_text(json.dumps(manifest))
        oracle = root / "oracle"
        subprocess.run([str(ROOT / "scripts/generate-oracle.sh"), str(oracle)],
                       cwd=ROOT, check=True, stdout=subprocess.DEVNULL)
        shutil.copy2(oracle / "serial-protocol.sh", boot / "serial-protocol.sh")
        final_record = subprocess.check_output(
            ["bash", "-c", 'source "$1"; printf "%s" "$LEANOS_SERIAL_3_FINAL"',
             "protocol", str(boot / "serial-protocol.sh")], text=True,
        )
        for row in variants:
            (boot / f"leanos-0.1.0-x86_64-assigned-edu-{row['fixture']}.iso").touch()
        fake = root / "fake-qemu"
        reasons = {row["fixture"]: row["reason"] for row in variants}
        fake.write_text("""#!/usr/bin/env python3
import sys
from pathlib import Path
args = sys.argv[1:]
reasons = """ + repr(reasons) + """
final_record = """ + repr(final_record) + """
log = args[args.index('-serial') + 1].removeprefix('file:')
fixture = next(k for k in reasons if any('assigned-edu-' + k + '.iso' in a for a in args))
Path(log).write_text(final_record + ' status=FAIL reason=' + reasons[fixture] + '\\n')
with open('invocations', 'a') as output:
    output.write(fixture + '\\n')
sys.exit(35)
""")
        fake.chmod(0o755)
        env = dict(os.environ, LEANOS_QEMU=str(fake), LEANOS_VERSION="0.1.0",
                   LEANOS_QEMU_ACCELERATOR="tcg", LEANOS_QEMU_MEMORY_MIB="128",
                   LEANOS_SERIAL_PROTOCOL=str(boot / "serial-protocol.sh"))
        calls = root / "invocations"

        def run():
            return subprocess.run(
                ["bash", "scripts/run-assigned-edu-negatives.sh"], cwd=root,
                env=env, capture_output=True, text=True,
            )

        result = run()
        if result.returncode or calls.read_text().splitlines() != [r["fixture"] for r in variants]:
            raise AssertionError(f"manifest-only fixture was not executed in order: {result}")
        calls.unlink()
        variants[0]["reason"] = "bad\tfield"
        manifest_path.write_text(json.dumps(manifest))
        result = run()
        if result.returncode == 0 or "invalid negative variant fields" not in result.stderr or calls.exists():
            raise AssertionError(f"malformed manifest reached a guest: {result}")
        variants[0]["reason"] = reasons[variants[0]["fixture"]]
        manifest_path.write_text(json.dumps(manifest))
        (boot / f"leanos-0.1.0-x86_64-assigned-edu-{variants[0]['fixture']}.iso").unlink()
        result = run()
        if result.returncode == 0 or "not found" not in result.stderr or calls.exists():
            raise AssertionError(f"missing declared image was accepted: {result}")
    print("Assigned-EDU manifest runner fixtures passed (fake QEMU)")


if __name__ == "__main__":
    main()
