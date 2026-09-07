#!/usr/bin/env python3
"""Execute the image builder's real bootstrap control flow with fixture tools."""

from __future__ import annotations

import os
from pathlib import Path
import re
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
BUILD = (ROOT / "scripts/build-image.sh").read_text(encoding="utf-8")
INITIALIZATION = BUILD[BUILD.index('build_profile_started_at='):BUILD.index('require_tool() {')]
BOOTSTRAP = BUILD[
    BUILD.index('current_lean_c_signature="$(compute_lean_c_signature'):
    BUILD.index('lean_prefix="$(lake env lean --print-prefix)"')
]
MODULES = re.search(r"lean_c_modules=\(\s*(.*?)\n\)", BOOTSTRAP, re.S).group(1).split()
PREFIX = ["setup-and-signatures", "oracle-generation", "boot-plan-stubs",
          "lake-build", "lean-c-cache-check"]


class BootstrapTimingTests(unittest.TestCase):
    def setUp(self) -> None:
        self.directory = tempfile.TemporaryDirectory(prefix="leanos-bootstrap-timing-")
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        (self.root / "scripts").mkdir()
        (self.root / "build").mkdir()
        for name, body in (
            ("generate-oracle.sh", '[[ "$FAIL_AT" != oracle ]] || exit 86\nprintf oracle > "$1/corpus.tsv"\n'),
            ("generate-boot-page-plan.sh", 'printf stub > "$2"\n'),
        ):
            path = self.root / "scripts" / name
            path.write_text("#!/usr/bin/env bash\nset -euo pipefail\n" + body)
            path.chmod(0o755)
        self.shell = '''set -euo pipefail
repo_root="$PWD"
build="$PWD/build"
page_plan_stubs=(boot-plan.h)
compute_lean_c_signature() { printf fixture-signature; }
lake() {
  if [[ "$1" == build ]]; then
    [[ "$FAIL_AT" != lake ]] || return 86
    SECONDS=$((SECONDS + 2))
  else
    [[ "$1 $2" == 'env lean' && "$3" == --c=* ]]
    [[ "$FAIL_AT" != "${4##*/}" ]] || return 86
    printf 'generated from %s\\n' "$4" > "${3#--c=}"
    SECONDS=$((SECONDS + 1))
  fi
}
''' + INITIALIZATION + BOOTSTRAP
        self.timing = self.root / "timing dir/phases-bootstrap.tsv"

    def run_bootstrap(self, failure: str = "", timed: bool = True) -> subprocess.CompletedProcess:
        env = {**os.environ, "FAIL_AT": failure}
        env.pop("LEANOS_BUILD_TIMING_FILE", None)
        if timed:
            env["LEANOS_BUILD_TIMING_FILE"] = str(self.root / "timing dir/phases.tsv")
        return subprocess.run(["bash", "-c", self.shell], cwd=self.root, env=env,
                              text=True, capture_output=True)

    def rows(self) -> list[list[str]]:
        lines = self.timing.read_text().splitlines()
        self.assertEqual(lines[0], "phase\tphase_seconds\ttotal_seconds\tmode")
        rows = [line.split("\t") for line in lines[1:]]
        previous = 0
        for phase, duration, total, mode in rows:
            self.assertGreaterEqual(int(duration), 0)
            self.assertEqual(int(total), previous + int(duration), phase)
            self.assertIn(mode, ("measured", "generated", "reused"))
            previous = int(total)
        return rows

    def assert_complete(self, mode: str) -> None:
        rows = self.rows()
        self.assertEqual([row[0] for row in rows],
                         PREFIX + [f"lean-c-{module}" for module in MODULES] + ["complete"])
        self.assertEqual([row[3] for row in rows[len(PREFIX):-1]], [mode] * len(MODULES))
        # The original six-phase file remains independent and unchanged.
        coarse = (self.root / "timing dir/phases.tsv").read_text().splitlines()
        self.assertEqual(coarse[0], "phase\tphase_seconds\ttotal_seconds")
        self.assertEqual(coarse[1].split("\t")[0], "bootstrap-and-lean-generation")
        self.assertGreaterEqual(int(coarse[1].split("\t")[2]), int(rows[-1][2]))

    def test_generated_reused_and_invalidated_inputs(self) -> None:
        result = self.run_bootstrap()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assert_complete("generated")
        artifacts = {path.name: path.read_bytes() for path in (self.root / "build").iterdir()}
        result = self.run_bootstrap()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assert_complete("reused")
        self.assertEqual(artifacts, {path.name: path.read_bytes()
                                    for path in (self.root / "build").iterdir()})
        for invalidation in ("missing-module", "changed-signature"):
            with self.subTest(invalidation=invalidation):
                if invalidation == "missing-module":
                    (self.root / "build" / f"{MODULES[-1]}.c").unlink()
                else:
                    (self.root / "build/generated-lean-c.sha256").write_text("old\n")
                result = self.run_bootstrap()
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assert_complete("generated")

    def test_failures_propagate_without_claiming_completion(self) -> None:
        for failure, last in (("oracle", "setup-and-signatures"),
                              ("lake", "boot-plan-stubs"),
                              (f"{MODULES[1]}.lean", f"lean-c-{MODULES[0]}")):
            with self.subTest(failure=failure):
                result = self.run_bootstrap(failure)
                self.assertEqual(result.returncode, 86, result.stderr)
                self.assertEqual(self.rows()[-1][0], last)
                self.assertNotIn("complete", [row[0] for row in self.rows()])
                self.assertFalse((self.root / "build/generated-lean-c.sha256").exists())
                self.assertFalse(list((self.root / "build").glob(".lean-c.*")))

    def test_without_timing_file(self) -> None:
        result = self.run_bootstrap(timed=False)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertFalse(self.timing.parent.exists())
        self.assertIn("build-bootstrap\tcomplete\t", result.stdout)


if __name__ == "__main__":
    unittest.main()
