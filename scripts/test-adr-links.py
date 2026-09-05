#!/usr/bin/env python3
"""Controlled fixtures for the ADR numbering and link gate."""

from __future__ import annotations

from pathlib import Path
import subprocess
import tempfile
import unittest


SCRIPT = Path(__file__).with_name("check-adr-links.py")


class AdrLinkCheckTest(unittest.TestCase):
    def run_check(self, files: dict[str, str]) -> subprocess.CompletedProcess[str]:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for relative, content in files.items():
                path = root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(content, encoding="utf-8")
            return subprocess.run(
                ["python3", str(SCRIPT), str(root)],
                check=False,
                capture_output=True,
                text=True,
            )

    def test_accepts_unique_numbers_and_resolving_links(self) -> None:
        result = self.run_check(
            {
                "docs/adr/0001-first.md": "# First\n",
                "docs/adr/0002-second.md": "[First](0001-first.md)\n",
            }
        )
        self.assertEqual(0, result.returncode, result.stderr)

    def test_rejects_duplicate_numbers(self) -> None:
        result = self.run_check(
            {
                "docs/adr/0001-first.md": "# First\n",
                "docs/adr/0001-second.md": "# Second\n",
            }
        )
        self.assertNotEqual(0, result.returncode)
        self.assertIn("duplicate ADR number 0001", result.stderr)

    def test_rejects_malformed_names(self) -> None:
        result = self.run_check({"docs/adr/1-short.md": "# Short\n"})
        self.assertNotEqual(0, result.returncode)
        self.assertIn("malformed ADR filename", result.stderr)

    def test_rejects_broken_local_adr_links(self) -> None:
        result = self.run_check(
            {"docs/adr/0001-first.md": "[Missing](0002-missing.md)\n"}
        )
        self.assertNotEqual(0, result.returncode)
        self.assertIn("broken ADR link", result.stderr)


if __name__ == "__main__":
    unittest.main()
