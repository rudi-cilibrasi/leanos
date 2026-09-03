#!/usr/bin/env python3
"""Controlled drift fixture for generated toolchain workflow consumers."""

from pathlib import Path
import shutil
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]

with tempfile.TemporaryDirectory() as directory:
    fixture = Path(directory)
    (fixture / "scripts").mkdir()
    (fixture / ".github/workflows").mkdir(parents=True)
    shutil.copy2(ROOT / "scripts/toolchain-profiles.json", fixture / "scripts")
    shutil.copy2(ROOT / "scripts/workflow_yaml.py", fixture / "scripts")
    for name in ("ci.yml", "release.yml"):
        shutil.copy2(ROOT / ".github/workflows" / name, fixture / ".github/workflows")
    ci = fixture / ".github/workflows/ci.yml"
    ci.write_text(ci.read_text().replace("sha256:6d483272", "sha256:aaaaaaaa", 1))
    command = [str(ROOT / "scripts/render-toolchain-consumers.py"), "--root", str(fixture)]
    failed = subprocess.run(command + ["--check"], text=True, capture_output=True)
    assert failed.returncode == 1
    assert "stale generated toolchain consumers" in failed.stderr
    subprocess.run(command, check=True)
    subprocess.run(command + ["--check"], check=True)
    ci.write_text(ci.read_text().replace("container:", "# container:", 1))
    missing = subprocess.run(command + ["--check"], text=True, capture_output=True)
    assert missing.returncode == 1
    assert "canonical container job set drifted" in missing.stderr

    shutil.copy2(ROOT / ".github/workflows/ci.yml", ci)
    source = ci.read_text()
    ci.write_text(source.replace("container: ghcr.io/", "container: ubuntu@", 1))
    wrong_image = subprocess.run(command + ["--check"], text=True, capture_output=True)
    assert wrong_image.returncode == 1
    assert "has a stale canonical image" in wrong_image.stderr

    shutil.copy2(ROOT / ".github/workflows/ci.yml", ci)
    ci.write_text(
        ci.read_text().replace(
            "    container: ghcr.io/",
            "    container:\n      image: ghcr.io/",
            1,
        )
    )
    mapping_container = subprocess.run(
        command + ["--check"], text=True, capture_output=True
    )
    assert mapping_container.returncode == 1
    assert "must use scalar container syntax" in mapping_container.stderr

print("Toolchain consumer render fixtures passed")
