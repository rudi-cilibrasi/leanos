#!/usr/bin/env python3
"""Controlled drift fixture for generated toolchain workflow consumers."""

from pathlib import Path
import shutil
import json
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]

with tempfile.TemporaryDirectory() as directory:
    fixture = Path(directory)
    (fixture / "scripts").mkdir()
    (fixture / "docs").mkdir()
    (fixture / ".github/workflows").mkdir(parents=True)
    shutil.copy2(ROOT / "scripts/toolchain-profiles.json", fixture / "scripts")
    shutil.copy2(ROOT / "scripts/workflow_yaml.py", fixture / "scripts")
    shutil.copy2(ROOT / "Containerfile.ci", fixture)
    shutil.copy2(ROOT / "docs/boot-image.md", fixture / "docs")
    for name in ("ci.yml", "release.yml", "pages.yml"):
        shutil.copy2(ROOT / ".github/workflows" / name, fixture / ".github/workflows")
    ci = fixture / ".github/workflows/ci.yml"
    digest = next(
        profile["reference_environment"]["ci_image_digest"]
        for profile in json.loads((ROOT / "scripts/toolchain-profiles.json").read_text())["profiles"]
        if profile["status"] == "canonical"
    )
    ci.write_text(ci.read_text().replace(digest, "sha256:" + "a" * 64, 1))
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

    shutil.copy2(ROOT / ".github/workflows/ci.yml", ci)
    containerfile = fixture / "Containerfile.ci"
    containerfile.write_text(
        containerfile.read_text().replace(
            "binutils=2.42-4ubuntu2.10", "binutils=2.42-4ubuntu2.9", 1
        )
    )
    stale_package = subprocess.run(
        command + ["--check"], text=True, capture_output=True
    )
    assert stale_package.returncode == 1
    assert "apt package inventory differs" in stale_package.stderr

    shutil.copy2(ROOT / "Containerfile.ci", containerfile)
    containerfile.write_text(
        containerfile.read_text() + "\nRUN apt-get install -y curl\n"
    )
    extra_install = subprocess.run(
        command + ["--check"], text=True, capture_output=True
    )
    assert extra_install.returncode == 1
    assert "expected exactly one apt install site, found 2" in extra_install.stderr

    shutil.copy2(ROOT / "Containerfile.ci", containerfile)
    containerfile.write_text(containerfile.read_text() + "\nRUN apt install -y curl\n")
    extra_apt_install = subprocess.run(
        command + ["--check"], text=True, capture_output=True
    )
    assert extra_apt_install.returncode == 1
    assert "expected exactly one apt install site, found 2" in extra_apt_install.stderr

    shutil.copy2(ROOT / "Containerfile.ci", containerfile)
    containerfile.write_text(
        containerfile.read_text() + "\nRUN apt-get -y install curl\n"
    )
    option_before_install = subprocess.run(
        command + ["--check"], text=True, capture_output=True
    )
    assert option_before_install.returncode == 1
    assert "expected exactly one apt install site, found 2" in option_before_install.stderr

    shutil.copy2(ROOT / "Containerfile.ci", containerfile)
    containerfile.write_text(
        containerfile.read_text() + "\nRUN :; apt-get install -y curl\n"
    )
    semicolon_install = subprocess.run(
        command + ["--check"], text=True, capture_output=True
    )
    assert semicolon_install.returncode == 1
    assert "expected exactly one apt install site, found 2" in semicolon_install.stderr

    shutil.copy2(ROOT / "Containerfile.ci", containerfile)
    documentation = fixture / "docs/boot-image.md"
    documentation.write_text(
        documentation.read_text().replace(
            "`binutils` | `2.42-4ubuntu2.10`",
            "`binutils` | `0`",
            1,
        )
    )
    stale_documentation = subprocess.run(
        command + ["--check"], text=True, capture_output=True
    )
    assert stale_documentation.returncode == 1
    assert "docs/boot-image.md" in stale_documentation.stderr

    shutil.copy2(ROOT / "docs/boot-image.md", documentation)
    pages = fixture / ".github/workflows/pages.yml"
    pages.write_text(
        pages.read_text().replace(
            "      - name: Set up Node\n",
            "      - name: Install mutable image tools\n"
            "        run: sudo apt-get install -y gcc\n\n"
            "      - name: Set up Node\n",
            1,
        )
    )
    mutable_pages = subprocess.run(
        command + ["--check"], text=True, capture_output=True
    )
    assert mutable_pages.returncode == 1
    assert "mutable apt command" in mutable_pages.stderr

    shutil.copy2(ROOT / ".github/workflows/pages.yml", pages)
    pages.write_text(pages.read_text().replace("    needs: build-image\n", "", 1))
    detached_browser = subprocess.run(
        command + ["--check"], text=True, capture_output=True
    )
    assert detached_browser.returncode == 1
    assert "browser build must require" in detached_browser.stderr

    shutil.copy2(ROOT / ".github/workflows/pages.yml", pages)
    pages.write_text(
        pages.read_text().replace(
            '            "${{ github.sha }}"\n',
            '            "0000000000000000000000000000000000000000"\n',
            1,
        )
    )
    unbound_bundle = subprocess.run(
        command + ["--check"], text=True, capture_output=True
    )
    assert unbound_bundle.returncode == 1
    assert "revision-bound image verification is missing" in unbound_bundle.stderr

    shutil.copy2(ROOT / ".github/workflows/pages.yml", pages)
    pages.write_text(pages.read_text().replace("            corpus.tsv \\\n", "", 1))
    incomplete_bundle = subprocess.run(
        command + ["--check"], text=True, capture_output=True
    )
    assert incomplete_bundle.returncode == 1
    assert "browser image bundle omits corpus.tsv" in incomplete_bundle.stderr

    shutil.copy2(ROOT / ".github/workflows/pages.yml", pages)
    pages.write_text(
        pages.read_text().replace(
            "            build/ci/leanos-pages-image.tar.gz.sha256\n",
            "            build/ci/wrong-image.tar.gz.sha256\n",
            1,
        )
    )
    wrong_upload_path = subprocess.run(
        command + ["--check"], text=True, capture_output=True
    )
    assert wrong_upload_path.returncode == 1
    assert "artifact upload path drifted" in wrong_upload_path.stderr

    shutil.copy2(ROOT / ".github/workflows/pages.yml", pages)
    pages.write_text(
        pages.read_text().replace(
            "          path: build/ci/pages-image\n",
            "          path: build/ci/wrong-pages-image\n",
            1,
        )
    )
    wrong_download_path = subprocess.run(
        command + ["--check"], text=True, capture_output=True
    )
    assert wrong_download_path.returncode == 1
    assert "artifact download path drifted" in wrong_download_path.stderr

print("Toolchain consumer render fixtures passed")
