#!/usr/bin/env python3
"""Execute the Pages image handoff with fixture bytes and no VERSION file."""

import os
from pathlib import Path
import shutil
import subprocess
import tempfile

from workflow_yaml import load_workflow


ROOT = Path(__file__).resolve().parents[1]
workflow = load_workflow(ROOT / ".github/workflows/pages.yml")


def command(job, name):
    return next(step["run"] for step in workflow["jobs"][job]["steps"]
                if step.get("name") == name)


def run(arguments, cwd, env):
    return subprocess.run(arguments, cwd=cwd, env=env, check=True,
                          text=True, capture_output=True).stdout.strip()


with tempfile.TemporaryDirectory(prefix="leanos-pages-pipeline-") as directory:
    root = Path(directory)
    for version in (None, "9.8.7"):
        source = root / (version or "default")
        scripts = source / "scripts"
        scripts.mkdir(parents=True)
        env = dict(os.environ)
        env.pop("LEANOS_VERSION", None)
        if version is not None:
            env["LEANOS_VERSION"] = version
        run(["git", "init", "-q"], source, env)
        run(["git", "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
             "-c", "commit.gpgsign=false", "commit", "--allow-empty", "-qm", "fixture"],
            source, env)
        revision = run(["git", "rev-parse", "HEAD"], source, env)
        shutil.copy2(ROOT / "scripts/image-bundle.sh", scripts)
        # Only compilation is stubbed; execute the actual workflow handoff and
        # real archive/revision/digest verification in two separate directories.
        build = scripts / "build-image.sh"
        build.write_text("""#!/bin/sh
set -eu
mkdir -p build/boot
printf 'fixture image\\n' > "build/boot/leanos-${LEANOS_VERSION:-0.1.0}-x86_64.iso"
for artifact in corpus.tsv serial-protocol.sh serial-protocol.tsv TOOLCHAIN_PROFILE.json; do
  printf '%s\\n' "$artifact" > "build/boot/$artifact"
done
git rev-parse HEAD > build/boot/SOURCE_REVISION
""")
        build.chmod(0o755)
        assert not (source / "VERSION").exists()
        run(["sh", "-e", "-c", command("build-image", "Build and bundle the canonical image")],
            source, env)

        consumer = source / "consumer"
        (consumer / "scripts").mkdir(parents=True)
        shutil.copy2(scripts / "image-bundle.sh", consumer / "scripts")
        download = consumer / "build/ci/pages-image"
        download.mkdir(parents=True)
        for suffix in ("", ".sha256"):
            shutil.copy2(source / f"build/ci/leanos-pages-image.tar.gz{suffix}", download)
        verify = command("build", "Verify revision-bound canonical image")
        verify = verify.replace("${{ github.sha }}", revision)
        run(["sh", "-e", "-c", verify], consumer, env)
        expected = {
            f"leanos-{version or '0.1.0'}-x86_64.iso", "corpus.tsv",
            "serial-protocol.sh", "serial-protocol.tsv", "SOURCE_REVISION",
            "TOOLCHAIN_PROFILE.json",
        }
        actual = consumer / "build/boot"
        assert {path.name for path in actual.iterdir()} == expected
        for name in expected:
            assert (actual / name).read_bytes() == (source / "build/boot" / name).read_bytes()

        # A successful archive verification alone must not admit a differently
        # named ISO than the version the browser job is about to consume.
        wrong_env = {**env, "LEANOS_VERSION": "8.7.6"}
        result = subprocess.run(["sh", "-e", "-c", verify], cwd=consumer,
                                env=wrong_env, text=True, capture_output=True)
        assert result.returncode != 0, "Pages accepted the wrong image version"

assert workflow["jobs"]["deploy"]["if"] == "github.ref == 'refs/heads/main'"
print("Pages image handoff passed without VERSION, with default and overridden versions")
