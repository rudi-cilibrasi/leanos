#!/usr/bin/env python3
"""Fixtures for the repository-owned workflow YAML loader."""

from pathlib import Path
import tempfile

from workflow_yaml import WorkflowYamlError, load_workflow


def load(source: str):
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "workflow.yml"
        path.write_text(source, encoding="utf-8")
        return load_workflow(path)


first = load("""name: CI
on:
  merge_group:
    branches: [main]
jobs:
  evidence:
    timeout-minutes: 60
    strategy:
      matrix:
        shard: [0, 1, 2, 3]
    steps:
      - name: Run evidence
        run: |
          ./scripts/run-emulator-evidence.py run
          test -s build/boot/serial.log
""")
second = load("""jobs:
  evidence:
    steps:
      - run: >-
          ./scripts/run-emulator-evidence.py run
          test -s build/boot/serial.log
        name: 'Run evidence'
    strategy:
      matrix:
        shard: [0,1,2,3]
    timeout-minutes: 60
on:
  merge_group:
    branches:
      - main
name: "CI"
""")
for workflow in (first, second):
    assert "on" in workflow and True not in workflow
    assert workflow["on"]["merge_group"]["branches"] == ["main"]
    assert workflow["jobs"]["evidence"]["strategy"]["matrix"]["shard"] == [0, 1, 2, 3]
    assert workflow["jobs"]["evidence"]["timeout-minutes"] == 60

try:
    load("name: CI\nname: duplicate\n")
except WorkflowYamlError as error:
    assert "duplicate key" in str(error)
else:
    raise AssertionError("duplicate workflow key was accepted")

try:
    load("name: CI\njobs: &shared {}\n")
except WorkflowYamlError as error:
    assert "anchors" in str(error)
else:
    raise AssertionError("workflow anchor was accepted")

print("Workflow YAML structural fixtures passed")
