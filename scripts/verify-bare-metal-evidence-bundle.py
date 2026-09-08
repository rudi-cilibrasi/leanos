#!/usr/bin/env python3
"""Verify a deterministic bare-metal typed-rejection evidence bundle."""

import argparse
import importlib.util
import json
from pathlib import Path
import sys

CLASSIFIER = Path(__file__).with_name("check-bare-metal-rejection.py")
SPEC = importlib.util.spec_from_file_location("bare_metal_rejection", CLASSIFIER)
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("bundle", type=Path)
    args = parser.parse_args()
    try:
        result = MODULE.verify_evidence_bundle(args.bundle)
    except MODULE.ClassificationError as error:
        print(json.dumps({"schemaVersion": 1, "result": error.result,
                          "detail": error.detail}, sort_keys=True))
        return 1
    except (OSError, UnicodeError, ValueError, TypeError, json.JSONDecodeError):
        print(json.dumps({"schemaVersion": 1, "result": "capture-failure",
                          "detail": "bundle is unreadable or invalid"}, sort_keys=True))
        return 1
    print(json.dumps(result, sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
