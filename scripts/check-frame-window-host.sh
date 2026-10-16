#!/usr/bin/env bash
# The frame copy window's generated boundary (issue #569).
#
# `leanos_frame_window_operand` is LeanOS.FrameCopyWindow.frameWindowOperand,
# the operand the frame-window kernel (and the Qotom production profile)
# calls on every frame copy: the alias address of the caller's buffer in its
# window root, or 0.  The hosted generated-boundary row `frame-window`
# (tests/frame-window-host.c) checks it on fixed requests for every refusal
# reason and every geometry rule, and differentially against a C
# restatement of the documented semantics and against the frame port
# witness leanos_frame_port_check on 200000 requests near the boundaries.
#
# usage: check-frame-window-host.sh [ordinary|sanitized]
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
mode="${1:-ordinary}"
case "$mode" in
  ordinary|sanitized) ;;
  *)
    echo "usage: $0 [ordinary|sanitized]" >&2
    exit 2
    ;;
esac
LEANOS_HOSTED_BOUNDARY_ID=frame-window ./scripts/check-boot-handoff-host.sh "$mode"
