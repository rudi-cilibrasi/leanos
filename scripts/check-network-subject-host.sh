#!/usr/bin/env bash
# The ring-3 network subject's generated boundary (issue #450).
#
# * `leanos_net_reply` is the C the Lean compiler generates for
#   LeanOS.Net.Echo.reply at the C hooks (LeanOS/Net/EchoC.lean); the network
#   subject (subjects/net) links it.
# * `leanos_frame_copy_check` is LeanOS.NetworkSubject.frameCopyCheck, the
#   witness the network-subject kernel calls on every frame copy.
#
# This gate checks what the shared definitions cannot:
#
# 1. Reference: tests/NetEchoVectors.lean requires the reference responder
#    LeanOS.Net.Echo.replyFrame to agree with replies built independently
#    from the frame constructors, and writes the differential vectors.
# 2. Hosted replay (the hosted generated-boundary row `network-subject`):
#    tests/net-echo-host.c checks the copy witness on fixed requests and,
#    over the same hooks as subjects/net/main.c, requires the generated
#    responder to return exactly the reference reply on every vector and to
#    touch no byte past the frame.
# The subject's own shape (no undefined symbol, no indirect branch, the
# slot's sizes) is checked by scripts/build-subject.sh when the image is
# built.
#
# usage: check-network-subject-host.sh [ordinary|sanitized]
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
lake build LeanOS.Net.EchoC leanos-net-echo-vectors >/dev/null
vectors=build/network-subject-vectors
mkdir -p "$vectors"
if [[ "$mode" == ordinary || ! -f "$vectors/vectors.txt" ]]; then
  .lake/build/bin/leanos-net-echo-vectors "$vectors/vectors.txt"
fi
LEANOS_NET_ECHO_VECTORS="$(cd "$vectors" && pwd)/vectors.txt" \
  LEANOS_HOSTED_BOUNDARY_ID=network-subject \
  ./scripts/check-boot-handoff-host.sh "$mode"
