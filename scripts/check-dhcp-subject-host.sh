#!/usr/bin/env bash
# The ring-3 DHCP subject's generated boundary (issue #556).
#
# * `leanos_dhcp_step` is the C the Lean compiler generates for
#   LeanOS.Net.DhcpClient.step at the C hooks (LeanOS/Net/DhcpClientC.lean);
#   the DHCP subject (subjects/dhcp) links it.
# * `leanos_frame_port_check` is LeanOS.DhcpSubject.framePortCheck, the
#   witness the dhcp-subject kernel calls on every frame copy.
#
# This gate checks what the shared definitions cannot:
#
# 1. Reference: tests/NetDhcpVectors.lean requires the model reading of the
#    client to send exactly the frames of the reference LeanOS.Wifi.Dhcp on
#    the frame source's records and to agree with the reference client
#    Wifi.Dhcp.Client.handle on every OFFER, ACK and NAK variant (single-byte
#    corruptions of every byte, truncations), and writes the differential
#    vectors.
# 2. Hosted replay (the hosted generated-boundary row `dhcp-subject`):
#    tests/net-dhcp-host.c checks the port witness on fixed requests and,
#    over the same hooks as subjects/dhcp/main.c, requires the generated
#    client to send exactly the model's frame, end with the model's
#    registers, and touch no byte past the record and the frame.
# The subject's own shape (no undefined symbol, no indirect branch, the
# slot's sizes) is checked by scripts/build-subject.sh when the image is
# built.
#
# usage: check-dhcp-subject-host.sh [ordinary|sanitized]
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
lake build LeanOS.Net.DhcpClientC LeanOS.DhcpSubject leanos-net-dhcp-vectors >/dev/null
vectors=build/dhcp-subject-vectors
mkdir -p "$vectors"
if [[ "$mode" == ordinary || ! -f "$vectors/vectors.txt" ]]; then
  .lake/build/bin/leanos-net-dhcp-vectors "$vectors/vectors.txt"
fi
LEANOS_NET_DHCP_VECTORS="$(cd "$vectors" && pwd)/vectors.txt" \
  LEANOS_HOSTED_BOUNDARY_ID=dhcp-subject \
  ./scripts/check-boot-handoff-host.sh "$mode"
