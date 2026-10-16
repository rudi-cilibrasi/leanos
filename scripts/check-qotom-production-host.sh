#!/usr/bin/env bash
# Hosted test of the Qotom production network dispatcher (issue #569).
#
# hardware/lab/qotom-production-network.c.inc runs only in the production
# Qotom image, which cannot boot under QEMU. tests/qotom-production-network-host.c
# compiles it against stand-ins for the kernel it is spliced into, links the
# real generated witnesses (the frame port check and window operand, the
# device witness and the cyclic blocking-IPC witness), and drives a whole
# three-subject session through it, then breaks each precondition once.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
modules=(NetworkSubject DhcpSubject FrameCopyWindow BlockingIPC KeyboardEcho ConsoleServer)
lake build LeanOS.FrameCopyWindow LeanOS.BlockingIPC LeanOS.KeyboardEcho >/dev/null
build=build/qotom-production-host
rm -rf "$build"
mkdir -p "$build"
prefix="$(lake env lean --print-prefix)"
generated=build/boundary-abi
./scripts/generate-oracle.sh "$generated" >/dev/null
objects=()
for module in "${modules[@]}"; do
  "${CC:-cc}" -std=c11 -O2 -ffunction-sections -fdata-sections -I"$prefix/include" \
    -c ".lake/build/ir/LeanOS/$module.c" -o "$build/$module.o"
  objects+=("$build/$module.o")
done
"${CC:-cc}" -std=c11 -O2 -Wall -Wextra -Werror -Wno-unused-function \
  -I"$generated" -c tests/qotom-production-network-host.c -o "$build/host.o"
lake env leanc -Wl,--gc-sections "$build/host.o" "${objects[@]}" -o "$build/host"
"$build/host"
