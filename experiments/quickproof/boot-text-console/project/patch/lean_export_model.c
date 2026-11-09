/* TRUSTED MODEL of the Lean export leanos_boot_text_surface, which LeanOS compiles from
 * LeanOS.BootTextConsole.checkRaw (LeanOS/BootTextConsole.lean at ee64a79):
 *
 *   def valid (s : Surface) : Bool :=
 *     s.kind == 2 && s.bits == 16 && s.address == 0xb8000 &&
 *     0 < s.width && s.width ≤ 160 && 0 < s.height && s.height ≤ 64 &&
 *     s.pitch % 2 == 0 && 2 * s.width ≤ s.pitch && s.pitch ≤ 512
 *   def checkRaw kind bits address pitch width height : UInt64 :=
 *     if valid ⟨kind, bits, address, pitch, width, height⟩ then 1 else 0
 *
 * transcribed conjunct by conjunct, in UInt64 arithmetic (2 * width wraps modulo 2^64 in both).  The theorem
 * of this project holds for the program linked with this model; LeanOS's own refinement theorem for the
 * emitted C of the export (LeanOS.Refinement.BootTextConsoleC.bootTextSurfaceC_spec, ADR 0029 method) states the
 * same conjunction about the compiled export. */
#include <stdint.h>
#include "boundary-abi.h"

uint64_t leanos_boot_text_surface(uint64_t kind, uint64_t bits, uint64_t address, uint64_t pitch,
                                  uint64_t width, uint64_t height) {
    if (kind != 2u) return 0;
    if (bits != 16u) return 0;
    if (address != 0xb8000u) return 0;
    if (!(0u < width)) return 0;
    if (!(width <= 160u)) return 0;
    if (!(0u < height)) return 0;
    if (!(height <= 64u)) return 0;
    if (pitch % 2u != 0u) return 0;
    if (!(2u * width <= pitch)) return 0;
    if (!(pitch <= 512u)) return 0;
    return 1;
}
