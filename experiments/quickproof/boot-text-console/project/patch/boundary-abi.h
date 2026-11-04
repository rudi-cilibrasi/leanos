/* Shim for LeanOS's generated build/boot/boundary-abi.h: the one export include/boot_text_console.h calls,
   with the prototype the generated header gives it. */
#ifndef LEANOS_BOUNDARY_ABI_H
#define LEANOS_BOUNDARY_ABI_H
#include <stdint.h>
uint64_t leanos_boot_text_surface(uint64_t kind, uint64_t bits, uint64_t address, uint64_t pitch,
                                  uint64_t width, uint64_t height);
#endif
