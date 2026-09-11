#ifndef LEANOS_LAB_QOTOM_ECAM_NATIVE_H
#define LEANOS_LAB_QOTOM_ECAM_NATIVE_H
#include <stddef.h>
#include "qotom-ecam-memory.h"

_Static_assert(offsetof(struct lab_ecam_controls, pat) == 0, "PAT ABI");
_Static_assert(offsetof(struct lab_ecam_controls, cr0) == 8, "CR0 ABI");
_Static_assert(offsetof(struct lab_ecam_controls, cr3) == 16, "CR3 ABI");
_Static_assert(offsetof(struct lab_ecam_controls, cr4) == 24, "CR4 ABI");
_Static_assert(offsetof(struct lab_ecam_controls, efer) == 32, "EFER ABI");
_Static_assert(offsetof(struct lab_ecam_controls, rflags) == 40, "RFLAGS ABI");
_Static_assert(sizeof(struct lab_ecam_controls) == 48, "control block ABI");

/* Trusted primitives for an already checked aperture transaction. The mapped
 * address must be aligned, and outputs must be private kernel storage. Faults
 * remain terminal under the caller's early exception/watchdog policy. */
int lab_ecam_native_controls(void *, struct lab_ecam_controls *);
void lab_ecam_native_invalidate(void *, uint64_t);
int lab_ecam_native_load32(void *, uint64_t, uint32_t *);
#endif
