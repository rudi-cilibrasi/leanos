/* Freestanding link of the generated device-program executor (issue #494).

   Built with the boot image's code-generation flags and linked with
   -nostdlib --gc-sections: the generated step, the C hooks of
   hardware/wifi/wifi-gen-exec.h in the kernel's direct-hook configuration and
   the step loop must need no Lean runtime and no libc symbol (`nm -u` empty),
   and the generated step must contain no indirect branch
   (scripts/check-generated-executor-host.sh). Never executed. */
#include <stdint.h>
#include "boundary-abi.h"
#define WIFI_HOOKS_DIRECT 1
#include "../hardware/wifi/wifi-gen-exec.h"

static volatile uint32_t sink;

uint32_t wifi_hook_mmio_read32(uint32_t off) { return sink + off; }
uint16_t wifi_hook_mmio_read16(uint32_t off) { return (uint16_t)(sink + off); }
uint8_t wifi_hook_mmio_read8(uint32_t off) { return (uint8_t)(sink + off); }
void wifi_hook_mmio_write32(uint32_t off, uint32_t value) { sink = off ^ value; }
void wifi_hook_mmio_write16(uint32_t off, uint16_t value) { sink = off ^ value; }
void wifi_hook_mmio_write8(uint32_t off, uint8_t value) { sink = off ^ value; }
uint32_t wifi_hook_cfg_read32(uint32_t off) { return sink + off; }
void wifi_hook_cfg_write32(uint32_t off, uint32_t value) { sink = off ^ value; }
void wifi_hook_delay_us(uint32_t us) { sink = us; }
void wifi_hook_print(uint32_t tag, uint32_t value) { sink = tag ^ value; }
uint32_t wifi_hook_phys(uint32_t off) { return 0x4000u + off; }

/* A one-instruction image: halt. */
static const uint8_t image[] = {
    'L', 'W', 'I', 'F', 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
};

void _start(void);
void _start(void) {
    static struct wifi_vm vm;
    uint32_t code = 0;
    if (!wifi_start(&vm, image, (uint32_t)sizeof image))
        sink = (uint32_t)wifi_gen_resume(&vm, 0, 1, &code) ^ code;
    for (;;) {
    }
}
