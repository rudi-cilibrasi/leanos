/* Hosted regression test of the generated device-program executor (issue
   #494).

   Every image of the fuzz corpus in $LEANOS_DEVICE_PROGRAM_CORPUS
   (tests/WifiFuzz.lean: NNNN.bin plus the simulator's expected.txt) runs
   through the executor every LeanOS kernel boots, `leanos_device_program_step`
   (the compiled `LeanOS.Wifi.Exec.step`) driven by
   hardware/wifi/wifi-gen-exec.h, with the fuzzer's device model. Each summary
   line must equal the simulator's (`Sim.run`) line. The module is never
   initialized: the generated step needs no Lean runtime. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "boundary-abi.h"
#include "../hardware/wifi/wifi-gen-exec.h"
#include "../hardware/wifi/fuzz-model.h"

extern void leanos_register_boundary_target(const char *, void *);

int main(void) {
    const char *dir = getenv("LEANOS_DEVICE_PROGRAM_CORPUS");
    if (!dir) {
        fprintf(stderr, "error: LEANOS_DEVICE_PROGRAM_CORPUS is unset\n");
        return 2;
    }
    leanos_register_boundary_target("leanos_device_program_step",
        (void *)(uintptr_t)&leanos_device_program_step);
    /* One direct step of a one-instruction image (`halt`). */
    static const uint8_t halt_image[] = {
        'L', 'W', 'I', 'F', 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    };
    static struct wifi_vm halt_vm;
    if (wifi_start(&halt_vm, halt_image, (uint32_t)sizeof halt_image)) return 2;
    wifi_gen_vm = &halt_vm;
    wifi_gen_h = 0;
    if (leanos_device_program_step(0) != WIFI_HALT || wifi_gen_status != WIFI_HALT ||
        halt_vm.pc != 1 || halt_vm.steps != 1) {
        fprintf(stderr, "error: the generated step did not halt the one-instruction image\n");
        return 1;
    }
    static char path[4096], expected[512], generated[512];
    static uint8_t image[1 << 20];
    snprintf(path, sizeof path, "%s/expected.txt", dir);
    FILE *lines = fopen(path, "r");
    if (!lines) { perror(path); return 2; }
    unsigned count = 0;
    while (fgets(expected, sizeof expected, lines)) {
        expected[strcspn(expected, "\n")] = 0;
        snprintf(path, sizeof path, "%s/%04u.bin", dir, count);
        FILE *f = fopen(path, "rb");
        if (!f) { perror(path); return 2; }
        size_t len = fread(image, 1, sizeof image, f);
        fclose(f);
        fuzz_summary(image, (uint32_t)len, wifi_gen_resume, generated, sizeof generated);
        if (strcmp(generated, expected)) {
            fprintf(stderr, "error: program %u disagrees\n  sim:       %s\n"
                "  generated: %s\n", count, expected, generated);
            return 1;
        }
        ++count;
    }
    fclose(lines);
    if (count == 0) {
        fprintf(stderr, "error: empty corpus %s\n", dir);
        return 1;
    }
    printf("Generated device-program executor: %u programs agree with Sim\n", count);
    return 0;
}
