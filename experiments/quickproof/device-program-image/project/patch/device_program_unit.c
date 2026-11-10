/* The code under test as one library unit: hardware/wifi/wifi-exec.h, unchanged.  Its functions are static, so
 * this unit gives each entry point an external name: the image parser wifi_image_header, which the kernel's three
 * bind paths and the Qotom lab call alone; wifi_start, which they call next; wifi_policy_within, which the lab's
 * admission calls; and the two admission shapes of boot/kernel.c, wifi_service_admitted (the device service) and
 * wifi_source_admitted (the network and DHCP frame sources).  Each wrapper only forwards its arguments.  The
 * executor scratch wifi_scratch is static too: dp_scratch gives the law its address, so that the law can fill it
 * before wifi_start and read it after. */
#include "device_program_api.h"

int dp_header(const uint8_t *image, uint32_t image_len, struct wifi_target *t, struct wifi_policy *pol,
              uint32_t *header_len) {
    return wifi_image_header(image, image_len, t, pol, header_len);
}

int dp_start(struct wifi_vm *vm, const uint8_t *image, uint32_t image_len) {
    return wifi_start(vm, image, image_len);
}

int dp_within(const struct wifi_policy *p, const struct wifi_policy *max) {
    return wifi_policy_within(p, max);
}

int dp_service(const struct wifi_target *t, const struct wifi_policy *p, const struct wifi_target *want,
               const struct wifi_policy *max) {
    return wifi_service_admitted(t, p, want, max);
}

int dp_source(const struct wifi_target *t, const struct wifi_policy *p, const struct wifi_policy *max) {
    return wifi_source_admitted(t, p, max);
}

uint8_t *dp_scratch(void) {
    return wifi_scratch;
}
