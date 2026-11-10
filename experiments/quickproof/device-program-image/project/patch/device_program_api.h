/* The external names patch/device_program_unit.c gives the image parser and the policy admission of
   hardware/wifi/wifi-exec.h (see there). */
#ifndef LEANOS_DEVICE_PROGRAM_API_H
#define LEANOS_DEVICE_PROGRAM_API_H
#include "wifi-exec.h"

int dp_header(const uint8_t *image, uint32_t image_len, struct wifi_target *t, struct wifi_policy *pol,
              uint32_t *header_len);
int dp_start(struct wifi_vm *vm, const uint8_t *image, uint32_t image_len);
int dp_within(const struct wifi_policy *p, const struct wifi_policy *max);
int dp_service(const struct wifi_target *t, const struct wifi_policy *p, const struct wifi_target *want,
               const struct wifi_policy *max);
int dp_source(const struct wifi_target *t, const struct wifi_policy *p, const struct wifi_policy *max);
uint8_t *dp_scratch(void);
#endif
