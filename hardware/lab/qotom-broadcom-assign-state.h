#ifndef LEANOS_LAB_QOTOM_BROADCOM_ASSIGN_STATE_H
#define LEANOS_LAB_QOTOM_BROADCOM_ASSIGN_STATE_H
#include "qotom-broadcom-d3.h"

/* State retained earlier in the boot for the reviewed Broadcom assignment
 * variant (qotom-broadcom-assign.c.inc). The defaults are a rejected D3
 * record and no accepted final vector, so an image variant that never ran
 * those stages fails closed. */
static uint32_t lab_retained_broadcom_d3_status=12;
static struct qotom_broadcom_d3_result lab_retained_broadcom_d3;
static struct pci_enumeration_header lab_retained_broadcom_endpoint;
static uint16_t lab_retained_pci_final_commands[16];
static uint32_t lab_retained_pci_final_match;
#endif
