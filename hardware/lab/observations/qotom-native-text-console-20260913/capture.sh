#!/usr/bin/env bash
set -euo pipefail
python3 scripts/run-qotom-recovery-lab.py \
  --host freebsd@192.168.6.21 --host-key-alias freebsd.lan \
  --usb-serial 11758C40 \
  --serial-device /dev/serial/by-id/usb-FTDI_FT232R_USB_UART_BG03A20M-if00-port0 \
  --elf build/qotom-lab/leanos-qotom-lab.elf \
  --output build/qotom-lab/physical-screen-retry-20260913 \
  --cycles 1 --scenario watchdog-leanos --cpu-diagnostic \
  --diagnostic-protocol build/qotom-lab/boot/serial-protocol.tsv \
  --diagnostic-replay build/j1900-cpu-host/host
