#!/usr/bin/env bash
set -euo pipefail
SSHPASS="${SSHPASS:?set the FreeBSD SSH password outside the evidence}" \
python3 scripts/run-qotom-recovery-lab.py \
  --host freebsd@192.168.6.21 --host-key-alias freebsd.lan \
  --ssh-prefix "sshpass -e ssh" --usb-serial 11758C40 \
  --serial-device /dev/serial/by-id/usb-FTDI_FT232R_USB_UART_BG03A20M-if00-port0 \
  --elf build/qotom-bsp-production-lab/leanos-qotom-lab.elf \
  --output /tmp/qotom-bsp-production-clean-capture-20260912 \
  --cycles 1 --scenario watchdog-leanos --bsp-production
