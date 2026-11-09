# A stand-in for FreeBSD's pmbr in scripts/test-qotom-internal-grub.py
# (issue #620). Loaded at 0x7C00 like a boot sector, it prints the BIOS drive
# number it was given in DL to COM1 ("FREEBSD-PMBR-SENTINEL dl=80") and halts.
# pmbr boots the disk that DL names, so the test checks that GRUB passes the
# internal disk's.
.code16
.global _start
_start:
  cli
  xor %ax,%ax
  mov %ax,%ds
  mov %ax,%ss
  mov $0x7c00,%sp
  mov %dl,%bh
  mov $message,%si
puts:
  lodsb
  test %al,%al
  jz drive
  call putc
  jmp puts
drive:
  mov %bh,%al
  shr $4,%al
  call hexdigit
  mov %bh,%al
  and $0x0f,%al
  call hexdigit
  mov $0x0a,%al
  call putc
stop:
  hlt
  jmp stop
hexdigit:
  add $0x30,%al
  cmp $0x39,%al
  jbe putc
  add $0x27,%al
putc:
  mov %al,%bl
  mov $0x3fd,%dx
wait:
  in %dx,%al
  test $0x20,%al
  jz wait
  mov %bl,%al
  mov $0x3f8,%dx
  out %al,%dx
  ret
message:
  .asciz "FREEBSD-PMBR-SENTINEL dl="
