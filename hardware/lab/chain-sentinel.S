.code16
.global _start
_start:
  xor %ax,%ax
  mov %ax,%ds
  mov $message,%si
next:
  lodsb
  test %al,%al
  jz stop
  mov %al,%bl
wait:
  mov $0x3fd,%dx
  in %dx,%al
  test $0x20,%al
  jz wait
  mov %bl,%al
  mov $0x3f8,%dx
  out %al,%dx
  jmp next
stop:
  cli
  hlt
  jmp stop
message:
  .asciz "FREEBSD-CHAIN-SENTINEL\n"
