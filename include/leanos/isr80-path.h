#ifndef LEANOS_ISR80_PATH_H
#define LEANOS_ISR80_PATH_H

/*
 * isr80's typed return-path selector (issue #560).
 *
 * After syscall_handler returns, isr80 in boot/boot.S picks the path that
 * leaves the kernel.  It reads that choice from the kernel-owned word
 * isr80_return_path, never from the reply word in RAX.  isr80 stores
 * LEANOS_ISR80_PATH_REPLY there before each call; a handler that switches
 * subjects overwrites it, through isr80_select in boot/kernel.c, with one of
 * the codes below once its model step has been checked.  A selector this
 * image does not handle stops the machine (ud2) in isr80.
 *
 * The codes and their names are LeanOS.Isr80PathSelector.Path.code and
 * Path.macroName.  boot/boot.S repeats these definitions because it is also
 * assembled from copies outside the tree; scripts/check-isr80-path-selector.py
 * (run by scripts/check-entry-policy.sh) requires all three to agree.
 */
#define LEANOS_ISR80_PATH_REPLY 0
#define LEANOS_ISR80_PATH_DISPATCH_FRESH_B 1
#define LEANOS_ISR80_PATH_BLOCK_B_ENTER_A 2
#define LEANOS_ISR80_PATH_WAKE_B 3
#define LEANOS_ISR80_PATH_BLOCK_B_RESUME_A 4
#define LEANOS_ISR80_PATH_BLOCK_C_ENTER_B 5
#define LEANOS_ISR80_PATH_REPORT_B_ENTER_A 6
#define LEANOS_ISR80_PATH_WAKE_C 7
#define LEANOS_ISR80_PATH_SERVER_C_RESUMES_CLIENT 8
#define LEANOS_ISR80_PATH_TIMER_C_RESUMES_A 9
#define LEANOS_ISR80_PATH_TIMER_A_WAITS 10
#define LEANOS_ISR80_PATH_FRAME_C_RESUMES_A 11
#define LEANOS_ISR80_PATH_FRAME_B_WAKES_C 12
#define LEANOS_ISR80_PATH_FRAME_C_RESUMES_B 13
#define LEANOS_ISR80_PATH_LOADER_ENTER_CHILD 14
#define LEANOS_ISR80_PATH_LOADER_CHILD_SENT 15

#endif
