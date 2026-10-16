import LeanOS.Wifi.Bytecode

/-
Realtek RTL8168E-VL wired Ethernet as a Lean device program (issue #452).

Ported from FreeBSD's BSD-licensed `re(4)` driver (`sys/dev/re/if_re.c`,
`sys/dev/rl/if_rlreg.h`, releng/15.0; the source hashes are recorded in
`docs/qotom-realtek-state.md`): the reset, C+ command, descriptor-address,
command, transmit/receive configuration and early-transmit settings that
`re_init_locked` applies to an 8168E-VL (`RL_FLAG_EARLYOFF`, `MACSTAT`,
`JUMBOV2`, `CMDSTOP`, transmit kick through `RL_GTXSTART`).

The Qotom has two of these controllers (10ec:8168 at 01:00.0 and 03:00.0);
this program drives 01:00.0 (FreeBSD's `re0`, the cabled port) through its
memory BAR2 (configuration offset 0x18, 4 KiB). It reads the station address
and link state, sets up one-descriptor receive and transmit rings
in executor scratch, then sends an ARP probe (RFC 5227: sender address
0.0.0.0, so it claims no address on the LAN) for the router and waits for the
reply, printing the router's hardware address and the receive counters.

Every exit after the transmit/receive engines are enabled — success and the
no-link, transmit-stuck and no-reply failures alike — runs one teardown
(issue #577, `docs/net-rtl8168.md`): re(4)'s `re_stop` for CMDSTOP chips
verbatim (receive filter off with the rest of RXCFG kept, stop request with
TE/RE, wait for the transmit queue, let the request settle; no early write of
0 to the command register), interrupts masked and acknowledged, both rings
disarmed in scratch (no descriptor left chip-owned or naming a buffer),
`re_reset`, the 9346CR lock, then Bus Master cleared. The receive ring is a
single descriptor carrying EOR, so the controller's ring position after any
number of frames is descriptor 0 (`Ring.next_one`). The program prints the
controller's registers before it touches it (tags 0x41xx, xx the register
offset) and after the teardown (0x42xx) for the maintainer's comparison.

The descriptor-ring base registers (TNPDS 0x20, THPDS 0x28, RDSAR 0xE4) and
the tally-counter dump address (0x10) are address sinks of its policy; the
buffer pointers inside the descriptors live in scratch (ADR 0021).
-/
namespace LeanOS.Net.Rtl8168

open LeanOS.Wifi.Bytecode

def target : Target :=
  { bus := 1, dev := 0, fn := 0, id := 0x816810ec, windowBytes := 0x1000, bar := 0x18 }

/-! ## Registers (BAR2 offsets, `if_rlreg.h`) -/

def idr0 : UInt32 := 0x00
def idr4 : UInt32 := 0x04
def mar0 : UInt32 := 0x08
def mar4 : UInt32 := 0x0C
def dtccr : UInt32 := 0x10
def tnpds : UInt32 := 0x20
def thpds : UInt32 := 0x28
def command : UInt32 := 0x37      -- 8 bits
def gtxstart : UInt32 := 0x38     -- 8 bits
def imr : UInt32 := 0x3C          -- 16 bits
def isr : UInt32 := 0x3E          -- 16 bits
def txcfg : UInt32 := 0x40
def rxcfg : UInt32 := 0x44
def missedPkt : UInt32 := 0x4C
def eecmd : UInt32 := 0x50        -- 8 bits
def cfg1 : UInt32 := 0x52         -- 8 bits
def cfg3 : UInt32 := 0x54         -- 8 bits
def cfg5 : UInt32 := 0x56         -- 8 bits
def timerInt : UInt32 := 0x58
def gmediastat : UInt32 := 0x6C   -- 8 bits
def maxRxPktLen : UInt32 := 0xDA  -- 16 bits
def cplusCmd : UInt32 := 0xE0     -- 16 bits
def rdsar : UInt32 := 0xE4
def earlyTxThresh : UInt32 := 0xEC  -- 8 bits

def cmdReset : UInt32 := 0x10
def cmdTxRx : UInt32 := 0x0C
def cmdStopReq : UInt32 := 0x80
def txcfgHwrev : UInt32 := 0x7CC00000
def hwrev8168eVl : UInt32 := 0x2C800000
def txcfgQueueEmpty : UInt32 := 0x00000800
/-- `RL_TXCFG_CONFIG`: interframe gap, 2048-byte transmit DMA bursts. -/
def txcfgConfig : UInt32 := 0x03000700
/-- `RL_RXCFG_CONFIG | RL_RXCFG_EARLYOFF | RX_INDIV | RX_BROAD`. -/
def rxcfgConfig : UInt32 := 0x0000E000 ||| 0x00000700 ||| 0x00001800 ||| 0x00003800 ||| 0x2 ||| 0x8
/-- `RL_CPLUSCMD_PCI_MRW | RL_CPLUSCMD_MACSTAT_DIS | 0x0001` (MACSTAT chips). -/
def cplusConfig : UInt32 := 0x0089
/-- `RL_RXCFG_RX_ALLPHYS | RX_INDIV | RX_MULTI | RX_BROAD`: the bits `re_stop`
clears to put the receive MAC into idle. -/
def rxcfgAccept : UInt32 := 0x0000000F

/-- Descriptor bits (`RL_RDESC_*`, `RL_TDESC_*`). -/
def own : UInt32 := 0x80000000
def eor : UInt32 := 0x40000000
def sof : UInt32 := 0x20000000
def eof : UInt32 := 0x10000000
def rxBcast : UInt32 := 0x01000000
def rxErrSum : UInt32 := 0x00100000

/-! ## Scratch layout -/

def rxRing : UInt32 := 0x0000     -- one 16-byte descriptor (EOR), 256-byte aligned
def txRing : UInt32 := 0x0100     -- one descriptor (EOR)
def rxBufs : UInt32 := 0x1000     -- 2 KiB per receive descriptor
def rxBufBytes : UInt32 := 0x800
/-- One receive descriptor, carrying EOR: the controller returns to it after
every frame, so the ring position it keeps is always descriptor 0 (issue
#577, `Ring.next_one`). The 2026-09-29 program used 16. -/
def rxCount : Nat := 1
def txBuf : UInt32 := 0xA000
def vars : UInt32 := 0xB000

namespace Var
def frames : UInt32 := vars + 0x0
def bcasts : UInt32 := vars + 0x4
def errors : UInt32 := vars + 0x8
def found : UInt32 := vars + 0xC
/-- Failure code of a post-enable exit, 0 on success (`exitL`). -/
def failCode : UInt32 := vars + 0x10
/-- Set when the teardown's reset did not complete. -/
def resetFault : UInt32 := vars + 0x14
end Var

namespace Tag
def pciId : UInt32 := 0x4000
def txcfg : UInt32 := 0x4001
def macLo : UInt32 := 0x4002
def macHi : UInt32 := 0x4003
def media : UInt32 := 0x4004
def running : UInt32 := 0x4005
def probeSent : UInt32 := 0x4006
def routerMacLo : UInt32 := 0x4007
def routerMacHi : UInt32 := 0x4008
def frames : UInt32 := 0x4009
def bcasts : UInt32 := 0x400A
def errors : UInt32 := 0x400B
def txStatus : UInt32 := 0x400C
/-- Teardown: the transmit queue did not report empty after the stop request. -/
def stopTimeout : UInt32 := 0x400D
/-- Teardown: `RST` did not clear. -/
def resetTimeout : UInt32 := 0x400E
def done : UInt32 := 0x40FF
/-- Register dumps: `before ||| off` before the program touches the
controller, `after ||| off` after the teardown. -/
def before : UInt32 := 0x4100
def after : UInt32 := 0x4200
end Tag

namespace Fail
def wrongDevice : UInt32 := 0x7B01
def noDma : UInt32 := 0x7B02
def wrongRevision : UInt32 := 0x7B03
def resetStuck : UInt32 := 0x7B04
def noLink : UInt32 := 0x7B05
def txStuck : UInt32 := 0x7B06
def noReply : UInt32 := 0x7B07
/-- The post-enable failures; each still runs the teardown. -/
def afterEnable : List UInt32 := [noLink, txStuck, noReply]
end Fail

/-- The router the probe asks for (192.168.6.1), as the little-endian dword
of its four bytes in a frame. -/
def routerIpLe : UInt32 := 0x0106A8C0

def st (w : Nat) (at_ : UInt32) (src : Operand) : ProgM Unit := do
  li 9 0
  emit (.memStore w 9 at_ src)

def ld (w : Nat) (dst : Reg) (at_ : UInt32) : ProgM Unit := do
  li 9 0
  emit (.memLoad w dst 9 at_)

def incr (at_ : UInt32) : ProgM Unit := do
  ld 4 8 at_
  addi 8 1
  st 4 at_ (.reg 8)

/-- Hand receive descriptor `r(idx)` (index register) back to the chip. -/
def rearm (idx : Reg) : ProgM Unit := do
  let notLast ← newLabel
  let write ← newLabel
  mov 1 idx
  shli 1 4
  li 3 (own ||| rxBufBytes)
  emit (.branch .ne idx (.imm (rxCount - 1).toUInt32) notLast)
  ori 3 eor
  place notLast
  place write
  emit (.memStore 4 1 (rxRing + 4) (.imm 0))
  emit (.memStore 4 1 rxRing (.reg 3))

/-- Subroutine: if receive descriptor `r10` holds a frame, account for it,
look for an ARP reply from the router, re-arm the descriptor and advance
`r10`; `r0` := 1. Otherwise `r0` := 0. -/
def rxPoll : ProgM Nat := do
  let entry ← newLabel
  let empty ← newLabel
  let notBcast ← newLabel
  let noErr ← newLabel
  let done ← newLabel
  place entry
  mov 1 10
  shli 1 4
  emit (.memLoad 4 2 1 rxRing)
  mov 3 2
  andi 3 own
  emit (.branch .ne 3 (.imm 0) empty)
  incr Var.frames
  mov 3 2
  andi 3 rxBcast
  emit (.branch .eq 3 (.imm 0) notBcast)
  incr Var.bcasts
  place notBcast
  mov 3 2
  andi 3 rxErrSum
  emit (.branch .eq 3 (.imm 0) noErr)
  incr Var.errors
  emit (.jump done)
  place noErr
  -- r4 := buffer of descriptor r10
  mov 4 10
  shli 4 11
  addi 4 rxBufs
  -- EtherType 0x0806, ARP opcode 2, sender protocol address = router.
  emit (.memLoad 1 5 4 12)
  shli 5 8
  emit (.memLoad 1 6 4 13)
  emit (.alu .or 5 (.reg 6))
  emit (.branch .ne 5 (.imm 0x0806) done)
  emit (.memLoad 2 5 4 20)
  emit (.branch .ne 5 (.imm 0x0200) done)
  emit (.memLoad 4 5 4 28)
  emit (.branch .ne 5 (.imm routerIpLe) done)
  emit (.memLoad 4 5 4 22)
  print Tag.routerMacLo 5
  emit (.memLoad 2 5 4 26)
  print Tag.routerMacHi 5
  st 4 Var.found (.imm 1)
  place done
  rearm 10
  addi 10 1
  andi 10 (rxCount - 1).toUInt32
  li 0 1
  emit .ret
  place empty
  li 0 0
  emit .ret
  return entry

/-- Receive for up to `ms` milliseconds, stopping early once the router's
reply has been seen. -/
def listen (rxPollL : Nat) (ms : UInt32) : ProgM Unit := do
  let top ← newLabel
  let more ← newLabel
  let out ← newLabel
  li 7 (ms * 10)
  place top
  place more
  emit (.call rxPollL)
  emit (.branch .ne 0 (.imm 0) more)
  ld 4 8 Var.found
  emit (.branch .ne 8 (.imm 0) out)
  -- 100 µs between polls: with one receive descriptor, a frame that lands
  -- while it is still full is dropped, so keep that window short.
  delay 100
  emit (.alu .sub 7 (.imm 1))
  emit (.branch .ne 7 (.imm 0) top)
  place out

/-- Build the 60-byte ARP probe at `txBuf` from the station address in
r5 (bytes 0–3) and r6 (bytes 4–5). -/
def buildProbe : ProgM Unit := do
  for k in [0:6] do st 1 (txBuf + k.toUInt32) (.imm 0xFF)      -- broadcast
  st 4 (txBuf + 6) (.reg 5)
  st 2 (txBuf + 10) (.reg 6)
  for (off, v) in [(12, 0x08), (13, 0x06),                     -- ARP
      (14, 0x00), (15, 0x01), (16, 0x08), (17, 0x00),          -- Ethernet, IPv4
      (18, 6), (19, 4), (20, 0x00), (21, 0x01)] do              -- request
    st 1 (txBuf + off) (.imm v)
  st 4 (txBuf + 22) (.reg 5)                                     -- sender MAC
  st 2 (txBuf + 26) (.reg 6)
  -- sender IP 0.0.0.0 and target MAC 0 are already zero (scratch starts zeroed)
  st 4 (txBuf + 38) (.imm routerIpLe)                            -- target IP

/-! ## Register dumps -/

/-- The registers the before/after dumps print, with their widths in bytes:
the command, interrupt, transmit/receive configuration, missed-packet,
9346CR and CONFIG1/3/5, timer, PHY-status, receive-length, C+ command and
early-transmit registers, and both dwords of every DMA address register. All
are plain reads (none of them is cleared by reading). -/
def dumpRegs : List (UInt32 × Nat) :=
  [(command, 1), (imr, 2), (isr, 2), (txcfg, 4), (rxcfg, 4), (missedPkt, 4), (eecmd, 1),
   (cfg1, 1), (cfg3, 1), (cfg5, 1), (timerInt, 4), (gmediastat, 1), (maxRxPktLen, 2),
   (cplusCmd, 2), (earlyTxThresh, 1), (dtccr, 4), (dtccr + 4, 4), (tnpds, 4), (tnpds + 4, 4),
   (thpds, 4), (thpds + 4, 4), (rdsar, 4), (rdsar + 4, 4)]

/-- Print every `dumpRegs` register as tag `base ||| offset` (uses r0). -/
def dump (base : UInt32) : ProgM Unit := do
  for (off, w) in dumpRegs do
    match w with
    | 1 => emit (.read8 0 off)
    | 2 => r16 0 off
    | _ => r32 0 off
    print (base ||| off) 0

/-! ## Teardown (issue #577) -/

/-- Hand the controller back in the state re(4)'s own `re_stop` and
`re_reset` leave it in (`re_init_locked` runs exactly these two before it
reprograms the chip). Never fails: like re(4), a stop or reset timeout is
reported (tags `stopTimeout`, `resetTimeout`) and the teardown goes on; a
reset timeout is recorded in `Var.resetFault`. Uses r9 and r12–r14.

1. `re_stop`: clear only the four accept bits of RXCFG, keeping the FIFO,
   DMA-burst and EARLYOFF fields; request the stop with TE and RE set (the
   CMDSTOP chips); wait for TXCFG queue-empty; then `DELAY(1000)`. re(4)
   writes nothing else to the command register here. The program before
   issue #577 zeroed RXCFG and wrote 0 to the command register right after
   the queue-empty poll, cutting the stop request short.
2. Mask and acknowledge every interrupt.
3. Disarm both rings in scratch: every descriptor keeps only EOR (never
   OWN) and names no buffer, so whatever ring base the controller retains,
   it finds nothing it may fill.
4. `re_reset`: `RST`, polled until it clears.
5. Lock the configuration registers (9346CR = 0). -/
def teardown : ProgM Unit := do
  r32 12 rxcfg
  andi 12 (~~~rxcfgAccept)
  emit (.write32 rxcfg (.reg 12))
  emit (.write8 command (.imm (cmdStopReq ||| cmdTxRx)))
  let txqTop ← newLabel
  let txqDone ← newLabel
  li 14 1000
  place txqTop
  r32 13 txcfg
  andi 13 txcfgQueueEmpty
  emit (.branch .ne 13 (.imm 0) txqDone)
  delay 100
  emit (.alu .sub 14 (.imm 1))
  emit (.branch .ne 14 (.imm 0) txqTop)
  printImm Tag.stopTimeout 0
  place txqDone
  delay 1000
  w16 imr 0
  w16 isr 0xFFFF
  for k in [0:rxCount] do
    let d := rxRing + 16 * k.toUInt32
    st 4 d (.imm (if k + 1 == rxCount then eor else 0))
    st 4 (d + 8) (.imm 0)
  st 4 txRing (.imm eor)
  st 4 (txRing + 8) (.imm 0)
  emit (.write8 command (.imm cmdReset))
  let rstTop ← newLabel
  let rstDone ← newLabel
  li 14 1000
  place rstTop
  delay 10
  emit (.read8 13 command)
  andi 13 cmdReset
  emit (.branch .eq 13 (.imm 0) rstDone)
  emit (.alu .sub 14 (.imm 1))
  emit (.branch .ne 14 (.imm 0) rstTop)
  printImm Tag.resetTimeout 0
  st 4 Var.resetFault (.imm 1)
  place rstDone
  emit (.write8 eecmd (.imm 0))

/-- Leave through the common exit with failure `code` (after enable). -/
def abortTo (exitL : Nat) (code : UInt32) : ProgM Unit := do
  st 4 Var.failCode (.imm code)
  emit (.jump exitL)

/-- The common exit: teardown, the after-dump, Bus Master off, then the
recorded outcome — the post-enable failure, else a teardown reset fault,
else success. -/
def exitBlock (exitL : Nat) : ProgM Unit := do
  place exitL
  teardown
  dump Tag.after
  emit (.cfgUpdate32 0x04 0xFFFF0004 0x0002)
  ld 4 0 Var.failCode
  for c in Fail.afterEnable do
    let next ← newLabel
    emit (.branch .ne 0 (.imm c) next)
    fail c
    place next
  ld 4 0 Var.resetFault
  let ok ← newLabel
  emit (.branch .eq 0 (.imm 0) ok)
  fail Fail.resetStuck
  place ok
  printImm Tag.done 0
  halt

def program : ProgM Unit := do
  setTarget target
  emit (.cfgRead32 0 0)
  print Tag.pciId 0
  expectEq 0 0x816810ec Fail.wrongDevice
  emit (.physAddr 0 0)
  let dmaOk ← newLabel
  emit (.branch .ne 0 (.imm 0) dmaOk)
  fail Fail.noDma
  place dmaOk
  emit (.cfgUpdate32 0x04 0xFFFF0000 0x0006)
  r32 0 txcfg
  print Tag.txcfg 0
  andi 0 txcfgHwrev
  expectEq 0 hwrev8168eVl Fail.wrongRevision
  -- The state the previous owner (firmware or FreeBSD) left behind.
  dump Tag.before
  r32 5 idr0
  print Tag.macLo 5
  r16 6 idr4
  print Tag.macHi 6
  -- re_reset
  emit (.write8 command (.imm cmdReset))
  let resetTop ← newLabel
  let resetDone ← newLabel
  li 14 1000
  place resetTop
  delay 10
  emit (.read8 13 command)
  andi 13 cmdReset
  emit (.branch .eq 13 (.imm 0) resetDone)
  emit (.alu .sub 14 (.imm 1))
  emit (.branch .ne 14 (.imm 0) resetTop)
  fail Fail.resetStuck
  place resetDone
  -- Rings: every receive descriptor owned by the chip; one transmit slot.
  for k in [0:rxCount] do
    emit (.physAddr 0 (rxBufs + rxBufBytes * k.toUInt32))
    st 4 (rxRing + 16 * k.toUInt32 + 8) (.reg 0)
    st 4 (rxRing + 16 * k.toUInt32 + 12) (.imm 0)
    li 10 k.toUInt32
    rearm 10
  emit (.physAddr 0 txBuf)
  st 4 (txRing + 8) (.reg 0)
  st 4 Var.failCode (.imm 0)
  st 4 Var.resetFault (.imm 0)
  let exitL ← newLabel
  -- re_init_locked
  emit (.write16 cplusCmd (.imm cplusConfig))
  emit (.write8 eecmd (.imm 0xC0))
  emit (.write32 idr0 (.reg 5))
  emit (.write32 idr4 (.reg 6))
  emit (.write8 eecmd (.imm 0x00))
  w32 (rdsar + 4) 0
  emit (.physAddr 0 rxRing)
  emit (.write32 rdsar (.reg 0))
  w32 (tnpds + 4) 0
  emit (.physAddr 0 txRing)
  emit (.write32 tnpds (.reg 0))
  -- From here on, every exit goes through `exitBlock` (the teardown).
  emit (.write8 command (.imm cmdTxRx))
  w32 txcfg txcfgConfig
  emit (.write8 earlyTxThresh (.imm 16))
  w32 mar0 0
  w32 mar4 0
  w32 rxcfg rxcfgConfig
  w16 imr 0
  w16 isr 0xFFFF
  w16 maxRxPktLen 0x600
  printImm Tag.running 0
  -- Link (the PHY autonegotiates on its own): wait up to 5 s.
  let linkTop ← newLabel
  let linkUp ← newLabel
  li 14 5000
  place linkTop
  emit (.read8 13 gmediastat)
  mov 12 13
  andi 13 0x02
  emit (.branch .ne 13 (.imm 0) linkUp)
  delay 1000
  emit (.alu .sub 14 (.imm 1))
  emit (.branch .ne 14 (.imm 0) linkTop)
  print Tag.media 12
  abortTo exitL Fail.noLink
  place linkUp
  print Tag.media 12
  buildProbe
  let rxPollL ← do
    let skip ← newLabel
    emit (.jump skip)
    let l ← rxPoll
    place skip
    pure l
  li 10 0
  -- Up to three probes, one second apart.
  let replied ← newLabel
  for _ in [0:3] do
    st 4 (txRing + 4) (.imm 0)
    st 4 txRing (.imm (own ||| eor ||| sof ||| eof ||| 60))
    emit (.write8 gtxstart (.imm 0x40))
    let txTop ← newLabel
    let txDone ← newLabel
    li 14 100
    place txTop
    ld 4 13 txRing
    andi 13 own
    emit (.branch .eq 13 (.imm 0) txDone)
    delay 1000
    emit (.alu .sub 14 (.imm 1))
    emit (.branch .ne 14 (.imm 0) txTop)
    abortTo exitL Fail.txStuck
    place txDone
    ld 4 13 txRing
    print Tag.txStatus 13
    printImm Tag.probeSent 0
    listen rxPollL 1000
    ld 4 8 Var.found
    emit (.branch .ne 8 (.imm 0) replied)
  ld 4 0 Var.frames; print Tag.frames 0
  abortTo exitL Fail.noReply
  place replied
  ld 4 0 Var.frames; print Tag.frames 0
  ld 4 0 Var.bcasts; print Tag.bcasts 0
  ld 4 0 Var.errors; print Tag.errors 0
  exitBlock exitL

/-! ## Why the ring position matters (issue #577)

A model of the receive-descriptor engine as both sides see it. The
controller fills descriptors in order and, after the one carrying EOR (the
last of the ring), returns to the first. FreeBSD's `re_rxeof` consumes
descriptors in order from `rl_rx_prodidx`, which `re_rx_list_init` sets to
0, and stops at the first one the controller still owns. If the controller
enters FreeBSD's 256-descriptor ring at a position `start ≠ 0` — a position
retained from the LeanOS run — FreeBSD sees nothing for `256 - start`
frames, then the whole backlog, exactly 256 frames, at once; the controller
is then back at `start` and the cycle repeats (`docs/net-rtl8168.md`). The
program's one-descriptor receive ring makes any position it leaves 0. -/
namespace Ring

/-- The descriptor the controller fills next in a ring of `size`
descriptors (EOR on the last), having entered at `start` and completed `n`
descriptors since. -/
def next (size start n : Nat) : Nat := (start + n) % size

/-- One descriptor with EOR: after any number of frames the controller is
back at descriptor 0. -/
theorem next_one (start n : Nat) : next 1 start n = 0 := Nat.mod_one _

/-- The 16-descriptor ring of 2026-09-29: its run received one frame and so
left the controller one descriptor in. -/
theorem next_sixteen_observed : next 16 0 1 = 1 := by decide

/-- After a full pass the controller is where it entered: the misalignment
is periodic and never heals by itself. -/
theorem next_full_pass (size start : Nat) : next size start size = start % size := by
  simp [next]

/-- Within the first pass (`f ≤ size` frames), descriptor `i` of a ring
entered at `start` has been completed. -/
def completed (size start f i : Nat) : Bool := decide ((i + size - start) % size < f)

/-- The frames FreeBSD's `re_rxeof` has consumed after the controller
completed `f ≤ size` frames: the completed prefix from descriptor 0. -/
def seen (size start f : Nat) : Nat :=
  ((List.range size).takeWhile (completed size start f)).length

theorem takeWhile_of_all {α} (p : α → Bool) :
    ∀ l : List α, (∀ x ∈ l, p x = true) → l.takeWhile p = l
  | [], _ => rfl
  | a :: l, h => by
    rw [List.takeWhile_cons_of_pos (h a (by simp))]
    exact congrArg _ (takeWhile_of_all p l fun x hx => h x (by simp [hx]))

/-- Entered off position 0, descriptor 0 stays owned by the controller for
the first `size - start` frames. -/
theorem first_pending {size start f : Nat} (h0 : 0 < start) (hs : start < size)
    (hf : f ≤ size - start) : completed size start f 0 = false := by
  have h : (size - start) % size = size - start := Nat.mod_eq_of_lt (by omega)
  simp only [completed, Nat.zero_add, h, decide_eq_false_iff_not]
  omega

/-- …so FreeBSD consumes nothing during those frames. -/
theorem seen_none {size start f : Nat} (h0 : 0 < start) (hs : start < size)
    (hf : f ≤ size - start) : seen size start f = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, size = n + 1 := ⟨size - 1, by omega⟩
  simp [seen, List.range_succ_eq_map, first_pending h0 hs hf]

/-- After a full pass every descriptor is complete and FreeBSD consumes the
whole ring at once. -/
theorem seen_full {size start : Nat} (hs : start < size) : seen size start size = size := by
  unfold seen
  rw [takeWhile_of_all _ _ (fun i _ => by
    simp only [completed, decide_eq_true_eq]
    exact Nat.mod_lt _ (by omega))]
  simp

/-- Entered at position 0, FreeBSD consumes every frame as it arrives. -/
theorem seen_aligned {size f : Nat} (hf : f ≤ size) : seen size 0 f = f := by
  obtain ⟨m, rfl⟩ : ∃ m, size = f + m := ⟨size - f, by omega⟩
  have hc : ∀ i, i < f + m → completed (f + m) 0 f i = decide (i < f) := by
    intro i hi
    simp [completed, Nat.mod_eq_of_lt hi]
  unfold seen
  rw [List.range_add, List.takeWhile_append_of_pos (fun a ha => by
    have := List.mem_range.mp ha
    rw [hc a (by omega)]
    simpa using this)]
  cases m with
  | zero => simp
  | succ m =>
    have : completed (f + (m + 1)) 0 f f = false := by
      rw [hc f (by omega)]; simp
    simp [List.range_succ_eq_map, this]

/-- FreeBSD's 256-descriptor ring after the 2026-09-29 run (position 1):
nothing for 255 frames, then exactly 256 at once. -/
theorem freebsd_after_observed_run : seen 256 1 255 = 0 ∧ seen 256 1 256 = 256 :=
  ⟨seen_none (by decide) (by decide) (by decide), seen_full (by decide)⟩

/-- With the teardown's ring the controller enters FreeBSD's ring at 0. -/
theorem freebsd_after_fixed_run (start n f : Nat) (hf : f ≤ 256) :
    seen 256 (next 1 start n) f = f := by
  rw [next_one]; exact seen_aligned hf

end Ring

end LeanOS.Net.Rtl8168
