import LeanOS.Usb.Xhci

/-
USB keyboard for LeanOS: find a boot-protocol HID keyboard (directly on a
root port or behind one USB 2.0 hub), configure it and turn its reports into
characters for a bounded session.

USB 2.0 chapter 9/11 requests and HID 1.11 boot protocol (appendix B), US
keyboard layout (HID usage tables, keyboard page 0x07).
-/
namespace LeanOS.Usb.Keyboard

open LeanOS.Wifi.Bytecode LeanOS.Usb.Xhci

variable [Layout]

/-! ## State (scratch words after the xHCI driver's) -/

namespace V
def devSlot : UInt32 := vars + 0x100     -- slot of the device being probed
def rootPort : UInt32 := vars + 0x104
def hubSlot : UInt32 := vars + 0x108
def hubPorts : UInt32 := vars + 0x10C
def kbdSlot : UInt32 := vars + 0x110
def kbdRoute : UInt32 := vars + 0x114
def kbdSpeed : UInt32 := vars + 0x118
def kbdTt : UInt32 := vars + 0x11C
def iface : UInt32 := vars + 0x120
def epAddr : UInt32 := vars + 0x124
def epMps : UInt32 := vars + 0x128
def epInterval : UInt32 := vars + 0x12C
def cfgValue : UInt32 := vars + 0x130
def dci : UInt32 := vars + 0x134
def ids : UInt32 := vars + 0x138
def elapsed : UInt32 := vars + 0x13C
def lastMf : UInt32 := vars + 0x140
def keys : UInt32 := vars + 0x144
def portStatus : UInt32 := vars + 0x148
def hubPortNo : UInt32 := vars + 0x14C
def tries : UInt32 := vars + 0x150
def reports : UInt32 := vars + 0x154
end V

namespace Tag
def hub : UInt32 := 0x2010
def hubPorts : UInt32 := 0x2011
def hubPortStatus : UInt32 := 0x2012
def device : UInt32 := 0x2013
def iface : UInt32 := 0x2014
def endpoint : UInt32 := 0x2015
def configured : UInt32 := 0x2016
def leds : UInt32 := 0x2017
def report : UInt32 := 0x2018
def key : UInt32 := 0x2100
def ready : UInt32 := 0x2101
def sessionEnd : UInt32 := 0x2102
def notKeyboard : UInt32 := 0x2019
def reports : UInt32 := 0x2103
end Tag

namespace Fail
def noKeyboard : UInt32 := 0x7F20
def noBootInterface : UInt32 := 0x7F21
end Fail

/-- US layout: HID usage → ASCII, unshifted and shifted (usages 0..63). -/
def asciiTable (shifted : Bool) : Array UInt32 := Id.run do
  let mut t := Array.replicate 64 (0 : UInt32)
  for i in [0:26] do
    t := t.set! (4 + i) ((if shifted then 'A' else 'a').toNat + i).toUInt32
  let digits := if shifted then "!@#$%^&*()" else "1234567890"
  for i in [0:10] do
    t := t.set! (0x1E + i) (digits.toList.getD i ' ').toNat.toUInt32
  t := t.set! 0x28 0x0A          -- Enter
  t := t.set! 0x29 0x1B          -- Escape
  t := t.set! 0x2A 0x08          -- Backspace
  t := t.set! 0x2B 0x09          -- Tab
  t := t.set! 0x2C 0x20          -- Space
  let punct := if shifted then "_+{}|~:\"~<>?" else "-=[]\\#;'`,./"
  for i in [0:12] do
    t := t.set! (0x2D + i) (punct.toList.getD i ' ').toNat.toUInt32
  return t

def tableBytes : ByteArray := Id.run do
  let mut b := ByteArray.empty
  for v in asciiTable false ++ asciiTable true do b := putU32 b v
  return b

/-! ## Helpers -/

/-- Disable Slot (type 10) for the slot in `slotVar`. -/
def disableSlot (slotVar : UInt32) : ProgM Unit := do
  ld 4 7 slotVar
  shli 7 24
  ori 7 ((10 : UInt32) <<< 10)
  command (.imm 0) (.reg 7)

/-- Hub class request on the hub's control pipe (driver context 0). -/
def hubReq (setup0 : Operand) (setup1 : Operand) (len : UInt32) (dirIn : Bool) : ProgM Unit :=
  control 0 V.hubSlot setup0 setup1 len dirIn

/-- GET_STATUS(port in r(portReg)) → `V.portStatus` (wPortStatus | wPortChange << 16). -/
def hubPortGetStatus (portReg : Reg) : ProgM Unit := do
  mov 8 portReg
  st 4 V.hubPortNo (.reg 8)
  ld 4 8 V.hubPortNo
  ori 8 ((4 : UInt32) <<< 16)
  hubReq (.imm ((0xA3 : UInt32) ||| ((0 : UInt32) <<< 8))) (.reg 8) 4 true
  ld 4 1 dataBuf
  st 4 V.portStatus (.reg 1)

/-- SET_FEATURE / CLEAR_FEATURE(feature) on hub port `V.hubPortNo`. -/
def hubPortFeature (set : Bool) (feature : UInt32) : ProgM Unit := do
  ld 4 8 V.hubPortNo
  hubReq (.imm ((0x23 : UInt32) ||| ((if set then (3 : UInt32) else 1) <<< 8) ||| (feature <<< (16 : UInt32)))) (.reg 8) 0 false

/-! ## Enumeration -/

/-- Probe root ports 1–6: address each connected device in driver context 0
and keep the first hub (`V.hubSlot`, `V.rootPort`); other devices' slots are
disabled again. Jumps to `hubFound`, or falls through when no hub exists. -/
def findHub (hubFound : Nat) : ProgM Unit := do
  for p in [1:7] do
    let port := p.toUInt32
    let next ← newLabel
    resetRootPort port
    emit (.branch .eq 0 (.imm 0) next)
    -- speed from PORTSC bits 10–13
    shri 0 10
    andi 0 0xF
    mov 2 0
    li 1 0                                   -- route string
    li 3 port
    li 4 0                                   -- no TT
    st 4 V.rootPort (.imm port)
    enableAndAddress 0 V.devSlot 1 2 3 4
    getDeviceDescriptor 0 V.devSlot
    ld 1 1 (dataBuf + 4)                     -- bDeviceClass
    print Tag.device 1
    let notHub ← newLabel
    emit (.branch .ne 1 (.imm 9) notHub)
    ld 4 1 V.devSlot
    st 4 V.hubSlot (.reg 1)
    emit (.jump hubFound)
    place notHub
    disableSlot V.devSlot
    place next

/-- Configure the hub in context 0: SET_CONFIGURATION(1), hub descriptor,
mark the slot as a hub (Configure Endpoint with the Hub fields), power all
ports. -/
def setupHub : ProgM Unit := do
  control 0 V.hubSlot (.imm ((0x00 : UInt32) ||| ((9 : UInt32) <<< 8) ||| ((1 : UInt32) <<< 16))) (.imm 0) 0 false
  hubReq (.imm ((0xA0 : UInt32) ||| ((6 : UInt32) <<< 8) ||| ((0x2900 : UInt32) <<< 16))) (.imm ((9 : UInt32) <<< 16)) 9 true
  ld 1 1 (dataBuf + 2)
  st 4 V.hubPorts (.reg 1)
  print Tag.hubPorts 1
  -- Configure Endpoint: slot context with Hub = 1, number of ports, TTT
  clearInput
  st 4 (ictx 0 1) (.imm 0x1)
  li 1 (((3 : UInt32) <<< 20) ||| ((1 : UInt32) <<< 26) ||| ((1 : UInt32) <<< 27))       -- HS, Hub, 1 entry
  st 4 (ictx 1 0) (.reg 1)
  ld 4 1 V.rootPort
  shli 1 16
  ld 4 2 V.hubPorts
  shli 2 24
  emit (.alu .or 1 (.reg 2))
  st 4 (ictx 1 1) (.reg 1)
  ld 2 1 (dataBuf + 3)                                  -- wHubCharacteristics
  shri 1 5
  andi 1 3                                              -- TT think time
  shli 1 16
  st 4 (ictx 1 2) (.reg 1)
  ld 4 7 V.hubSlot
  shli 7 24
  ori 7 ((12 : UInt32) <<< 10)
  emit (.physAddr 6 inputCtx)
  command (.reg 6) (.reg 7)
  printImm Tag.hub 0
  -- power every port
  for p in [1:5] do
    let skip ← newLabel
    ld 4 1 V.hubPorts
    emit (.branch .ltu 1 (.imm p.toUInt32) skip)
    st 4 V.hubPortNo (.imm p.toUInt32)
    hubPortFeature true 8                               -- PORT_POWER
    place skip
  delay 250000

/-- Scan hub ports 1–4 for a device, reset it, address it in context 1 with
the hub's transaction translator, read its descriptors and accept it if it
has a boot-keyboard interface (else disable the slot and continue). Jumps to
`found`; falls through when none. -/
def findKeyboardOnHub (found : Nat) : ProgM Unit := do
  for p in [1:5] do
    let next ← newLabel
    ld 4 1 V.hubPorts
    emit (.branch .ltu 1 (.imm p.toUInt32) next)
    li 5 p.toUInt32
    hubPortGetStatus 5
    ld 4 1 V.portStatus
    print Tag.hubPortStatus 1
    andi 1 1                                            -- connection
    emit (.branch .eq 1 (.imm 0) next)
    hubPortFeature true 4                               -- PORT_RESET
    st 4 V.tries (.imm 50)
    let wait ← newLabel
    let reset ← newLabel
    place wait
    delay 10000
    li 5 p.toUInt32
    hubPortGetStatus 5
    ld 4 1 V.portStatus
    andi 1 0x12                                         -- reset | enable
    emit (.branch .eq 1 (.imm 0x02) reset)
    ld 4 1 V.tries
    emit (.alu .sub 1 (.imm 1))
    st 4 V.tries (.reg 1)
    emit (.branch .ne 1 (.imm 0) wait)
    emit (.jump next)
    place reset
    hubPortFeature false 20                             -- C_PORT_RESET
    hubPortFeature false 16                             -- C_PORT_CONNECTION
    delay 20000
    ld 4 1 V.portStatus
    print Tag.hubPortStatus 1
    -- speed: bit 9 low, bit 10 high, else full
    li 2 1
    mov 3 1
    andi 3 0x200
    let notLs ← newLabel
    emit (.branch .eq 3 (.imm 0) notLs)
    li 2 2
    place notLs
    mov 3 1
    andi 3 0x400
    let notHs ← newLabel
    emit (.branch .eq 3 (.imm 0) notHs)
    li 2 3
    place notHs
    st 4 V.kbdSpeed (.reg 2)
    st 4 V.kbdRoute (.imm p.toUInt32)
    -- TT hub slot | TT port << 8 for low/full speed devices
    li 4 0
    let noTt ← newLabel
    emit (.branch .eq 2 (.imm 3) noTt)
    ld 4 4 V.hubSlot
    ori 4 (p.toUInt32 <<< 8)
    place noTt
    st 4 V.kbdTt (.reg 4)
    li 1 p.toUInt32
    ld 4 3 V.rootPort
    enableAndAddress 1 V.kbdSlot 1 2 3 4
    getDeviceDescriptor 1 V.kbdSlot
    ld 4 1 (dataBuf + 8)
    st 4 V.ids (.reg 1)
    findBootInterface
    ld 4 1 V.epAddr
    emit (.branch .ne 1 (.imm 0) found)
    printImm Tag.notKeyboard p.toUInt32
    disableSlot V.kbdSlot
    place next
where
  /-- Read the configuration descriptor of the device in context 1 and record
  the first boot-keyboard interface's interrupt IN endpoint (`V.epAddr` stays
  0 if there is none). -/
  findBootInterface : ProgM Unit := do
    st 4 V.epAddr (.imm 0)
    control 1 V.kbdSlot (.imm ((0x80 : UInt32) ||| ((6 : UInt32) <<< 8) ||| ((0x0200 : UInt32) <<< 16))) (.imm ((255 : UInt32) <<< 16)) 255 true
    ld 1 1 (dataBuf + 5)
    st 4 V.cfgValue (.reg 1)
    ld 2 8 (dataBuf + 2)                                -- wTotalLength
    let small ← newLabel
    emit (.branch .ltu 8 (.imm 256) small)
    li 8 255
    place small
    li 5 0                                              -- offset
    li 6 0                                              -- in boot-keyboard interface
    let top ← newLabel
    let done ← newLabel
    place top
    mov 1 5
    addi 1 2
    emit (.branch .geu 1 (.reg 8) done)
    emit (.memLoad 1 2 5 dataBuf)                       -- bLength
    emit (.branch .eq 2 (.imm 0) done)
    emit (.memLoad 1 3 5 (dataBuf + 1))                 -- bDescriptorType
    let notIface ← newLabel
    emit (.branch .ne 3 (.imm 4) notIface)
    li 6 0
    emit (.memLoad 1 4 5 (dataBuf + 5))
    let advance ← newLabel
    emit (.branch .ne 4 (.imm 3) advance)
    emit (.memLoad 1 4 5 (dataBuf + 6))
    emit (.branch .ne 4 (.imm 1) advance)
    emit (.memLoad 1 4 5 (dataBuf + 7))
    emit (.branch .ne 4 (.imm 1) advance)
    li 6 1
    emit (.memLoad 1 4 5 (dataBuf + 2))
    st 4 V.iface (.reg 4)
    print Tag.iface 4
    emit (.jump advance)
    place notIface
    emit (.branch .ne 3 (.imm 5) advance)
    emit (.branch .eq 6 (.imm 0) advance)
    emit (.memLoad 1 4 5 (dataBuf + 2))                 -- bEndpointAddress
    mov 7 4
    andi 7 0x80
    emit (.branch .eq 7 (.imm 0) advance)
    emit (.memLoad 1 7 5 (dataBuf + 3))
    andi 7 3
    emit (.branch .ne 7 (.imm 3) advance)
    st 4 V.epAddr (.reg 4)
    emit (.memLoad 2 7 5 (dataBuf + 4))
    andi 7 0x7FF
    st 4 V.epMps (.reg 7)
    emit (.memLoad 1 7 5 (dataBuf + 6))
    st 4 V.epInterval (.reg 7)
    print Tag.endpoint 4
    emit (.jump done)
    place advance
    emit (.alu .add 5 (.reg 2))
    emit (.jump top)
    place done

/-! ## Keyboard setup and session -/

/-- SET_CONFIGURATION, Configure Endpoint for the interrupt IN endpoint,
SET_PROTOCOL(boot), SET_IDLE(0), then an LED sweep. -/
def setupKeyboard (idle : UInt32 := 0) : ProgM Unit := do
  ld 4 1 V.cfgValue
  shli 1 16
  ori 1 ((9 : UInt32) <<< 8)
  control 1 V.kbdSlot (.reg 1) (.imm 0) 0 false
  -- DCI = 2 × endpoint number + 1 (IN)
  ld 4 1 V.epAddr
  andi 1 0xF
  shli 1 1
  addi 1 1
  st 4 V.dci (.reg 1)
  -- interval exponent: floor(log2(bInterval × 8)) for LS/FS (125 µs units);
  -- for HS the endpoint already encodes 2^(bInterval-1) microframes.
  ld 4 2 V.epInterval
  ld 4 3 V.kbdSpeed
  let hsInt ← newLabel
  let haveInt ← newLabel
  emit (.branch .eq 3 (.imm 3) hsInt)
  shli 2 3
  li 4 0
  let lg ← newLabel
  place lg
  emit (.branch .ltu 2 (.imm 2) haveInt)
  shri 2 1
  addi 4 1
  emit (.jump lg)
  place hsInt
  mov 4 2
  emit (.alu .sub 4 (.imm 1))
  place haveInt
  st 4 V.epInterval (.reg 4)
  -- input context: add A0 | A(dci); slot context entries = dci
  clearInput
  ld 4 1 V.dci
  li 2 1
  emit (.alu .shl 2 (.reg 1))
  ori 2 1
  st 4 (ictx 0 1) (.reg 2)
  ld 4 2 V.kbdRoute
  ld 4 3 V.kbdSpeed
  shli 3 20
  emit (.alu .or 2 (.reg 3))
  mov 3 1
  shli 3 27
  emit (.alu .or 2 (.reg 3))
  st 4 (ictx 1 0) (.reg 2)
  ld 4 2 V.rootPort
  shli 2 16
  st 4 (ictx 1 1) (.reg 2)
  ld 4 2 V.kbdTt
  st 4 (ictx 1 2) (.reg 2)
  -- endpoint context at input context index dci + 1
  addi 1 1
  shli 1 5                                     -- × 32
  ld 4 2 V.epInterval
  shli 2 16
  emit (.memStore 4 1 inputCtx (.reg 2))
  ld 4 2 V.epMps
  mov 3 2
  shli 2 16
  ori 2 (((3 : UInt32) <<< 1) ||| ((7 : UInt32) <<< 3))              -- CErr 3, Interrupt IN
  emit (.memStore 4 1 (inputCtx + 4) (.reg 2))
  emit (.physAddr 2 intRing)
  ori 2 1
  emit (.memStore 4 1 (inputCtx + 8) (.reg 2))
  emit (.memStore 4 1 (inputCtx + 12) (.imm 0))
  shli 3 16
  ori 3 8                                      -- avg TRB length 8, max ESIT = MPS
  emit (.memStore 4 1 (inputCtx + 16) (.reg 3))
  ringInit (transferRing 5 intRing)
  ld 4 7 V.kbdSlot
  shli 7 24
  ori 7 ((12 : UInt32) <<< 10)
  emit (.physAddr 6 inputCtx)
  command (.reg 6) (.reg 7)
  printImm Tag.configured 0
  -- HID boot protocol, no idle repeat
  ld 4 1 V.iface
  control 1 V.kbdSlot (.imm ((0x21 : UInt32) ||| ((0x0B : UInt32) <<< 8))) (.reg 1) 0 false
  ld 4 1 V.iface
  -- SET_IDLE: duration in 4 ms units (0 = report only on change)
  control 1 V.kbdSlot (.imm ((0x21 : UInt32) ||| ((0x0A : UInt32) <<< 8) ||| ((idle <<< 8) <<< 16))) (.reg 1) 0 false
  -- LED sweep: Num, Caps, Scroll, all, off (SET_REPORT output, 1 byte)
  for leds in ([1, 2, 4, 7, 0] : List UInt32) do
    st 1 dataBuf (.imm leds)
    ld 4 1 V.iface
    ori 1 ((1 : UInt32) <<< 16)
    control 1 V.kbdSlot (.imm ((0x21 : UInt32) ||| ((0x09 : UInt32) <<< 8) ||| ((0x0200 : UInt32) <<< 16))) (.reg 1) 1 false
    printImm Tag.leds leds
    delay 250000

/-- Queue one interrupt IN transfer into `reportBuf` and ring the doorbell. -/
def armReport : ProgM Unit := do
  emit (.physAddr 6 reportBuf)
  ld 4 7 V.epMps
  enqueue (transferRing 5 intRing) (.reg 6) (.imm 0) (.reg 7)
    (.imm (((1 : UInt32) <<< 10) ||| 0x20 ||| 0x4))       -- Normal, IOC, ISP
  ld 4 1 V.kbdSlot
  shli 1 2
  ld 4 2 V.dci
  emit (.write32At 1 (doorbell 0) (.reg 2))

/-- Report `reportBuf` against `prevReport`: every newly pressed usage in
bytes 2–7 becomes one character (tag 0x2100). -/
def decodeReport (tableOff : UInt32) (yieldKeys : Bool := false) : ProgM Unit := do
  ld 1 8 reportBuf                              -- modifiers
  andi 8 0x22                                   -- either Shift
  for i in [2:8] do
    let skip ← newLabel
    ld 1 1 (reportBuf + i.toUInt32)
    emit (.branch .ltu 1 (.imm 4) skip)
    emit (.branch .geu 1 (.imm 64) skip)
    for j in [2:8] do
      ld 1 2 (prevReport + j.toUInt32)
      emit (.branch .eq 1 (.reg 2) skip)
    mov 3 1
    let noShift ← newLabel
    emit (.branch .eq 8 (.imm 0) noShift)
    addi 3 64
    place noShift
    emit (.blobLoad32 4 3 tableOff)
    emit (.branch .eq 4 (.imm 0) skip)
    -- Hand the key to the invoking subject (device service), or print it.
    if yieldKeys then emit (.yield (.reg 4)) else print Tag.key 4
    ld 4 5 V.keys
    addi 5 1
    st 4 V.keys (.reg 5)
    place skip
  for i in [0:8] do
    ld 1 1 (reportBuf + i.toUInt32)
    st 1 (prevReport + i.toUInt32) (.reg 1)

/-- Echo keys for `seconds` of controller time (MFINDEX, 125 µs units). -/
def session (seconds : UInt32) (tableOff : UInt32) (yieldKeys : Bool := false) : ProgM Unit := do
  st 4 V.elapsed (.imm 0)
  st 4 V.keys (.imm 0)
  st 4 V.reports (.imm 0)
  r32 1 mfindex
  andi 1 0x3FFF
  st 4 V.lastMf (.reg 1)
  ld 4 1 V.ids
  print Tag.ready 1
  armReport
  let top ← newLabel
  let out ← newLabel
  place top
  -- elapsed += (MFINDEX - last) mod 2^14
  r32 1 mfindex
  andi 1 0x3FFF
  ld 4 2 V.lastMf
  st 4 V.lastMf (.reg 1)
  emit (.alu .sub 1 (.reg 2))
  andi 1 0x3FFF
  ld 4 2 V.elapsed
  emit (.alu .add 2 (.reg 1))
  st 4 V.elapsed (.reg 2)
  emit (.branch .geu 2 (.imm (seconds * 8000)) out)
  nextEvent 100
  emit (.branch .ne 0 (.imm 32) top)
  -- transfer event on our slot and endpoint?
  ld 4 1 Var.ev3
  shri 1 24
  ld 4 2 V.kbdSlot
  emit (.branch .ne 1 (.reg 2) top)
  ld 4 1 Var.ev2
  shri 1 24
  let good ← newLabel
  emit (.branch .eq 1 (.imm 1) good)
  emit (.branch .eq 1 (.imm 13) good)
  print Tag.report 1
  armReport
  emit (.jump top)
  place good
  ld 4 1 V.reports
  addi 1 1
  st 4 V.reports (.reg 1)
  decodeReport tableOff yieldKeys
  armReport
  emit (.jump top)
  place out
  ld 4 1 V.reports
  print Tag.reports 1
  ld 4 1 V.keys
  print Tag.sessionEnd 1

/-- The complete keyboard program: controller bring-up, enumeration through
at most one hub, keyboard setup, and a `seconds`-long echo session. With
`yieldKeys` each typed character is handed to the invoking subject by
`yield` (the device-service form, ADR 0022) instead of being printed. -/
def program (seconds : UInt32) (idle : UInt32 := 0) (yieldKeys : Bool := false) : ProgM Unit := do
  let tableOff ← addBlob "hid-us-ascii" tableBytes
  bringUp
  let hubFound ← newLabel
  let kbdFound ← newLabel
  findHub hubFound
  fail Fail.noKeyboard
  place hubFound
  setupHub
  findKeyboardOnHub kbdFound
  fail Fail.noKeyboard
  place kbdFound
  setupKeyboard idle
  session seconds tableOff yieldKeys
  halt

end LeanOS.Usb.Keyboard
