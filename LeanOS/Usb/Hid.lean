import LeanOS.Usb.Xhci

/-
Boot-protocol HID devices on the xHCI driver, shared by the keyboard
(`LeanOS/Usb/Keyboard.lean`) and the mouse (`LeanOS/Usb/Mouse.lean`): find a
device with a HID boot interface of a given protocol (directly on a root port
or behind one USB 2.0 hub), configure it for the boot protocol, and poll its
interrupt IN endpoint for a bounded session, handing each report to the
device class's decoder. The mass-storage program (`LeanOS/Usb/MassStorage.lean`)
reuses the enumeration (`attachWith`) and the configuration-descriptor walk
(`findInterface`) with its own interface match and bulk endpoints.

The hub support (`findHub`, `setupHub`, `findOnHub`; `docs/usb-hub.md`)
handles one hub level: root port, then a USB 2.0 hub, then the device.

USB 2.0 chapter 9/11 requests (§11.24 hub class requests, §7.1.7.3 connect
debounce), xHCI 1.1 §6.2.2 (slot context: route string, hub and TT fields)
and HID 1.11 (§7.2 class requests, appendix B boot interfaces).
-/
namespace LeanOS.Usb.Hid

open LeanOS.Wifi.Bytecode LeanOS.Usb.Xhci

variable [Layout]

-- HID boot interface protocols (bInterfaceProtocol of an interface of class
-- 3, subclass 1).
namespace Protocol
def keyboard : UInt32 := 1
def mouse : UInt32 := 2
end Protocol

/-! ## State (scratch words after the xHCI driver's) -/

namespace V
def devSlot : UInt32 := vars + 0x100     -- slot of the device being probed
def rootPort : UInt32 := vars + 0x104
def hubSlot : UInt32 := vars + 0x108
def hubPorts : UInt32 := vars + 0x10C
def hidSlot : UInt32 := vars + 0x110      -- the accepted HID device
def hidRoute : UInt32 := vars + 0x114
def hidSpeed : UInt32 := vars + 0x118
def hidTt : UInt32 := vars + 0x11C
def iface : UInt32 := vars + 0x120
def epAddr : UInt32 := vars + 0x124
def epMps : UInt32 := vars + 0x128
def epInterval : UInt32 := vars + 0x12C
def cfgValue : UInt32 := vars + 0x130
def dci : UInt32 := vars + 0x134
def ids : UInt32 := vars + 0x138
def elapsed : UInt32 := vars + 0x13C
def lastMf : UInt32 := vars + 0x140
/-- Records the session handed on (keys, mouse records). -/
def records : UInt32 := vars + 0x144
def portStatus : UInt32 := vars + 0x148
/-- wIndex of the next hub port request (`hubPortGetStatus`,
`hubPortFeature`); `findOnRoot` keeps the hub's root port here. -/
def hubPortNo : UInt32 := vars + 0x14C
def tries : UInt32 := vars + 0x150
def reports : UInt32 := vars + 0x154
/-- Speed of the hub (PORTSC speed of its root port, `Speed`). -/
def hubSpeed : UInt32 := vars + 0x158
/-- The hub port being powered or searched (1-based). -/
def hubPort : UInt32 := vars + 0x15C
/-- Hub ports powered and searched: bNbrPorts, at most `maxHubPorts`. -/
def hubScanPorts : UInt32 := vars + 0x160
/-- Power-on wait left, in 2 ms units. -/
def hubWait : UInt32 := vars + 0x164
/-- Consecutive connected reads of a hub port in the debounce. -/
def stable : UInt32 := vars + 0x168
end V

/- PORTSC port speed IDs (the default speed ID mapping of xHCI 1.1 §7.2,
Supported Protocol capability), also used for the speed decoded from a hub's
wPortStatus. -/
namespace Speed
def full : UInt32 := 1
def low : UInt32 := 2
def high : UInt32 := 3
def super : UInt32 := 4
end Speed

/-- Hub ports searched at most: a route string tier holds port numbers 1–15
(four bits per tier, xHCI 1.1 §6.2.2). -/
def maxHubPorts : UInt32 := 15

/-- The shortest power-on wait, in 2 ms units: 250 ms, the fixed wait the
earlier driver used after PORT_POWER, which the Qotom's Genesys 05e3:0610
hub ran with (`hardware/lab/observations/qotom-usb-keyboard-20260927`). -/
def minHubWait : UInt32 := 125

-- Enumeration diagnostics. The 0x20xx tags print as raw records; the hub
-- records (0x24xx, `docs/usb-hub.md`) are rendered by the lab kernel's print
-- hook (`hardware/lab/qotom-wifi.c.inc`).
namespace Tag
/-- The hub: root port | speed << 8 | slot << 16. -/
def hubFound : UInt32 := 0x2400
/-- The hub configured: bNbrPorts | power-on wait in ms << 8 | TT think
time (wHubCharacteristics bits 5–6, high-speed hubs only) << 24. -/
def hubConfigured : UInt32 := 0x2401
/-- GET_PORT_STATUS: wPortStatus | (wPortChange & 0xFF) << 16 | port << 24. -/
def hubPortStatus : UInt32 := 0x2402
/-- A connected hub port given up: port | reason << 8 (`SkipReason`). -/
def hubPortSkipped : UInt32 := 0x2403
/-- A device behind the hub about to be addressed, its slot context fields:
route string | speed << 20 | root port << 24 (line continues), then slot
dword 2's TT word, TT hub slot | TT port << 8 (line ends). -/
def hubDevice : UInt32 := 0x2404
def hubDeviceTt : UInt32 := 0x2405
/-- A SuperSpeed root port passed over in the hub search: port | speed << 8. -/
def hubRootSkipped : UInt32 := 0x2406
def device : UInt32 := 0x2013
def iface : UInt32 := 0x2014
def endpoint : UInt32 := 0x2015
def configured : UInt32 := 0x2016
def report : UInt32 := 0x2018
/-- The device on this (hub or root) port has no boot interface of the
protocol sought; its slot is disabled again. -/
def rejected : UInt32 := 0x2019
/-- A control transfer queued during the session (`controlQueue`) completed:
its completion code. -/
def controlDone : UInt32 := 0x201A
end Tag

/-! ## Helpers -/

/- wPortStatus (bits 0–15) and wPortChange (bits 16–31) bits of a hub
port's GET_STATUS reply (USB 2.0 Tables 11-21 and 11-22). -/
namespace PortBit
def connection : UInt32 := 0x1
def enable : UInt32 := 0x2
def lowSpeed : UInt32 := 0x200
def highSpeed : UInt32 := 0x400
def cConnection : UInt32 := 0x10000
def cReset : UInt32 := 0x100000
end PortBit

/- Hub port feature selectors (USB 2.0 Table 11-17). -/
namespace Feature
def portReset : UInt32 := 4
def portPower : UInt32 := 8
def cPortConnection : UInt32 := 16
def cPortReset : UInt32 := 20
end Feature

/- Why a connected hub port was given up (`Tag.hubPortSkipped`). -/
namespace SkipReason
/-- The connection did not hold for 100 ms within 2 s. -/
def unstable : UInt32 := 1
/-- No C_PORT_RESET within 500 ms of SET_FEATURE(PORT_RESET). -/
def resetTimeout : UInt32 := 2
/-- The reset completed but the port is not enabled. -/
def notEnabled : UInt32 := 3
end SkipReason

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

/-- Print `V.portStatus` of hub port `V.hubPort` (`Tag.hubPortStatus`). -/
def printHubPortStatus : ProgM Unit := do
  ld 4 1 V.portStatus
  mov 2 1
  andi 1 0xFFFF
  shri 2 16
  andi 2 0xFF
  shli 2 16
  emit (.alu .or 1 (.reg 2))
  ld 4 2 V.hubPort
  shli 2 24
  emit (.alu .or 1 (.reg 2))
  print Tag.hubPortStatus 1

/-- Give up hub port `V.hubPort` for `reason` (`Tag.hubPortSkipped`). -/
def skipHubPort (reason : UInt32) : ProgM Unit := do
  ld 4 1 V.hubPort
  ori 1 (reason <<< 8)
  print Tag.hubPortSkipped 1

/-- The speed of the device on a hub port, from `V.portStatus` (wPortStatus
bit 9 low speed, bit 10 high speed, else full speed), to `V.hidSpeed`. -/
def hubPortSpeed : ProgM Unit := do
  ld 4 1 V.portStatus
  li 2 Speed.full
  mov 3 1
  andi 3 PortBit.lowSpeed
  let notLs ← newLabel
  emit (.branch .eq 3 (.imm 0) notLs)
  li 2 Speed.low
  place notLs
  mov 3 1
  andi 3 PortBit.highSpeed
  let notHs ← newLabel
  emit (.branch .eq 3 (.imm 0) notHs)
  li 2 Speed.high
  place notHs
  st 4 V.hidSpeed (.reg 2)

/-- The TT word of the slot context's dword 2 for the device on hub port
`V.hubPort`, to `V.hidTt` (xHCI 1.1 §6.2.2): TT Hub Slot ID `V.hubSlot` |
TT Port Number `V.hubPort` << 8 for a full- or low-speed device
(`V.hidSpeed`) behind a high-speed hub (`V.hubSpeed`), whose transaction
translator splits its transactions; 0 for a high-speed device and for any
device behind a full-speed hub. -/
def hubTtFields : ProgM Unit := do
  li 4 0
  let noTt ← newLabel
  let tt ← newLabel
  ld 4 1 V.hubSpeed
  emit (.branch .ne 1 (.imm Speed.high) noTt)
  ld 4 1 V.hidSpeed
  emit (.branch .eq 1 (.imm Speed.full) tt)
  emit (.branch .ne 1 (.imm Speed.low) noTt)
  place tt
  ld 4 4 V.hubSlot
  ld 4 1 V.hubPort
  shli 1 8
  emit (.alu .or 4 (.reg 1))
  place noTt
  st 4 V.hidTt (.reg 4)

/-- The hub's slot context in the input context, for the Configure Endpoint
command that makes its slot a hub (xHCI 1.1 §4.6.6 and §6.2.2): its speed
(`V.hubSpeed`), Hub = 1, one context entry, its root port, Number of Ports =
bNbrPorts (`V.hubPorts`), and for a high-speed hub the TT think time,
wHubCharacteristics bits 5–6 of the hub descriptor in `dataBuf` (reserved,
and left 0, for a full-speed hub). MTT stays 0: a multiple-TT hub runs one
TT until its alternate setting 1 is selected, which this driver never does. -/
def hubSlotContext : ProgM Unit := do
  ld 4 1 V.hubSpeed
  shli 1 20
  ori 1 (((1 : UInt32) <<< 26) ||| ((1 : UInt32) <<< 27))   -- Hub, 1 entry
  st 4 (ictx 1 0) (.reg 1)
  ld 4 1 V.rootPort
  shli 1 16
  ld 4 2 V.hubPorts
  shli 2 24
  emit (.alu .or 1 (.reg 2))
  st 4 (ictx 1 1) (.reg 1)
  li 1 0
  ld 4 2 V.hubSpeed
  let noTtt ← newLabel
  emit (.branch .ne 2 (.imm Speed.high) noTtt)
  ld 2 1 (dataBuf + 3)                                  -- wHubCharacteristics
  shri 1 5
  andi 1 3                                              -- TT think time
  shli 1 16
  place noTtt
  st 4 (ictx 1 2) (.reg 1)

/-- From the hub descriptor in `dataBuf`: bNbrPorts to `V.hubPorts`, the
ports to power and search (bNbrPorts, at most `maxHubPorts`) to
`V.hubScanPorts`, and the power-on wait in 2 ms units to `V.hubWait`:
bPwrOn2PwrGood (power good, USB 2.0 §11.23.2.1) + 50, the 100 ms a device
may take after its power is good to signal attach (TSIGATT, §7.1.7.3), at
least `minHubWait`. -/
def hubDescriptorLimits : ProgM Unit := do
  ld 1 1 (dataBuf + 2)                                  -- bNbrPorts
  st 4 V.hubPorts (.reg 1)
  let fits ← newLabel
  emit (.branch .ltu 1 (.imm (maxHubPorts + 1)) fits)
  li 1 maxHubPorts
  place fits
  st 4 V.hubScanPorts (.reg 1)
  ld 1 1 (dataBuf + 5)                                  -- bPwrOn2PwrGood
  addi 1 50                                             -- + TSIGATT
  let long ← newLabel
  emit (.branch .geu 1 (.imm minHubWait) long)
  li 1 minHubWait
  place long
  st 4 V.hubWait (.reg 1)

/-! ## Enumeration -/

/-- Probe root ports 1–6: address each connected device in driver context 0
and keep the first hub (`V.hubSlot`, `V.rootPort`, `V.hubSpeed`); other
devices' slots are disabled again. A SuperSpeed port is passed over without
addressing its device: a USB 2.0 hub is never there, while a USB 3 hub's
SuperSpeed half is, with a hub descriptor of type 0x2A and its own port
status layout. Jumps to `hubFound`, or falls through when no hub exists. -/
def findHub (hubFound : Nat) : ProgM Unit := do
  for p in [1:7] do
    let port := p.toUInt32
    let next ← newLabel
    resetRootPort port
    emit (.branch .eq 0 (.imm 0) next)
    -- speed from PORTSC bits 10–13
    shri 0 10
    andi 0 0xF
    let usb2 ← newLabel
    emit (.branch .ltu 0 (.imm Speed.super) usb2)
    shli 0 8
    ori 0 port
    print Tag.hubRootSkipped 0
    emit (.jump next)
    place usb2
    st 4 V.hubSpeed (.reg 0)
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
    shli 1 16
    ld 4 2 V.hubSpeed
    shli 2 8
    emit (.alu .or 1 (.reg 2))
    ori 1 port
    print Tag.hubFound 1
    emit (.jump hubFound)
    place notHub
    disableSlot V.devSlot
    place next

/-- Configure the hub in context 0: SET_CONFIGURATION(1), the hub descriptor
(`hubDescriptorLimits`), Configure Endpoint marking the slot as a hub
(`hubSlotContext`), SET_FEATURE(PORT_POWER) on ports 1 to `V.hubScanPorts`,
then the power-on wait. -/
def setupHub : ProgM Unit := do
  control 0 V.hubSlot (.imm ((0x00 : UInt32) ||| ((9 : UInt32) <<< 8) ||| ((1 : UInt32) <<< 16))) (.imm 0) 0 false
  hubReq (.imm ((0xA0 : UInt32) ||| ((6 : UInt32) <<< 8) ||| ((0x2900 : UInt32) <<< 16))) (.imm ((9 : UInt32) <<< 16)) 9 true
  hubDescriptorLimits
  -- Configure Endpoint (A0): the slot context with the hub fields
  clearInput
  st 4 (ictx 0 1) (.imm 0x1)
  hubSlotContext
  ld 4 7 V.hubSlot
  shli 7 24
  ori 7 ((12 : UInt32) <<< 10)
  emit (.physAddr 6 inputCtx)
  command (.reg 6) (.reg 7)
  -- bNbrPorts | wait in ms << 8 | TT think time << 24 (slot dword 2 bits 16–17)
  ld 4 1 V.hubPorts
  ld 4 2 V.hubWait
  shli 2 9
  emit (.alu .or 1 (.reg 2))
  ld 4 2 (ictx 1 2)
  shli 2 8
  emit (.alu .or 1 (.reg 2))
  print Tag.hubConfigured 1
  -- power ports 1 .. V.hubScanPorts
  st 4 V.hubPort (.imm 0)
  let power ← newLabel
  let powered ← newLabel
  place power
  ld 4 1 V.hubPort
  addi 1 1
  st 4 V.hubPort (.reg 1)
  ld 4 2 V.hubScanPorts
  emit (.branch .ltu 2 (.reg 1) powered)
  st 4 V.hubPortNo (.reg 1)
  hubPortFeature true Feature.portPower
  emit (.jump power)
  place powered
  let wait ← newLabel
  place wait
  delay 2000
  ld 4 1 V.hubWait
  emit (.alu .sub 1 (.imm 1))
  st 4 V.hubWait (.reg 1)
  emit (.branch .ne 1 (.imm 0) wait)

/-- Read the configuration descriptor (at most 255 bytes) of the device in
context 1 into `dataBuf`, record its bConfigurationValue (`V.cfgValue`) and
walk its descriptors. An interface descriptor of class `cls`, subclass
`subclass` and protocol `protocol` starts a matching interface: its number
goes to `V.iface`, it is printed (`Tag.iface`) and `onInterface` runs; any
other interface descriptor ends it. Each endpoint descriptor inside a
matching interface goes to `onEndpoint advance done` with r5 its offset in
`dataBuf` and r2 its bLength; the handler jumps to `advance` for the next
descriptor or to `done` to stop the walk, and must keep r2, r5, r6 and r8
(it may use r1, r3, r4, r7 and r9). Also used by the mass-storage program
(`LeanOS/Usb/MassStorage.lean`). -/
def findInterface (cls subclass protocol : UInt32) (onInterface : ProgM Unit)
    (onEndpoint : Nat → Nat → ProgM Unit) : ProgM Unit := do
  control 1 V.hidSlot (.imm ((0x80 : UInt32) ||| ((6 : UInt32) <<< 8) ||| ((0x0200 : UInt32) <<< 16))) (.imm ((255 : UInt32) <<< 16)) 255 true
  ld 1 1 (dataBuf + 5)
  st 4 V.cfgValue (.reg 1)
  ld 2 8 (dataBuf + 2)                                -- wTotalLength
  let small ← newLabel
  emit (.branch .ltu 8 (.imm 256) small)
  li 8 255
  place small
  li 5 0                                              -- offset
  li 6 0                                              -- in a matching interface
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
  emit (.branch .ne 4 (.imm cls) advance)             -- bInterfaceClass
  emit (.memLoad 1 4 5 (dataBuf + 6))
  emit (.branch .ne 4 (.imm subclass) advance)        -- bInterfaceSubClass
  emit (.memLoad 1 4 5 (dataBuf + 7))
  emit (.branch .ne 4 (.imm protocol) advance)        -- bInterfaceProtocol
  li 6 1
  emit (.memLoad 1 4 5 (dataBuf + 2))
  st 4 V.iface (.reg 4)
  print Tag.iface 4
  onInterface
  emit (.jump advance)
  place notIface
  emit (.branch .ne 3 (.imm 5) advance)
  emit (.branch .eq 6 (.imm 0) advance)
  onEndpoint advance done
  place advance
  emit (.alu .add 5 (.reg 2))
  emit (.jump top)
  place done

/-- Read the configuration descriptor of the device in context 1 and record
the first HID boot interface (class 3, subclass 1) of `protocol`, and its
interrupt IN endpoint (`V.epAddr` stays 0 if there is none). -/
def findBootInterface (protocol : UInt32) : ProgM Unit := do
  st 4 V.epAddr (.imm 0)
  findInterface 3 1 protocol (pure ()) fun advance done => do
    emit (.memLoad 1 4 5 (dataBuf + 2))               -- bEndpointAddress
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

/-- Accept a device with a HID boot interface of `protocol` (r1 ≠ 0 iff
accepted; the enumeration's `accept` contract). -/
def bootInterface (protocol : UInt32) : ProgM Unit := do
  findBootInterface protocol
  ld 4 1 V.epAddr

/-- Search hub ports 1 to `V.hubScanPorts` for a device (USB 2.0 §11.24.2.7,
§7.1.7.3 and §7.1.7.5). A port whose GET_STATUS shows no connection is
passed over. On a connected port the connection must then hold for four
reads 25 ms apart (100 ms; a connection change is cleared and restarts the
count), within 80 reads; then SET_FEATURE(PORT_RESET), GET_STATUS every 10
ms until C_PORT_RESET (at most 50 times), CLEAR_FEATURE(C_PORT_RESET), the
port must be enabled, and 20 ms of reset recovery. The device is addressed
in context 1 with the route string (the hub port, tier 1), its speed
(`hubPortSpeed`), the hub's root port and the TT fields (`hubTtFields`); its
device descriptor is read (idVendor | idProduct << 16 to `V.ids`) and
`accept` runs, which reads what else it needs and leaves r1 ≠ 0 to accept
the device (else its slot is disabled and the search goes on). Jumps to
`found`; falls through when none. -/
def findOnHub (accept : ProgM Unit) (found : Nat) : ProgM Unit := do
  st 4 V.hubPort (.imm 0)
  let next ← newLabel
  let done ← newLabel
  place next
  ld 4 1 V.hubPort
  addi 1 1
  st 4 V.hubPort (.reg 1)
  ld 4 2 V.hubScanPorts
  emit (.branch .ltu 2 (.reg 1) done)
  hubPortGetStatus 1
  printHubPortStatus
  ld 4 1 V.portStatus
  andi 1 PortBit.connection
  emit (.branch .eq 1 (.imm 0) next)
  -- debounce: four consecutive connected reads with no connection change
  st 4 V.stable (.imm 0)
  st 4 V.tries (.imm 80)
  let debounce ← newLabel
  let retry ← newLabel
  let steady ← newLabel
  place debounce
  delay 25000
  ld 4 1 V.hubPort
  hubPortGetStatus 1
  ld 4 1 V.portStatus
  mov 2 1
  andi 2 PortBit.cConnection
  let noChange ← newLabel
  emit (.branch .eq 2 (.imm 0) noChange)
  hubPortFeature false Feature.cPortConnection
  st 4 V.stable (.imm 0)
  emit (.jump retry)
  place noChange
  andi 1 PortBit.connection
  let up ← newLabel
  emit (.branch .ne 1 (.imm 0) up)
  st 4 V.stable (.imm 0)
  emit (.jump retry)
  place up
  ld 4 1 V.stable
  addi 1 1
  st 4 V.stable (.reg 1)
  emit (.branch .geu 1 (.imm 4) steady)
  place retry
  ld 4 1 V.tries
  emit (.alu .sub 1 (.imm 1))
  st 4 V.tries (.reg 1)
  emit (.branch .ne 1 (.imm 0) debounce)
  skipHubPort SkipReason.unstable
  emit (.jump next)
  place steady
  -- reset, then wait for C_PORT_RESET
  hubPortFeature true Feature.portReset
  st 4 V.tries (.imm 50)
  let wait ← newLabel
  let reset ← newLabel
  place wait
  delay 10000
  ld 4 1 V.hubPort
  hubPortGetStatus 1
  ld 4 1 V.portStatus
  andi 1 PortBit.cReset
  emit (.branch .ne 1 (.imm 0) reset)
  ld 4 1 V.tries
  emit (.alu .sub 1 (.imm 1))
  st 4 V.tries (.reg 1)
  emit (.branch .ne 1 (.imm 0) wait)
  skipHubPort SkipReason.resetTimeout
  emit (.jump next)
  place reset
  hubPortFeature false Feature.cPortReset
  ld 4 1 V.portStatus
  andi 1 PortBit.enable
  let enabled ← newLabel
  emit (.branch .ne 1 (.imm 0) enabled)
  skipHubPort SkipReason.notEnabled
  emit (.jump next)
  place enabled
  delay 20000                                         -- reset recovery
  printHubPortStatus
  -- slot context: route string (tier 1 = the hub port), speed, TT
  hubPortSpeed
  ld 4 1 V.hubPort
  st 4 V.hidRoute (.reg 1)
  hubTtFields
  ld 4 1 V.hidRoute
  ld 4 2 V.hidSpeed
  shli 2 20
  emit (.alu .or 1 (.reg 2))
  ld 4 2 V.rootPort
  shli 2 24
  emit (.alu .or 1 (.reg 2))
  print Tag.hubDevice 1
  ld 4 1 V.hidTt
  print Tag.hubDeviceTt 1
  ld 4 1 V.hidRoute
  ld 4 2 V.hidSpeed
  ld 4 3 V.rootPort
  ld 4 4 V.hidTt
  enableAndAddress 1 V.hidSlot 1 2 3 4
  getDeviceDescriptor 1 V.hidSlot
  ld 4 1 (dataBuf + 8)
  st 4 V.ids (.reg 1)
  accept
  emit (.branch .ne 1 (.imm 0) found)
  ld 4 1 V.hubPort
  print Tag.rejected 1
  disableSlot V.hidSlot
  emit (.jump next)
  place done

/-- Probe root ports 1–6 for a device attached directly (no hub, no
transaction translator): address each connected non-hub device in context 1
and accept the first for which `accept` leaves r1 ≠ 0 (as in `findOnHub`).
The port of an already configured hub (`V.hubSlot` ≠ 0, at `V.rootPort`) is
left alone. Jumps to `found`; falls through when none. -/
def findOnRoot (accept : ProgM Unit) (found : Nat) : ProgM Unit := do
  ld 4 1 V.hubSlot
  st 4 V.hubPortNo (.imm 0)
  let noHub ← newLabel
  emit (.branch .eq 1 (.imm 0) noHub)
  ld 4 1 V.rootPort
  st 4 V.hubPortNo (.reg 1)                          -- hub's root port to skip
  place noHub
  for p in [1:7] do
    let port := p.toUInt32
    let next ← newLabel
    ld 4 1 V.hubPortNo
    emit (.branch .eq 1 (.imm port) next)
    resetRootPort port
    emit (.branch .eq 0 (.imm 0) next)
    shri 0 10                                        -- PORTSC speed (1 FS, 2 LS, 3 HS)
    andi 0 0xF
    mov 2 0
    st 4 V.hidSpeed (.reg 2)
    st 4 V.hidRoute (.imm 0)
    st 4 V.hidTt (.imm 0)
    st 4 V.rootPort (.imm port)
    li 1 0                                           -- route string
    li 3 port
    li 4 0                                           -- no TT
    enableAndAddress 1 V.hidSlot 1 2 3 4
    getDeviceDescriptor 1 V.hidSlot
    ld 1 1 (dataBuf + 4)                             -- bDeviceClass
    print Tag.device 1
    let notMatching ← newLabel
    emit (.branch .eq 1 (.imm 9) notMatching)
    ld 4 1 (dataBuf + 8)
    st 4 V.ids (.reg 1)
    accept
    emit (.branch .ne 1 (.imm 0) found)
    place notMatching
    printImm Tag.rejected port
    disableSlot V.hidSlot
    place next

/-- Controller bring-up, then enumeration through at most one hub or directly
on a root port, for a device that `accept` takes (see `findOnHub`); runs
`missing`, which must not fall through, when there is none. The device is
left addressed in context 1 (`V.hidSlot`, `V.hidRoute`, `V.hidSpeed`,
`V.hidTt`, `V.rootPort`), with what `accept` recorded. -/
def attachWith (accept : ProgM Unit) (missing : ProgM Unit) : ProgM Unit := do
  bringUp
  let hubFound ← newLabel
  let found ← newLabel
  let rootSearch ← newLabel
  findHub hubFound
  emit (.jump rootSearch)
  place hubFound
  setupHub
  findOnHub accept found
  -- no matching device behind the hub (or no hub): one plugged straight
  -- into a root port
  place rootSearch
  findOnRoot accept found
  missing
  place found

/-- `attachWith` for a device with a boot interface of `protocol`; fails with
`missing` when there is none. Its interface and interrupt IN endpoint are
recorded (`V.iface`, `V.epAddr`, `V.epMps`, `V.epInterval`). -/
def attach (protocol : UInt32) (missing : UInt32) : ProgM Unit :=
  attachWith (bootInterface protocol) (fail missing)

/-! ## Device setup and session -/

/-- SET_CONFIGURATION, Configure Endpoint for the interrupt IN endpoint,
SET_PROTOCOL(boot), SET_IDLE(`idle`, in 4 ms units; 0 = report only on
change). -/
def setupInterface (idle : UInt32 := 0) : ProgM Unit := do
  ld 4 1 V.cfgValue
  shli 1 16
  ori 1 ((9 : UInt32) <<< 8)
  control 1 V.hidSlot (.reg 1) (.imm 0) 0 false
  -- DCI = 2 × endpoint number + 1 (IN)
  ld 4 1 V.epAddr
  andi 1 0xF
  shli 1 1
  addi 1 1
  st 4 V.dci (.reg 1)
  -- interval exponent: floor(log2(bInterval × 8)) for LS/FS (125 µs units);
  -- for HS the endpoint already encodes 2^(bInterval-1) microframes.
  ld 4 2 V.epInterval
  ld 4 3 V.hidSpeed
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
  ld 4 2 V.hidRoute
  ld 4 3 V.hidSpeed
  shli 3 20
  emit (.alu .or 2 (.reg 3))
  mov 3 1
  shli 3 27
  emit (.alu .or 2 (.reg 3))
  st 4 (ictx 1 0) (.reg 2)
  ld 4 2 V.rootPort
  shli 2 16
  st 4 (ictx 1 1) (.reg 2)
  ld 4 2 V.hidTt
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
  ld 4 7 V.hidSlot
  shli 7 24
  ori 7 ((12 : UInt32) <<< 10)
  emit (.physAddr 6 inputCtx)
  command (.reg 6) (.reg 7)
  printImm Tag.configured 0
  -- HID boot protocol
  ld 4 1 V.iface
  control 1 V.hidSlot (.imm ((0x21 : UInt32) ||| ((0x0B : UInt32) <<< 8))) (.reg 1) 0 false
  ld 4 1 V.iface
  -- SET_IDLE: duration in 4 ms units (0 = report only on change)
  control 1 V.hidSlot (.imm ((0x21 : UInt32) ||| ((0x0A : UInt32) <<< 8) ||| ((idle <<< 8) <<< 16))) (.reg 1) 0 false

/-- Queue one interrupt IN transfer into `reportBuf` and ring the doorbell. -/
def armReport : ProgM Unit := do
  emit (.physAddr 6 reportBuf)
  ld 4 7 V.epMps
  enqueue (transferRing 5 intRing) (.reg 6) (.imm 0) (.reg 7)
    (.imm (((1 : UInt32) <<< 10) ||| 0x20 ||| 0x4))       -- Normal, IOC, ISP
  ld 4 1 V.hidSlot
  shli 1 2
  ld 4 2 V.dci
  emit (.write32At 1 (doorbell 0) (.reg 2))

/-- The session records of a device class. -/
structure Records where
  /-- Before the first report: idVendor | idProduct << 16. -/
  ready : UInt32
  /-- At the end: the reports received. -/
  reports : UInt32
  /-- At the end: the records handed on (`V.records`). -/
  sessionEnd : UInt32

/-- Poll the device for `seconds` of controller time (MFINDEX, 125 µs units):
each report the interrupt endpoint completes (Success or Short Packet; the
transfer event stays in `Var.ev0..ev3`) goes to `onReport`, which counts what
it hands on in `V.records`, and the transfer is queued again. A completed
control transfer that `onReport` queued (EP0, `controlQueue`) prints
`Tag.controlDone` with its completion code; other endpoints' events are
ignored. -/
def session (seconds : UInt32) (records : Records) (onReport : ProgM Unit) : ProgM Unit := do
  st 4 V.elapsed (.imm 0)
  st 4 V.records (.imm 0)
  st 4 V.reports (.imm 0)
  r32 1 mfindex
  andi 1 0x3FFF
  st 4 V.lastMf (.reg 1)
  ld 4 1 V.ids
  print records.ready 1
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
  ld 4 2 V.hidSlot
  emit (.branch .ne 1 (.reg 2) top)
  -- on our interrupt endpoint? EP0 (endpoint id 1) completes queued control
  -- transfers
  ld 4 1 Var.ev3
  shri 1 16
  andi 1 0x1F
  let ours ← newLabel
  ld 4 2 V.dci
  emit (.branch .eq 1 (.reg 2) ours)
  emit (.branch .ne 1 (.imm 1) top)
  ld 4 1 Var.ev2
  shri 1 24
  print Tag.controlDone 1
  emit (.jump top)
  place ours
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
  onReport
  armReport
  emit (.jump top)
  place out
  ld 4 1 V.reports
  print records.reports 1
  ld 4 1 V.records
  print records.sessionEnd 1

end LeanOS.Usb.Hid
