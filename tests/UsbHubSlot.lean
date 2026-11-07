import LeanOS.Usb.Hid
import LeanOS.Wifi.Sim

/-! Simulated check of the hub enumeration's slot-context fields
(`LeanOS/Usb/Hid.lean`, `docs/usb-hub.md`), the parts QEMU cannot reach: its
`usb-hub` is a full-speed hub, so the transaction-translator fields of a
full- or low-speed device behind a high-speed hub and a high-speed hub's TT
think time never occur there. Each case stores the inputs in scratch, runs
the program's own fragment (`hubPortSpeed`, `hubTtFields`, `hubSlotContext`,
`hubDescriptorLimits`) in the simulator and prints what it computed, which
must equal the xHCI 1.1 §6.2.2 and USB 2.0 §11.23–§11.24 values written out
here. -/

open LeanOS.Wifi.Bytecode LeanOS.Wifi LeanOS.Usb.Xhci LeanOS.Usb.Hid

attribute [local instance] LeanOS.Usb.Xhci.qemu

/-- wPortStatus | wPortChange << 16 of a connected, enabled, powered port
(USB 2.0 Table 11-21), and the speed `hubPortSpeed` must decode. -/
def speedCases : List (UInt32 × UInt32) :=
  [(0x00000103, Speed.full),
   (0x00000303, Speed.low),
   (0x00000503, Speed.high),
   (0x00100503, Speed.high),          -- C_PORT_RESET still set
   (0x00110303, Speed.low)]           -- C_PORT_RESET and C_PORT_CONNECTION

/-- (hub speed, device speed, hub slot, hub port) and the TT word of slot
dword 2: TT Hub Slot ID | TT Port Number << 8 only for a full- or
low-speed device behind a high-speed hub. -/
def ttCases : List ((UInt32 × UInt32 × UInt32 × UInt32) × UInt32) :=
  [((Speed.high, Speed.full, 3, 7), 0x0703),
   ((Speed.high, Speed.low, 3, 7), 0x0703),
   ((Speed.high, Speed.high, 3, 7), 0),
   ((Speed.full, Speed.full, 3, 7), 0),   -- QEMU's usb-hub
   ((Speed.full, Speed.low, 3, 7), 0),
   -- the Qotom's Genesys 05e3:0610 high-speed hub in slot 1 with its
   -- low-speed keyboard on port 3 (hardware/lab/observations/qotom-usb-keyboard-20260927)
   ((Speed.high, Speed.low, 1, 3), 0x0301),
   ((Speed.high, Speed.full, 2, 15), 0x0F02)]

/-- (hub speed, root port, bNbrPorts, wHubCharacteristics) and the hub's
slot dwords 0–2: speed << 20 | Hub (bit 26) | one context entry << 27; root
port << 16 | Number of Ports << 24; TT think time << 16 (bits 5–6 of
wHubCharacteristics) for a high-speed hub, else 0. -/
def slotCases : List ((UInt32 × UInt32 × UInt32 × UInt32) × (UInt32 × UInt32 × UInt32)) :=
  [((Speed.high, 4, 4, 0x00E0), (0x0C300000, 0x04040000, 0x30000)),
   ((Speed.high, 5, 7, 0x0049), (0x0C300000, 0x07050000, 0x20000)),
   ((Speed.high, 1, 4, 0x0009), (0x0C300000, 0x04010000, 0)),
   ((Speed.full, 5, 8, 0x0069), (0x0C100000, 0x08050000, 0))]   -- TTT bits reserved

/-- (bNbrPorts, bPwrOn2PwrGood) and (`V.hubPorts`, `V.hubScanPorts`,
`V.hubWait`): ports searched capped at 15, the wait at least 50 × 2 ms. -/
def limitCases : List ((UInt32 × UInt32) × (UInt32 × UInt32 × UInt32)) :=
  [((4, 50), (4, 4, 50)),
   ((8, 1), (8, 8, 50)),              -- QEMU's usb-hub
   ((7, 0), (7, 7, 50)),
   ((15, 100), (15, 15, 100)),
   ((16, 255), (16, 15, 255)),
   ((255, 49), (255, 15, 50))]

def tagSpeed : UInt32 := 0x2F00
def tagTt : UInt32 := 0x2F01
def tagSlot : UInt32 := 0x2F02
def tagLimit : UInt32 := 0x2F03

def expected : List (UInt32 × UInt32) :=
  speedCases.map (fun (_, v) => (tagSpeed, v)) ++
  ttCases.map (fun (_, v) => (tagTt, v)) ++
  slotCases.flatMap (fun (_, (a, b, c)) => [(tagSlot, a), (tagSlot, b), (tagSlot, c)]) ++
  limitCases.flatMap (fun (_, (a, b, c)) => [(tagLimit, a), (tagLimit, b), (tagLimit, c)])

def prog : ProgM Unit := do
  for (status, _) in speedCases do
    st 4 V.portStatus (.imm status)
    hubPortSpeed
    ld 4 1 V.hidSpeed
    print tagSpeed 1
  for ((hubSpeed, devSpeed, slot, port), _) in ttCases do
    st 4 V.hubSpeed (.imm hubSpeed)
    st 4 V.hidSpeed (.imm devSpeed)
    st 4 V.hubSlot (.imm slot)
    st 4 V.hubPort (.imm port)
    hubTtFields
    ld 4 1 V.hidTt
    print tagTt 1
  for ((hubSpeed, rootPort, ports, chars), _) in slotCases do
    clearInput
    st 4 V.hubSpeed (.imm hubSpeed)
    st 4 V.rootPort (.imm rootPort)
    st 4 V.hubPorts (.imm ports)
    st 2 (dataBuf + 3) (.imm chars)
    hubSlotContext
    for dw in [0:3] do
      ld 4 1 (ictx 1 dw.toUInt32)
      print tagSlot 1
  for ((ports, pgood), _) in limitCases do
    st 1 (dataBuf + 2) (.imm ports)
    st 1 (dataBuf + 5) (.imm pgood)
    hubDescriptorLimits
    ld 4 1 V.hubPorts
    print tagLimit 1
    ld 4 1 V.hubScanPorts
    print tagLimit 1
    ld 4 1 V.hubWait
    print tagLimit 1
  halt

def main : IO UInt32 := do
  match build prog with
  | .error e => IO.eprintln e; return 1
  | .ok p =>
    let (st, m) := Sim.run p Sim.Device.none ()
    let got := m.prints.toList
    IO.println s!"status {repr st}, {got.length} records"
    let ok := st == .halt && got == expected
    IO.println (if ok then "PASS usb hub port speed, TT fields, hub slot context and descriptor limits"
                else s!"FAIL got {repr got}, expected {repr expected}")
    return if ok then 0 else 1
