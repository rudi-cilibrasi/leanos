import LeanOS.Net.DhcpSource
import LeanOS.Net.DhcpClient

/-!
Hosted vectors for the DHCP subject's client (issue #556).

1. The model reading of the hook-generic client, `DhcpClient.stepRecord`,
   must send exactly the frames the frame source expects on its own records
   (`DhcpSource.dhcpRecords`, built from the reference `LeanOS.Wifi.Dhcp`),
   end bound to the leased address, and agree with the reference client
   `LeanOS.Wifi.Dhcp.Client.handle` on every frame from both waiting states
   (`selecting` and `requesting`): the server's OFFER, ACK and NAK, replies
   for another transaction, another hardware address and another server,
   each with single-byte corruptions of every byte and truncations.
2. It then prints vectors for the differential test of the generated C
   (`scripts/check-dhcp-subject-host.sh`): the registers before, the record,
   the frame the model sends (`-` for none) and the registers after.

usage: leanos-net-dhcp-vectors OUT
-/

open LeanOS.Net LeanOS.Net.FrameSource LeanOS.Net.DhcpSource

def hex (b : ByteArray) : String :=
  String.join (b.toList.map fun x =>
    let s := String.ofList (Nat.toDigits 16 x.toNat)
    if s.length == 1 then "0" ++ s else s)

def regsHex (r : Array UInt64) : String :=
  ",".intercalate (r.toList.map fun x => String.ofList (Nat.toDigits 16 x.toNat))

/-- The registers of a client waiting in `selecting` for transaction `xid`. -/
def selecting (xid : UInt32) : Array UInt64 :=
  (DhcpClient.initialRegs.set! 0 1 |>.set! 1 xid.toUInt64 |>.set! 2 mac)

/-- The registers of a client waiting in `requesting` for the offer of
`offered` by `server`. -/
def requesting (xid offered server : UInt32) : Array UInt64 :=
  (selecting xid |>.set! 0 2 |>.set! 3 offered.toUInt64 |>.set! 4 server.toUInt64)

/-- The reference client in the state the registers describe. -/
def refClient (r : Array UInt64) : LeanOS.Wifi.Dhcp.Client :=
  let xid := (r.getD 1 0).toUInt32
  let offer : LeanOS.Wifi.Dhcp.Lease :=
    { address := (r.getD 3 0).toUInt32, serverId := (r.getD 4 0).toUInt32,
      subnetMask := none, router := none, dns := [], leaseSeconds := none }
  let state := if r.getD 0 0 == 2 then LeanOS.Wifi.Dhcp.State.requesting xid offer
    else LeanOS.Wifi.Dhcp.State.selecting xid
  { mac := macArray, state }

/-- What the reference client's state says the registers 0, 1, 3, 4, 5 are
(the phase, the transaction, the offer, its server, the lease). -/
def refRegs (c : LeanOS.Wifi.Dhcp.Client) (before : Array UInt64) : List UInt64 :=
  match c.state with
  | .selecting xid => [1, xid.toUInt64, before.getD 3 0, before.getD 4 0, before.getD 5 0]
  | .requesting xid o => [2, xid.toUInt64, o.address.toUInt64, o.serverId.toUInt64,
      before.getD 5 0]
  | .bound l => [3, before.getD 1 0, before.getD 3 0, before.getD 4 0, l.address.toUInt64]

def modelRegs (r : Array UInt64) : List UInt64 :=
  [r.getD 0 0, r.getD 1 0, r.getD 3 0, r.getD 4 0, r.getD 5 0]

/-- The reference on an Ethernet frame: the IPv4 datagram after an IPv4
ethertype, the reply in our Ethernet header. -/
def refFrame (r : Array UInt64) (f : ByteArray) : List UInt64 × Option ByteArray :=
  let isIp := f.size ≥ 14 && f[12]! == 0x08 && f[13]! == 0x00
  if !isIp then (modelRegs r, none) else
  let (c, out) := (refClient r).handle (f.extract 14 f.size)
  (refRegs c r, out.map toEthernet)

def main (args : List String) : IO UInt32 := do
  let [out] := args | do IO.eprintln "usage: leanos-net-dhcp-vectors OUT"; return 2
  let mut lines : Array String := #[]
  let mut ok := true
  -- 1. The frame source's own records, in order.
  let mut regs := DhcpClient.initialRegs
  for (k, f, want) in (List.range dhcpRecords.length).zip dhcpRecords do
    let (regs', got) := DhcpClient.stepRecord regs f
    if got.map (·.toList) != want.map (·.toList) then
      IO.eprintln s!"error: record {k + 1}: model sent {got.map hex}, reference {want.map hex}"
      ok := false
    lines := lines.push s!"{regsHex regs} {hex f} {(got.map hex).getD "-"} {regsHex regs'}"
    regs := regs'
  if regs.getD 0 0 != 3 || regs.getD 5 0 != leased.toUInt64 || regs.getD 2 0 != mac then
    IO.eprintln s!"error: the client did not end bound to the lease: {regsHex regs}"
    ok := false
  -- 2. Every frame from both waiting states, against the reference client.
  let states := [selecting xid0, requesting xid0 nakedIp serverIp]
  let frames : List ByteArray := List.map arr [
    reply LeanOS.Wifi.Dhcp.MsgType.offer xid0 nakedIp serverIp mac,
    reply LeanOS.Wifi.Dhcp.MsgType.ack xid0 nakedIp serverIp mac,
    reply LeanOS.Wifi.Dhcp.MsgType.nak xid0 0 serverIp mac,
    reply LeanOS.Wifi.Dhcp.MsgType.ack xid0 nakedIp otherServerIp mac,
    reply LeanOS.Wifi.Dhcp.MsgType.offer (xid0 + 1) nakedIp serverIp mac,
    reply LeanOS.Wifi.Dhcp.MsgType.ack xid0 nakedIp serverIp 0x02004c454141,
    arpRequest peerMac peerIp leased]
  let mut compared := 0
  for r in states do
    for f in frames do
      let mut variants : Array ByteArray := #[f]
      for i in [0:f.size] do
        for x in [0x01, 0x80, 0xff] do
          variants := variants.push (f.set! i (f[i]! ^^^ (x : UInt8)))
      for n in [14, 33, 34, 41, 42, 281, 282, 283, 290, f.size - 1] do
        if n < f.size then variants := variants.push (f.extract 0 n)
      for g in variants do
        let (regs', got) := DhcpClient.stepRecord r g
        let (want, wantOut) := refFrame r g
        if modelRegs regs' != want || got.map (·.toList) != wantOut.map (·.toList) then
          if ok then
            IO.eprintln s!"error: model {modelRegs regs'} {got.map hex} != reference {want} {wantOut.map hex} on {hex g}"
          ok := false
        compared := compared + 1
        lines := lines.push s!"{regsHex r} {hex g} {(got.map hex).getD "-"} {regsHex regs'}"
  -- 3. Ticks: retransmissions while selecting and requesting, and the
  -- restart after the third unanswered REQUEST.
  let mut t := requesting xid0 nakedIp serverIp
  for _ in [0:9] do
    let (t', got) := DhcpClient.stepRecord t tick
    lines := lines.push s!"{regsHex t} {hex tick} {(got.map hex).getD "-"} {regsHex t'}"
    t := t'
  if t.getD 0 0 != 1 || t.getD 1 0 != xid1.toUInt64 then
    IO.eprintln s!"error: three unanswered REQUESTs did not restart: {regsHex t}"
    ok := false
  unless ok do return 1
  IO.FS.writeFile out (String.intercalate "\n" lines.toList ++ "\n")
  let sent := (lines.filter fun l => (l.splitOn " ").getD 2 "-" != "-").size
  IO.println s!"net-dhcp vectors: {lines.size} records, {sent} with a frame sent, {compared} compared with Wifi.Dhcp.Client -> {out}"
  return 0
