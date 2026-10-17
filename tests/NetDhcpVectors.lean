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
   each with single-byte corruptions of every byte and truncations. On
   ticks it must follow RFC 2131's retransmission schedule (issue #573):
   each tick agrees with the proved timer model `DhcpClient.Timer.tick`,
   and the waits between retransmissions are 4, 8, 16, 32, then 64 ticks,
   each within ±1 (an independent statement of the RFC's schedule), for
   DISCOVER and REQUEST and over many transaction ids.
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
  -- 3. Ticks: the RFC 2131 retransmission schedule (issue #573). The waits
  -- are checked against an independent statement of the RFC's schedule
  -- (4, 8, 16, 32, then 64 seconds, ±1), each tick against the proved
  -- timer model `DhcpClient.Timer.tick`, and each frame against
  -- `Wifi.Dhcp`.
  let rfcBase (n : Nat) : Nat := min (4 * 2 ^ n) 64
  let discover0 := toEthernet (LeanOS.Wifi.Dhcp.discover macArray xid0)
  let request0 := toEthernet (LeanOS.Wifi.Dhcp.request macArray xid0 nakedIp serverIp)
  let discover1 := toEthernet (LeanOS.Wifi.Dhcp.discover macArray xid1)
  -- 3a. selecting, right after the first DISCOVER: six retransmissions.
  let mut t := selecting xid0
  let mut gaps : Array Nat := #[]
  let mut since := 0
  for _ in [0:200] do
    let (t', got) := DhcpClient.stepRecord t tick
    lines := lines.push s!"{regsHex t} {hex tick} {(got.map hex).getD "-"} {regsHex t'}"
    let (want, sent) := (DhcpClient.Timer.ofRegs t).tick
    if DhcpClient.Timer.ofRegs t' != want || got.isSome != (sent != .none) ||
        (got.isSome && got.map (·.toList) != some discover0.toList) then
      IO.eprintln s!"error: selecting tick from {regsHex t}: {regsHex t'} {got.map hex}"
      ok := false
    since := since + 1
    if got.isSome then
      gaps := gaps.push since
      since := 0
    t := t'
  if gaps.size < 6 then
    IO.eprintln s!"error: {gaps.size} DISCOVER retransmissions in 200 ticks"
    ok := false
  for k in [0:gaps.size] do
    -- the retransmission count saturates at `backoffSteps` (4): the wait
    -- stays 64 ±1 from then on
    let d := (DhcpClient.retransmitDelay xid0.toUInt64 (min k 4).toUInt64).toNat
    if gaps[k]! != d || gaps[k]! + 1 < rfcBase k || gaps[k]! > rfcBase k + 1 then
      IO.eprintln s!"error: DISCOVER retransmission {k} after {gaps[k]!} ticks, RFC base {rfcBase k}"
      ok := false
  -- 3b. requesting: two REQUEST retransmissions, then DISCOVER with the
  -- next transaction id after the third REQUEST's wait.
  let mut r := requesting xid0 nakedIp serverIp
  let mut sends : Array (Nat × List UInt8) := #[]
  since := 0
  for _ in [0:40] do
    let (r', got) := DhcpClient.stepRecord r tick
    lines := lines.push s!"{regsHex r} {hex tick} {(got.map hex).getD "-"} {regsHex r'}"
    let (want, sent) := (DhcpClient.Timer.ofRegs r).tick
    if DhcpClient.Timer.ofRegs r' != want || got.isSome != (sent != .none) then
      IO.eprintln s!"error: requesting tick from {regsHex r}: {regsHex r'}"
      ok := false
    since := since + 1
    if let some g := got then
      sends := sends.push (since, g.toList)
      since := 0
    r := r'
  let d (n : Nat) := (DhcpClient.retransmitDelay xid0.toUInt64 n.toUInt64).toNat
  let wantSends := [(d 0, request0.toList), (d 1, request0.toList), (d 2, discover1.toList)]
  if sends.toList.take wantSends.length != wantSends ||
      (DhcpClient.Timer.ofRegs r).phase != 1 || (DhcpClient.Timer.ofRegs r).xid != xid1.toUInt64 then
    IO.eprintln s!"error: unanswered REQUESTs: {sends.toList.map (·.1)}, ended {regsHex r}"
    ok := false
  for k in [0:3] do
    if d k + 1 < rfcBase k || d k > rfcBase k + 1 then
      IO.eprintln s!"error: REQUEST wait {k} is {d k} ticks, RFC base {rfcBase k}"
      ok := false
  -- 3c. Many transactions: every wait within ±1 of the RFC's base, and the
  -- jitter takes each of -1, 0 and +1 (no vectors written).
  let mut jitters : List Int := []
  for x in [0:96] do
    let xid := xid0 + (x * 7919).toUInt32
    let mut c := selecting xid
    let mut gap := 0
    let mut k := 0
    for _ in [0:130] do
      let (c', got) := DhcpClient.stepRecord c tick
      gap := gap + 1
      if got.isSome then
        let j : Int := (gap : Int) - rfcBase k
        if j < -1 || j > 1 then
          IO.eprintln s!"error: xid {xid}: retransmission {k} after {gap} ticks"
          ok := false
        jitters := j :: jitters
        k := k + 1
        gap := 0
      c := c'
  unless [-1, 0, 1].all (jitters.contains ·) do
    IO.eprintln "error: the jitter does not take each of -1, 0 and +1"
    ok := false
  unless ok do return 1
  IO.FS.writeFile out (String.intercalate "\n" lines.toList ++ "\n")
  let sent := (lines.filter fun l => (l.splitOn " ").getD 2 "-" != "-").size
  IO.println s!"net-dhcp vectors: {lines.size} records, {sent} with a frame sent, {compared} compared with Wifi.Dhcp.Client -> {out}"
  return 0
