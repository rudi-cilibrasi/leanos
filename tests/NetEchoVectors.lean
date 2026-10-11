import LeanOS.Net.FrameSource

/-!
Hosted vectors for the network subject's responder (issue #450).

1. The reference responder `LeanOS.Net.Echo.replyFrame` must agree, on the
   frame source's frames, with replies built independently from the frame
   constructors (an ARP reply with the fields written out, an ICMP echo
   reply and a UDP datagram built from scratch with their own checksums),
   so the in-place rewrite and the incremental checksum are checked against
   a second construction.
2. It then prints vectors for the differential test of the generated C
   (`scripts/check-network-subject-host.sh`): every frame source frame and,
   for each, deterministic single-byte corruptions of the first 42 bytes and
   truncations, each with the reference reply (`-` for none).

usage: leanos-net-echo-vectors OUT
-/

open LeanOS.Net LeanOS.Net.FrameSource

def hex (b : ByteArray) : String :=
  String.join (b.toList.map fun x =>
    let s := String.ofList (Nat.toDigits 16 x.toNat)
    if s.length == 1 then "0" ++ s else s)

def arr (l : List UInt8) : ByteArray := ⟨l.toArray⟩

/-- The expected replies, built independently of `Echo.reply`. -/
def expected : List (Option ByteArray) := [
  some (arr (ethernet peerMac mac 0x0806
    ([0, 1, 8, 0, 6, 4, 0, 2] ++ macBytes mac ++ ipBytes ip ++ macBytes peerMac ++
      ipBytes peerIp))),
  some (arr (
    let data := ascii "leanos network subject"
    let msg (sum : Nat) := [0, 0] ++ be16 sum ++ be16 0x4c45 ++ be16 1 ++ data
    ethernet peerMac mac 0x0800 (ipv4 1 ip peerIp 0x1001 (msg (checksum (msg 0)))))),
  some (arr (udpDatagram peerMac mac ip peerIp 7 40000 (ascii "echo through ring 3"))),
  none, none, none]

def main (args : List String) : IO UInt32 := do
  let [out] := args | do IO.eprintln "usage: leanos-net-echo-vectors OUT"; return 2
  let mut ok := true
  for (k, got, want) in (List.range replies.length).zip (replies.zip expected) do
    if got.map (·.toList) != want.map (·.toList) then
      IO.eprintln s!"error: frame {k + 1}: reference reply {got.map hex} != expected {want.map hex}"
      ok := false
  unless ok do return 1
  let mut lines : Array String := #[]
  let emit (f : ByteArray) : String :=
    s!"{hex f} {(Echo.replyFrame f mac ip).map hex |>.getD "-"}"
  for f in frames do
    lines := lines.push (emit f)
    for i in [0:min 42 f.size] do
      for x in [0x01, 0x80, 0xff] do
        let g := f.set! i (f[i]! ^^^ (x : UInt8))
        lines := lines.push (emit g)
    for n in [1, 13, 14, 33, 34, 41, 42, f.size - 1] do
      if n < f.size then lines := lines.push (emit (f.extract 0 n))
  IO.FS.writeFile out (String.intercalate "\n" lines.toList ++ "\n")
  let replied := (lines.filter fun l => !l.endsWith " -").size
  IO.println s!"net-echo vectors: {lines.size} frames, {replied} with a reply -> {out}"
  return 0
