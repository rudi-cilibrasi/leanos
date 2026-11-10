import LeanOS.DeviceProgramConfinement

/-!
Print every device-program policy of `LeanOS.DeviceProgramConfinement` in a
canonical one-line form, for `scripts/check-device-policies.py` (issue #642).
That script requires each C `struct wifi_policy` profile in `boot/kernel.c`
and `hardware/lab/qotom-wifi.c.inc` to equal the policy its comment names.

Line format (all numbers hexadecimal):
`NAME window=W cfgRead=R cfgWrite=W cmdClear=C cmdSet=S dma=0|1
sinks=A,B,... descs=T:START:COUNT:STRIDE,...` (an empty list prints `-`).
-/

open LeanOS.Wifi.Bytecode LeanOS.DeviceProgramConfinement

private def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

private def list (xs : List String) : String := if xs.isEmpty then "-" else ",".intercalate xs

private def line (name : String) (π : Policy) : String :=
  s!"{name} window={hex π.window.toNat} cfgRead={hex π.cfgRead.toNat} " ++
  s!"cfgWrite={hex π.cfgWrite.toNat} cmdClear={hex π.cmdClear.toNat} " ++
  s!"cmdSet={hex π.cmdSet.toNat} dma={if π.dma then 1 else 0} " ++
  s!"sinks={list (π.addrSinks.map (hex ·.toNat))} " ++
  s!"descs={list (π.descriptors.map fun d =>
    s!"{if d.trb then 1 else 0}:{hex d.start.toNat}:{hex d.count.toNat}:{hex d.stride.toNat}")}"

/-- Every named policy. A new policy must be added here, or the check cannot
find the policy its C profile names. -/
def policies : List (String × Policy) :=
  [("qotomBcm43224Policy", qotomBcm43224Policy),
   ("qotomXhciPolicy", qotomXhciPolicy),
   ("qotomAhciPolicy", qotomAhciPolicy),
   ("qotomRtl8168Policy", qotomRtl8168Policy),
   ("q35XhciPolicy", q35XhciPolicy),
   ("q35AhciPolicy", q35AhciPolicy),
   ("q35FrameSourcePolicy", q35FrameSourcePolicy)]

def main : IO Unit :=
  for (name, π) in policies do
    IO.println (line name π)
