import LeanOS.SecurityClaims

open LeanOS

/- Granting the console capability to a second subject must break the
console-integrity claim: `b` is then no longer unprivileged, and its console
write changes the trace. -/
def twoHolders : ConsoleServer.Authority where
  console s := s == .server || s == .b
  reachesServer s := s == .a

example :
    (ConsoleServer.run twoHolders ConsoleServer.initial [(.b, .write 7)]).1.output =
      (ConsoleServer.run twoHolders ConsoleServer.initial []).1.output :=
  SecurityClaims.console_integrity twoHolders .b ⟨rfl, rfl⟩ ConsoleServer.initial
    [(.b, .write 7)] [] rfl
