import LeanOS.SpawnOracle

namespace LeanOS.NegativeFixtures.SpawnIdentityRollback

open LeanOS
open LeanOS.FailStop
open LeanOS.SpawnOracle

/-- A spawn that forgets to roll back the identity: when a stage after
issuance fails, it keeps the state with the child already issued. -/
def forgetfulSpawn (state : CompositeState) (request : SpawnRequest) : SpawnOutcome :=
  match spawnBuild state request with
  | .ok built => { state := built.state, result := .spawned built.child built.addressSpace }
  | .error reason =>
      match spawnAuthorize state request.spawnWord, (issueSubject state).result with
      | none, .issued _ => { state := (issueSubject state).state, result := .rejected reason }
      | _, _ => { state, result := .rejected reason }

/-- The stale-endpoint vector: generation 4 at slot 0 is not subject 2's
endpoint, so the grant stage fails after the identity was issued. -/
def staleRequest : SpawnRequest :=
  { spawnWord := 1, endpointWord := 0x40000, rights := sendOnly }

def rollsBack : Bool :=
  match BootPageTablePlan.compile BootPageTablePlan.sampleInput with
  | .ok plan =>
      let seed := spawnOracleSeed plan
      let outcome := forgetfulSpawn seed staleRequest
      outcome.result == .rejected (.endpointHandle (.denied .staleHandle)) &&
        observe outcome.state == observe seed
  | .error _ => false

/- The forgetful spawn reports the typed rejection but leaves subject 3
issued and live, and the subject counter advanced: the oracle's rollback check
must fail. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  rollsBack = true
is false
-/
#guard_msgs in
example : rollsBack = true := by
  native_decide

/-- The authoritative spawn passes the same check. -/
example : (match BootPageTablePlan.compile BootPageTablePlan.sampleInput with
    | .ok plan =>
        let seed := spawnOracleSeed plan
        let outcome := spawn seed staleRequest
        outcome.result == .rejected (.endpointHandle (.denied .staleHandle)) &&
          observe outcome.state == observe seed
    | .error _ => false) = true := by
  native_decide

end LeanOS.NegativeFixtures.SpawnIdentityRollback
