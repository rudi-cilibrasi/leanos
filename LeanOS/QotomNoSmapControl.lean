/-!
# Qotom J1900 no-SMAP machine-control checkpoint

This scalar boundary validates the live control transition selected by ADR
0017.  It authorizes enabling SMEP while keeping SMAP, PCID, PGE, and
interrupts disabled.  Acceptance identifies the bounded two-root copy
strategy, but deliberately publishes neither root and grants no CPL3
authority.
-/
namespace LeanOS.QotomNoSmapControl

def wpMask : UInt64 := 0x10000
def pgeMask : UInt64 := 0x80
def pcidMask : UInt64 := 0x20000
def smepMask : UInt64 := 0x100000
def smapMask : UInt64 := 0x200000
def nxeMask : UInt64 := 0x800
def interruptMask : UInt64 := 0x200

def preconditions (cr0 cr4Before efer rflags : UInt64) : Bool :=
  cr0 &&& wpMask == wpMask &&
  efer &&& nxeMask == nxeMask &&
  cr4Before &&& smepMask == 0 &&
  cr4Before &&& smapMask == 0 &&
  cr4Before &&& pcidMask == 0 &&
  cr4Before &&& pgeMask == 0 &&
  rflags &&& interruptMask == 0

def transitionAccepted
    (cr0 cr4Before cr4After efer rflags : UInt64) : Bool :=
  preconditions cr0 cr4Before efer rflags &&
  cr4After == (cr4Before ||| smepMask) &&
  cr4After &&& smepMask == smepMask &&
  cr4After &&& smapMask == 0 &&
  cr4After &&& pcidMask == 0 &&
  cr4After &&& pgeMask == 0

/-- Stable diagnostic bits: WP, NXE, pre-SMAP, PCID, PGE, IF, exact CR4
transition, post-SMEP, and pre-SMEP respectively. Zero is the only accepted
mask. -/
def errorMask (cr0 cr4Before cr4After efer rflags : UInt64) : UInt64 :=
  (if cr0 &&& wpMask == wpMask then 0 else 1) +
  (if efer &&& nxeMask == nxeMask then 0 else 2) +
  (if cr4Before &&& smapMask == 0 then 0 else 4) +
  (if cr4Before &&& pcidMask == 0 then 0 else 8) +
  (if cr4Before &&& pgeMask == 0 then 0 else 16) +
  (if rflags &&& interruptMask == 0 then 0 else 32) +
  (if cr4After == (cr4Before ||| smepMask) then 0 else 64) +
  (if cr4After &&& smepMask == smepMask && cr4After &&& smapMask == 0 &&
      cr4After &&& pcidMask == 0 && cr4After &&& pgeMask == 0 then 0 else 128)
  + (if cr4Before &&& smepMask == 0 then 0 else 256)

/-- Words are ABI, precondition status, transition status, error mask,
strategy identity, maximum bytes, maximum aliases, mandatory reload, CPL3
authority, closed-root publication, and copy-root publication. -/
def query (cr0 cr4Before cr4After efer rflags word : UInt64) : UInt64 :=
  if word == 0 then 1
  else if word == 1 then if preconditions cr0 cr4Before efer rflags then 1 else 2
  else if word == 2 then if transitionAccepted cr0 cr4Before cr4After efer rflags then 1 else 2
  else if word == 3 then errorMask cr0 cr4Before cr4After efer rflags
  else if word == 4 then 1
  else if word == 5 then 16
  else if word == 6 then 2
  else if word == 7 then 1
  else 0

theorem query_never_authorizes_cpl3 cr0 cr4Before cr4After efer rflags :
    query cr0 cr4Before cr4After efer rflags 8 = 0 := by
  simp [query]

theorem query_never_claims_root_publication cr0 cr4Before cr4After efer rflags :
    query cr0 cr4Before cr4After efer rflags 9 = 0 ∧
    query cr0 cr4Before cr4After efer rflags 10 = 0 := by
  simp [query]

theorem transition_one_iff cr0 cr4Before cr4After efer rflags :
    query cr0 cr4Before cr4After efer rflags 2 = 1 ↔
      transitionAccepted cr0 cr4Before cr4After efer rflags = true := by
  simp [query]

example : query 0x10000 0x20 0x100020 0x800 0x2 1 = 1 := by decide
example : query 0x10000 0x20 0x100020 0x800 0x2 2 = 1 := by decide
example : query 0x10000 0x20 0x100020 0x800 0x202 2 = 2 := by decide
example : query 0x10000 0x20 0x300020 0x800 0x2 2 = 2 := by decide
example : query 0x10000 0x100020 0x100020 0x800 0x2 2 = 2 := by decide

@[export leanos_qotom_nosmap_control_query]
def exportedQuery (cr0 cr4Before cr4After efer rflags word : UInt64) : UInt64 :=
  query cr0 cr4Before cr4After efer rflags word

end LeanOS.QotomNoSmapControl
