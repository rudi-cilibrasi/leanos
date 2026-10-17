/-!
# Qotom bounded copy-root publication checkpoint

This scalar boundary admits the exact first Qotom root construction and a
sixteen-byte cross-page copy-in only after the machine adapter reports both
root scans, two mandatory reload paths, closed-root readback, and byte
agreement.  It publishes no CPL3 authority because production entry and
return integration remain separate obligations.

The protected inventory is A's text, A's two stack pages, B's text and B's
stack, and in the production profile also C's text and stack.  Exactly three
audited inventories exist, and the caller names the one its image was built
for with an explicit variant input:

* variant 0, the ordinary profile: A's text is one page, so five protected
  frames; the source root maps three of them (A's text and stack) and
  retains 4088 other present leaves;
* variant 1, the DHCP-subject profile (`LEANOS_QOTOM_DHCP_SUBJECT`, issue
  #556): A's text holds both the generated DHCP client and the echo
  responder and spans two pages, so six protected frames; the source root
  maps four of them and retains 4087;
* variant 2, the production network profile (`LEANOS_QOTOM_PRODUCTION_NETWORK`,
  issue #569): A's text holds the asm subjects and the DHCP client and
  spans two pages, and the inventory adds subject C's text page and stack
  page, so eight protected frames; the image's three-root boot plan omits
  C's pages from A's root, the source, so it maps four of them (A's text and
  stack) and retains 4085.

Every other variant is rejected, and no variant accepts another's counts.
-/
namespace LeanOS.QotomCopyRootPublication

/-- The ordinary five-frame inventory. -/
def baseVariant : UInt64 := 0
/-- The DHCP-subject six-frame inventory (A's text spans two pages). -/
def dhcpSubjectVariant : UInt64 := 1
/-- The production eight-frame inventory (subject C's pages added). -/
def productionVariant : UInt64 := 2

def knownVariant (variant : UInt64) : Bool :=
  variant == baseVariant || variant == dhcpSubjectVariant || variant == productionVariant

/-- The protected-frame count is exactly the selected variant's. -/
def protectedExact (variant protectedCount : UInt64) : Bool :=
  (variant == baseVariant && protectedCount == 5) ||
  (variant == dhcpSubjectVariant && protectedCount == 6) ||
  (variant == productionVariant && protectedCount == 8)

/-- The removed source aliases and retained present leaves are exactly the
selected variant's. The first two keep 4091 present source leaves; the
production variant 4089, since A's root also omits C's two pages. -/
def countsExact (variant removed retained : UInt64) : Bool :=
  (variant == baseVariant && removed == 3 && retained == 4088) ||
  (variant == dhcpSubjectVariant && removed == 4 && retained == 4087) ||
  (variant == productionVariant && removed == 4 && retained == 4085)

def alignedArenaRoot (root : UInt64) : Bool :=
  root != 0 && root < 0x1000000 && root &&& 0xfff == 0

/-- Stable bits cover the builder result, the selected variant's inventory and
alias counts, root identities, machine scans, transfer length/data, final
active closed root, and the variant itself. Zero is the only accepted error
mask. -/
def errorMask (variant builderStatus protectedCount removed retained aliases
    closedRoot copyRoot closedScan copyScan transferred bytesMatch
    activeRoot : UInt64) : UInt64 :=
  (if builderStatus == 0 then 0 else 1) |||
  (if protectedExact variant protectedCount then 0 else 2) |||
  (if countsExact variant removed retained then 0 else 4) |||
  (if aliases == 2 then 0 else 8) |||
  (if alignedArenaRoot closedRoot then 0 else 16) |||
  (if alignedArenaRoot copyRoot && copyRoot != closedRoot then 0 else 32) |||
  (if closedScan == 1 then 0 else 64) |||
  (if copyScan == 1 then 0 else 128) |||
  (if transferred == 16 then 0 else 256) |||
  (if bytesMatch == 1 then 0 else 512) |||
  (if activeRoot == closedRoot then 0 else 1024) |||
  (if knownVariant variant then 0 else 2048)

def accepted (variant builderStatus protectedCount removed retained aliases
    closedRoot copyRoot closedScan copyScan transferred bytesMatch
    activeRoot : UInt64) : Bool :=
  errorMask variant builderStatus protectedCount removed retained aliases
    closedRoot copyRoot closedScan copyScan transferred bytesMatch activeRoot == 0

/-- Words are ABI, acceptance, error mask, closed-root publication,
copy-root publication, completed bytes, CPL3 authority, and next-checkpoint
identity. Root publication means an audited reload selected the constructed
root and read it back; it does not imply entry-path coverage. ABI 2 adds the
leading inventory variant. -/
def query (variant builderStatus protectedCount removed retained aliases
    closedRoot copyRoot closedScan copyScan transferred bytesMatch
    activeRoot word : UInt64) : UInt64 :=
  let ok := accepted variant builderStatus protectedCount removed retained
    aliases closedRoot copyRoot closedScan copyScan transferred bytesMatch
    activeRoot
  if word == 0 then 2
  else if word == 1 then if ok then 1 else 2
  else if word == 2 then errorMask variant builderStatus protectedCount removed
    retained aliases closedRoot copyRoot closedScan copyScan transferred
    bytesMatch activeRoot
  else if word == 3 then if ok then 1 else 0
  else if word == 4 then if ok then 1 else 0
  else if word == 5 then if ok then transferred else 0
  else if word == 7 then 1
  else 0

theorem query_never_authorizes_cpl3 variant builderStatus protectedCount removed
    retained aliases closedRoot copyRoot closedScan copyScan transferred
    bytesMatch activeRoot :
    query variant builderStatus protectedCount removed retained aliases
      closedRoot copyRoot closedScan copyScan transferred bytesMatch activeRoot
      6 = 0 := by
  simp [query]

theorem publication_requires_acceptance variant builderStatus protectedCount
    removed retained aliases closedRoot copyRoot closedScan copyScan transferred
    bytesMatch activeRoot
    (h : query variant builderStatus protectedCount removed retained aliases
      closedRoot copyRoot closedScan copyScan transferred bytesMatch activeRoot
      3 = 1) :
    accepted variant builderStatus protectedCount removed retained aliases
      closedRoot copyRoot closedScan copyScan transferred bytesMatch
      activeRoot = true := by
  simpa [query] using h

/-- Acceptance pins the inventory to exactly one of the three audited profiles,
and to the one the caller selected: no other variant, protected count, or
removed/retained pair is admitted, and a variant never accepts the other
variant's counts. -/
theorem accepted_inventory_exact variant builderStatus protectedCount removed
    retained aliases closedRoot copyRoot closedScan copyScan transferred
    bytesMatch activeRoot
    (h : accepted variant builderStatus protectedCount removed retained aliases
      closedRoot copyRoot closedScan copyScan transferred bytesMatch
      activeRoot = true) :
    (variant = baseVariant ∧ protectedCount = 5 ∧ removed = 3 ∧
        retained = 4088) ∨
      (variant = dhcpSubjectVariant ∧ protectedCount = 6 ∧ removed = 4 ∧
        retained = 4087) ∨
      (variant = productionVariant ∧ protectedCount = 8 ∧ removed = 4 ∧
        retained = 4085) := by
  simp only [accepted, errorMask, beq_iff_eq, UInt64.or_eq_zero_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, hp⟩, hc⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  split at hp
  · split at hc
    · rename_i hp' hc'
      simp only [protectedExact, countsExact, baseVariant, dhcpSubjectVariant,
        productionVariant, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hp' hc'
      simp only [baseVariant, dhcpSubjectVariant, productionVariant]
      rcases hp' with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩ <;>
        rcases hc' with (⟨⟨hv, rfl⟩, rfl⟩ | ⟨⟨hv, rfl⟩, rfl⟩) | ⟨⟨hv, rfl⟩, rfl⟩ <;>
        first | exact absurd hv (by decide) | simp
    · exact absurd hc (by decide)
  · exact absurd hp (by decide)

/-- The ordinary five-frame inventory publishes both roots. -/
theorem base_inventory_publishes :
    query baseVariant 0 5 3 4088 2 0x300000 0x30b000 1 1 16 1 0x300000 3 = 1 ∧
      query baseVariant 0 5 3 4088 2 0x300000 0x30b000 1 1 16 1 0x300000 2 = 0 := by
  decide

/-- The DHCP-subject six-frame inventory publishes both roots. -/
theorem dhcp_subject_inventory_publishes :
    query dhcpSubjectVariant 0 6 4 4087 2 0x300000 0x30b000 1 1 16 1 0x300000
        3 = 1 ∧
      query dhcpSubjectVariant 0 6 4 4087 2 0x300000 0x30b000 1 1 16 1 0x300000
        2 = 0 := by
  decide

/-- The production eight-frame inventory publishes both roots. -/
theorem production_inventory_publishes :
    query productionVariant 0 8 4 4085 2 0x300000 0x30b000 1 1 16 1 0x300000
        3 = 1 ∧
      query productionVariant 0 8 4 4085 2 0x300000 0x30b000 1 1 16 1 0x300000
        2 = 0 := by
  decide

/-- Each variant rejects the others' inventories with the protected-count and
removed/retained bits, and an unknown variant is rejected outright. -/
theorem variants_reject_each_others_inventory :
    query baseVariant 0 6 4 4087 2 0x300000 0x30b000 1 1 16 1 0x300000 2 = 6 ∧
      query dhcpSubjectVariant 0 5 3 4088 2 0x300000 0x30b000 1 1 16 1 0x300000
        2 = 6 ∧
      query baseVariant 0 8 4 4085 2 0x300000 0x30b000 1 1 16 1 0x300000 2 = 6 ∧
      query productionVariant 0 5 3 4088 2 0x300000 0x30b000 1 1 16 1 0x300000
        2 = 6 ∧
      query productionVariant 0 6 4 4087 2 0x300000 0x30b000 1 1 16 1 0x300000
        2 = 6 ∧
      query 3 0 5 3 4088 2 0x300000 0x30b000 1 1 16 1 0x300000 2 = 2054 ∧
      query 3 0 8 4 4085 2 0x300000 0x30b000 1 1 16 1 0x300000 2 = 2054 := by
  decide

example : query baseVariant 0 5 3 4088 2 0x300000 0x30b000 1 1 16 1
    0x300000 1 = 1 := by decide
example : query baseVariant 0 5 3 4088 2 0x300000 0x30b000 1 1 15 1
    0x300000 1 = 2 := by decide
example : query baseVariant 0 5 3 4088 2 0x300000 0x30b000 1 1 16 1
    0x300000 6 = 0 := by decide
example : query dhcpSubjectVariant 0 6 4 4088 2 0x300000 0x30b000 1 1 16 1
    0x300000 2 = 4 := by decide
example : query dhcpSubjectVariant 0 6 3 4087 2 0x300000 0x30b000 1 1 16 1
    0x300000 2 = 4 := by decide

@[export leanos_qotom_copy_root_publication_query]
def exportedQuery (variant builderStatus protectedCount removed retained aliases
    closedRoot copyRoot closedScan copyScan transferred bytesMatch activeRoot
    word : UInt64) : UInt64 :=
  query variant builderStatus protectedCount removed retained aliases closedRoot
    copyRoot closedScan copyScan transferred bytesMatch activeRoot word

end LeanOS.QotomCopyRootPublication
