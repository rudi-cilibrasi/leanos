import LeanOS.QotomNativePCIInventory

/-! Scalar representation of the complete native identity/routing inventory.
These values carry no command policy or DMA authority. -/
namespace LeanOS.QotomNativePCIFields
open QotomPCIInventory

/-- BDF, vendor/device/class, multifunction, layout, and four routing fields.
Endpoint routing fields are canonical zero. -/
def entryWords (entry : Entry) : List UInt64 :=
  [entry.bdf.bus, entry.bdf.device, entry.bdf.function,
   entry.identity.vendor, entry.identity.device, entry.identity.classCode,
   if entry.multifunction then 1 else 0] ++
    match entry.routing with
    | .endpoint => [0, 0, 0, 0, 0]
    | .bridge p s u c => [1, p, s, u, c]

/-- Scalar encoding loses none of the typed inventory projection. -/
theorem entryWords_injective (a b : Entry)
    (same : entryWords a = entryWords b) : a = b := by
  rcases a with ⟨⟨ab, ad, af⟩, ⟨av, ai, ac⟩, am, ar⟩
  rcases b with ⟨⟨bb, bd, bf⟩, ⟨bv, bi, bc⟩, bm, br⟩
  cases am <;> cases bm <;> cases ar <;> cases br <;>
    simp_all [entryWords]

/-- Equality of all encoded rows implies equality of the complete inventory. -/
theorem entries_eq_of_words (a b : List Entry)
    (same : a.map entryWords = b.map entryWords) : a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all
  | cons first rest ih =>
    cases b with
    | nil => simp_all
    | cons next tail =>
      simp only [List.map_cons, List.cons.injEq] at same
      rw [entryWords_injective first next same.1, ih tail same.2]

/-- Complete scalar-row equality supplies the native witness's exact inventory
property; count, ordering, and every typed field are included. -/
theorem native_inventory_of_words (headers : List PCIHeaderObservation.Header)
    (same : (headers.map QotomPCIInventory.project).map entryWords =
      QotomNativePCIInventory.baseline.map entryWords) :
    headers.map QotomPCIInventory.project = QotomNativePCIInventory.baseline :=
  entries_eq_of_words _ _ same

/-- The reference observer's selected fields encode precisely the typed
inventory projection of the accepted header. -/
theorem observed_entry_words (raw : PCIHeaderObservation.RawHeader)
    (header : PCIHeaderObservation.Header)
    (accepted : PCIHeaderObservation.decode raw = .ok header) :
    [raw.bdf.bus, raw.bdf.device, raw.bdf.function,
     PCIHeaderObservation.observe raw 1, PCIHeaderObservation.observe raw 2,
     PCIHeaderObservation.observe raw 3, PCIHeaderObservation.observe raw 7,
     PCIHeaderObservation.observe raw 8, PCIHeaderObservation.observe raw 9,
     PCIHeaderObservation.observe raw 10, PCIHeaderObservation.observe raw 11,
     PCIHeaderObservation.observe raw 12] = entryWords (project header) := by
  have address := congrArg PCIHeaderObservation.RawHeader.bdf
    (PCIHeaderObservation.decode_preserves_raw raw header accepted)
  cases layout : header.layout <;>
    simp [PCIHeaderObservation.observe, accepted,
      PCIHeaderObservation.observationWords, entryWords, project, layout, address]

/-- Closed scalar table. Invalid index/field have distinct non-data tags. -/
def expected (index field : UInt64) : UInt64 :=
  if index ≥ 16 then 0x70000
  else if field ≥ 12 then 0x70001
  else if index == 0 then
    if field == 0 then 0x0
    else if field == 1 then 0x0
    else if field == 2 then 0x0
    else if field == 3 then 0x8086
    else if field == 4 then 0xf00
    else if field == 5 then 0x60000
    else if field == 6 then 0x0
    else if field == 7 then 0x0
    else if field == 8 then 0x0
    else if field == 9 then 0x0
    else if field == 10 then 0x0
    else 0x0
  else if index == 1 then
    if field == 0 then 0x0
    else if field == 1 then 0x2
    else if field == 2 then 0x0
    else if field == 3 then 0x8086
    else if field == 4 then 0xf31
    else if field == 5 then 0x30000
    else if field == 6 then 0x0
    else if field == 7 then 0x0
    else if field == 8 then 0x0
    else if field == 9 then 0x0
    else if field == 10 then 0x0
    else 0x0
  else if index == 2 then
    if field == 0 then 0x0
    else if field == 1 then 0x13
    else if field == 2 then 0x0
    else if field == 3 then 0x8086
    else if field == 4 then 0xf23
    else if field == 5 then 0x10601
    else if field == 6 then 0x0
    else if field == 7 then 0x0
    else if field == 8 then 0x0
    else if field == 9 then 0x0
    else if field == 10 then 0x0
    else 0x0
  else if index == 3 then
    if field == 0 then 0x0
    else if field == 1 then 0x14
    else if field == 2 then 0x0
    else if field == 3 then 0x8086
    else if field == 4 then 0xf35
    else if field == 5 then 0xc0330
    else if field == 6 then 0x0
    else if field == 7 then 0x0
    else if field == 8 then 0x0
    else if field == 9 then 0x0
    else if field == 10 then 0x0
    else 0x0
  else if index == 4 then
    if field == 0 then 0x0
    else if field == 1 then 0x1a
    else if field == 2 then 0x0
    else if field == 3 then 0x8086
    else if field == 4 then 0xf18
    else if field == 5 then 0x108000
    else if field == 6 then 0x0
    else if field == 7 then 0x0
    else if field == 8 then 0x0
    else if field == 9 then 0x0
    else if field == 10 then 0x0
    else 0x0
  else if index == 5 then
    if field == 0 then 0x0
    else if field == 1 then 0x1b
    else if field == 2 then 0x0
    else if field == 3 then 0x8086
    else if field == 4 then 0xf04
    else if field == 5 then 0x40300
    else if field == 6 then 0x0
    else if field == 7 then 0x0
    else if field == 8 then 0x0
    else if field == 9 then 0x0
    else if field == 10 then 0x0
    else 0x0
  else if index == 6 then
    if field == 0 then 0x0
    else if field == 1 then 0x1c
    else if field == 2 then 0x0
    else if field == 3 then 0x8086
    else if field == 4 then 0xf48
    else if field == 5 then 0x60400
    else if field == 6 then 0x1
    else if field == 7 then 0x1
    else if field == 8 then 0x0
    else if field == 9 then 0x1
    else if field == 10 then 0x1
    else 0x10
  else if index == 7 then
    if field == 0 then 0x0
    else if field == 1 then 0x1c
    else if field == 2 then 0x1
    else if field == 3 then 0x8086
    else if field == 4 then 0xf4a
    else if field == 5 then 0x60400
    else if field == 6 then 0x1
    else if field == 7 then 0x1
    else if field == 8 then 0x0
    else if field == 9 then 0x2
    else if field == 10 then 0x2
    else 0x10
  else if index == 8 then
    if field == 0 then 0x0
    else if field == 1 then 0x1c
    else if field == 2 then 0x2
    else if field == 3 then 0x8086
    else if field == 4 then 0xf4c
    else if field == 5 then 0x60400
    else if field == 6 then 0x1
    else if field == 7 then 0x1
    else if field == 8 then 0x0
    else if field == 9 then 0x3
    else if field == 10 then 0x3
    else 0x10
  else if index == 9 then
    if field == 0 then 0x0
    else if field == 1 then 0x1c
    else if field == 2 then 0x3
    else if field == 3 then 0x8086
    else if field == 4 then 0xf4e
    else if field == 5 then 0x60400
    else if field == 6 then 0x1
    else if field == 7 then 0x1
    else if field == 8 then 0x0
    else if field == 9 then 0x4
    else if field == 10 then 0x4
    else 0x10
  else if index == 10 then
    if field == 0 then 0x0
    else if field == 1 then 0x1d
    else if field == 2 then 0x0
    else if field == 3 then 0x8086
    else if field == 4 then 0xf34
    else if field == 5 then 0xc0320
    else if field == 6 then 0x0
    else if field == 7 then 0x0
    else if field == 8 then 0x0
    else if field == 9 then 0x0
    else if field == 10 then 0x0
    else 0x0
  else if index == 11 then
    if field == 0 then 0x0
    else if field == 1 then 0x1f
    else if field == 2 then 0x0
    else if field == 3 then 0x8086
    else if field == 4 then 0xf1c
    else if field == 5 then 0x60100
    else if field == 6 then 0x1
    else if field == 7 then 0x0
    else if field == 8 then 0x0
    else if field == 9 then 0x0
    else if field == 10 then 0x0
    else 0x0
  else if index == 12 then
    if field == 0 then 0x0
    else if field == 1 then 0x1f
    else if field == 2 then 0x3
    else if field == 3 then 0x8086
    else if field == 4 then 0xf12
    else if field == 5 then 0xc0500
    else if field == 6 then 0x0
    else if field == 7 then 0x0
    else if field == 8 then 0x0
    else if field == 9 then 0x0
    else if field == 10 then 0x0
    else 0x0
  else if index == 13 then
    if field == 0 then 0x1
    else if field == 1 then 0x0
    else if field == 2 then 0x0
    else if field == 3 then 0x10ec
    else if field == 4 then 0x8168
    else if field == 5 then 0x20000
    else if field == 6 then 0x0
    else if field == 7 then 0x0
    else if field == 8 then 0x0
    else if field == 9 then 0x0
    else if field == 10 then 0x0
    else 0x0
  else if index == 14 then
    if field == 0 then 0x2
    else if field == 1 then 0x0
    else if field == 2 then 0x0
    else if field == 3 then 0x14e4
    else if field == 4 then 0x4353
    else if field == 5 then 0x28000
    else if field == 6 then 0x0
    else if field == 7 then 0x0
    else if field == 8 then 0x0
    else if field == 9 then 0x0
    else if field == 10 then 0x0
    else 0x0
  else 
    if field == 0 then 0x3
    else if field == 1 then 0x0
    else if field == 2 then 0x0
    else if field == 3 then 0x10ec
    else if field == 4 then 0x8168
    else if field == 5 then 0x20000
    else if field == 6 then 0x0
    else if field == 7 then 0x0
    else if field == 8 then 0x0
    else if field == 9 then 0x0
    else if field == 10 then 0x0
    else 0x0

/-- Each scalar row equals all twelve fields of the actual typed baseline.
The range proof covers every admitted index, not only captured positive cases. -/
theorem expected_row (index : UInt64) (bound : index < 16) :
    some ((List.range 12).map (fun field => expected index (UInt64.ofNat field))) =
      (QotomNativePCIInventory.baseline[index.toNat]?).map entryWords := by
  have positions : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 ∨ index = 9 ∨ index = 10 ∨ index = 11 ∨ index = 12 ∨ index = 13 ∨ index = 14 ∨ index = 15 := by
    simp only [UInt64.lt_iff_toNat_lt, ← UInt64.toNat_inj] at *
    simp at *
    omega
  rcases positions with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 <;> subst index <;> decide

/-- Compare all fields of one next-in-order native inventory entry. -/
def matchesFields (index f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 : UInt64) : Bool :=
  index < 16 && f0 == expected index 0 &&
    f1 == expected index 1 &&
    f2 == expected index 2 &&
    f3 == expected index 3 &&
    f4 == expected index 4 &&
    f5 == expected index 5 &&
    f6 == expected index 6 &&
    f7 == expected index 7 &&
    f8 == expected index 8 &&
    f9 == expected index 9 &&
    f10 == expected index 10 &&
    f11 == expected index 11

/-- A successful scalar comparison binds its complete row to the typed slot. -/
theorem matches_row (index f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 : UInt64)
    (matched : matchesFields index f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 = true) :
    some [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11] =
      (QotomNativePCIInventory.baseline[index.toNat]?).map entryWords := by
  simp only [matchesFields, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at matched
  have conditions : index < 16 ∧ f0 = expected index 0 ∧ f1 = expected index 1 ∧ f2 = expected index 2 ∧ f3 = expected index 3 ∧ f4 = expected index 4 ∧ f5 = expected index 5 ∧ f6 = expected index 6 ∧ f7 = expected index 7 ∧ f8 = expected index 8 ∧ f9 = expected index 9 ∧ f10 = expected index 10 ∧ f11 = expected index 11 := by simpa only [and_assoc] using matched
  rcases conditions with ⟨bound, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  have row := expected_row index bound
  change some [expected index 0, expected index 1, expected index 2, expected index 3, expected index 4, expected index 5, expected index 6, expected index 7, expected index 8, expected index 9, expected index 10, expected index 11] = _ at row
  simpa only [← h0, ← h1, ← h2, ← h3, ← h4, ← h5, ← h6, ← h7, ← h8, ← h9, ← h10, ← h11] using row

/-- When the supplied fields encode a decoded header projection, scalar
comparison proves that exact typed entry occupies the native baseline slot. -/
theorem matches_entry (index f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 : UInt64) (entry : Entry)
    (encoded : entryWords entry = [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11])
    (matched : matchesFields index f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 = true) :
    some entry = QotomNativePCIInventory.baseline[index.toNat]? := by
  have row := matches_row index f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 matched
  rw [← encoded] at row
  cases slot : QotomNativePCIInventory.baseline[index.toNat]? with
  | none => simp [slot] at row
  | some expectedEntry =>
    simp only [slot, Option.map_some, Option.some.injEq] at row
    exact congrArg some (entryWords_injective entry expectedEntry row)

/-- Validate and compare one immutable supplied header at its canonical index. -/
def checkHeader (index bus device fn w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : UInt64) : Bool :=
  PCIHeaderObservation.Scalar.status 16 bus device fn w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 == 1 &&
    matchesFields index bus device fn (PCIHeaderObservation.Scalar.query 1 16 bus device fn w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15)
      (PCIHeaderObservation.Scalar.query 2 16 bus device fn w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15)
      (PCIHeaderObservation.Scalar.query 3 16 bus device fn w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15)
      (PCIHeaderObservation.Scalar.query 7 16 bus device fn w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15)
      (PCIHeaderObservation.Scalar.query 8 16 bus device fn w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15)
      (PCIHeaderObservation.Scalar.query 9 16 bus device fn w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15)
      (PCIHeaderObservation.Scalar.query 10 16 bus device fn w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15)
      (PCIHeaderObservation.Scalar.query 11 16 bus device fn w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15)
      (PCIHeaderObservation.Scalar.query 12 16 bus device fn w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15)

/-- A successful scalar header check decodes the actual supplied raw words and
binds their typed projection to this exact native inventory slot. -/
theorem checkHeader_binds_raw (index bus device fn w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : UInt64)
    (matched : checkHeader index bus device fn w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 = true) :
    ∃ header, PCIHeaderObservation.decode ⟨⟨bus, device, fn⟩, [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15]⟩ = .ok header ∧
      some (project header) = QotomNativePCIInventory.baseline[index.toNat]? := by
  simp only [checkHeader, Bool.and_eq_true, beq_iff_eq] at matched
  have tag := PCIHeaderObservation.Scalar.status_eq_decode bus device fn w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
  cases decoded : PCIHeaderObservation.decode ⟨⟨bus, device, fn⟩, [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15]⟩ with
  | error reason =>
    rw [decoded] at tag
    cases reason <;> simp_all [PCIHeaderObservation.Error.code]
  | ok header =>
    refine ⟨header, rfl, ?_⟩
    apply matches_entry index bus device fn (PCIHeaderObservation.Scalar.query 1 16 bus device fn w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15)
      (PCIHeaderObservation.Scalar.query 2 16 bus device fn w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15)
      (PCIHeaderObservation.Scalar.query 3 16 bus device fn w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15)
      (PCIHeaderObservation.Scalar.query 7 16 bus device fn w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15)
      (PCIHeaderObservation.Scalar.query 8 16 bus device fn w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15)
      (PCIHeaderObservation.Scalar.query 9 16 bus device fn w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15)
      (PCIHeaderObservation.Scalar.query 10 16 bus device fn w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15)
      (PCIHeaderObservation.Scalar.query 11 16 bus device fn w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15)
      (PCIHeaderObservation.Scalar.query 12 16 bus device fn w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15) (project header) ?_ matched.2
    simp only [PCIHeaderObservation.Scalar.query_eq_observe]
    exact (observed_entry_words _ header decoded).symm

/-- Stable freestanding boundary: one means this raw header matches its native
inventory slot; zero rejects. It grants no platform or DMA authority. -/
@[export leanos_qotom_native_pci_header_check]
def exportedCheckHeader (index bus device fn w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : UInt64) : UInt64 :=
  if checkHeader index bus device fn w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 then 1 else 0

theorem exported_check_iff (index bus device fn w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : UInt64) :
    exportedCheckHeader index bus device fn w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 = 1 ↔ checkHeader index bus device fn w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 = true := by
  simp [exportedCheckHeader]

end LeanOS.QotomNativePCIFields
