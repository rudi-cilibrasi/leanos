/-!
Optional early EGA text-surface geometry. The bootloader must advertise the
surface, and the caller must still own the initial identity mapping and the
legacy text aperture. This selector does not establish monitor presence,
firmware honesty, PCI decode state, or authority after a root/device change.
-/
namespace LeanOS.BootTextConsole

structure Surface where
  kind : UInt64
  bits : UInt64
  address : UInt64
  pitch : UInt64
  width : UInt64
  height : UInt64
  deriving DecidableEq, Repr

/-- Initial color-text aperture only. Unsupported graphics formats are optional
absence, never a reason to prevent serial boot. Bounds avoid multiplication or
address overflow in the freestanding writer. -/
@[inline] def valid (s : Surface) : Bool :=
  s.kind == 2 && s.bits == 16 && s.address == 0xb8000 &&
  0 < s.width && s.width ≤ 160 && 0 < s.height && s.height ≤ 64 &&
  s.pitch % 2 == 0 && 2 * s.width ≤ s.pitch && s.pitch ≤ 512

@[export leanos_boot_text_surface]
def checkRaw (kind bits address pitch width height : UInt64) : UInt64 :=
  if valid ⟨kind, bits, address, pitch, width, height⟩ then 1 else 0

theorem accepted_geometry s (h : valid s = true) :
    s.kind = 2 ∧ s.bits = 16 ∧ s.address = 0xb8000 ∧
    0 < s.width ∧ s.width ≤ 160 ∧ 0 < s.height ∧ s.height ≤ 64 ∧
    s.pitch % 2 = 0 ∧ 2 * s.width ≤ s.pitch ∧ s.pitch ≤ 512 := by
  simpa [valid, and_assoc] using h

/-- Every cell is also inside the advertised pitch-times-height extent. -/
theorem cell_inside_surface s row column (h : valid s = true)
    (hr : row < s.height.toNat) (hc : column < s.width.toNat) :
    row * s.pitch.toNat + 2 * column + 2 ≤ s.height.toNat * s.pitch.toNat := by
  obtain ⟨_, _, _, _, hw, _, _, _, hpw, _⟩ := accepted_geometry s h
  have hwN : s.width.toNat ≤ 160 := by exact_mod_cast hw
  have hm : (2 * s.width).toNat = 2 * s.width.toNat := by
    rw [UInt64.toNat_mul]
    change 2 * s.width.toNat % 2 ^ 64 = 2 * s.width.toNat
    apply Nat.mod_eq_of_lt
    omega
  have hpwN := UInt64.le_iff_toNat_le.mp hpw
  rw [hm] at hpwN
  have hcell : 2 * column + 2 ≤ s.pitch.toNat := by omega
  have hrow : row + 1 ≤ s.height.toNat := by omega
  have hmul := Nat.mul_le_mul_right s.pitch.toNat hrow
  rw [Nat.add_mul] at hmul
  omega

/-- A character cell's two bytes lie inside the 32 KiB text aperture. The
arithmetic is stated over naturals so the proof includes absence of wrapping. -/
theorem cell_inside_aperture s row column (h : valid s = true)
    (hr : row < s.height.toNat) (hc : column < s.width.toNat) :
    row * s.pitch.toNat + 2 * column + 2 ≤ 32768 := by
  obtain ⟨_, _, _, hw0, hw, hh0, hh, _, hpw, hp⟩ := accepted_geometry s h
  have hwN : s.width.toNat ≤ 160 := by exact_mod_cast hw
  have hhN : s.height.toNat ≤ 64 := by exact_mod_cast hh
  have hpN : s.pitch.toNat ≤ 512 := by exact_mod_cast hp
  have hrow : row ≤ 63 := by omega
  have hcol : column ≤ 159 := by omega
  have hm := Nat.mul_le_mul hrow hpN
  omega

end LeanOS.BootTextConsole
