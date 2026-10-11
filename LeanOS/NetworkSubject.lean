import LeanOS.KeyboardEcho

/-!
# The ring-3 network subject's frame endpoint (issue #450)

The WiFi driver subject holds the device capability for the NIC; the bound
device program receives frames and transmits replies. The network subject,
a separate ring-3 subject, answers ARP, ICMP echo and UDP echo
(`LeanOS.Net.Echo`) and holds no device capability. Frames cross between
them through a *frame endpoint* whose payload does not fit the two-word IPC
message, so the kernel copies them:

* The driver program leaves a received frame in its executor scratch and
  yields its length (`deliver`). The driver subject sends the length and a
  sequence number to the network subject over the verified blocking IPC; it
  never reads the frame.
* The network subject asks the kernel to copy the pending frame into a
  buffer of its own (`fetch`), computes the reply in place, and asks the
  kernel to copy the reply out (`send`). The kernel accepts either only from
  the endpoint's holder, the network subject, and only when the whole
  buffer range lies inside the holder's own writable memory, the window
  [`base`, `limit`) (on q35 its stack page, through the SMAP user-copy
  window; on the Qotom through the bounded copy roots).
* The driver program takes the reply from scratch and transmits it
  (`transmit`). Subjects change their own memory with ordinary stores
  (`write`).

The theorems prove the confinement the issue asks for:

* **Only the holder reaches frames**: a `fetch` or `send` by any other
  subject is refused and changes nothing (`nonholder_refused`).
* **Its own buffer only**: across any run, a byte of a subject's memory
  changes only by that subject's own store, or, for the network subject,
  by an endpoint copy into its window (`step_mem_changed`,
  `run_mem_outside_window`): the kernel never writes frame bytes into the
  driver subject, a third subject, or the network subject outside its
  window.
* **Frames cross only through the endpoint**: the endpoint's receive slot
  changes only when the driver program delivers a frame, and its transmit
  slot only by the network subject's accepted `send`, which carries exactly
  bytes of its window, or by the driver program taking it
  (`step_rx_changed`, `step_tx_changed`).
* **No device authority**: the network subject is never granted a device
  capability, so every device program `bind` or `invoke` it attempts is
  denied without effect (`network_no_device_effects`, from
  `DeviceCapability.ungranted_subject_no_device_effects`).
* **The kernel's check**: the allocation-free witness `frameCopyCheck`
  (exported as `leanos_frame_copy_check`), which the kernel calls on every
  copy request, accepts exactly the requests `step` accepts
  (`frameCopyCheck_fetch`, `frameCopyCheck_send`) and refuses every other
  subject (`frameCopyCheck_nonholder`).

Not modelled: the ring-3 code, the IPC exchange (checked separately against
`leanos_blocking_ipc_event`), the device program's radio, scheduling and the
executor. The booted kernel is tested, not proved, against this model.
-/

namespace LeanOS.NetworkSubject

/-- Subject codes of the boot images: the driver subject A, a subject B that
holds nothing, and the network subject C (`ConsoleServer.subjectCode`). -/
def driver : Nat := 1
def network : Nat := 3

/-- Ethernet II frame bounds (no FCS). -/
def minFrame : Nat := 14
def maxFrame : Nat := 1514

/-- The network subject's own writable memory, `[base, limit)`. -/
structure Window where
  base : Nat
  limit : Nat
  deriving Repr, DecidableEq

/-- `len` bytes at `addr` lie inside the window. -/
def Window.covers (w : Window) (addr len : Nat) : Bool :=
  w.base ≤ addr && addr + len ≤ w.limit

/-- Address `a` lies inside the window. -/
def Window.contains (w : Window) (a : Nat) : Prop := w.base ≤ a ∧ a < w.limit

/-- Each subject's memory and the endpoint's two slots in executor scratch. -/
structure State where
  mem : Nat → Nat → UInt8
  rx : List UInt8
  rxPending : Bool
  tx : List UInt8
  txPending : Bool

inductive Op where
  /-- The driver program leaves a received frame in scratch and yields. -/
  | deliver (frame : List UInt8)
  /-- `who` asks the kernel to copy the pending frame to `addr`. -/
  | fetch (who addr : Nat)
  /-- `who` asks the kernel to copy `len` bytes at `addr` out as the reply. -/
  | send (who addr len : Nat)
  /-- The driver program takes the reply and transmits it. -/
  | transmit
  /-- `who` stores `bytes` at `addr` in its own memory. -/
  | write (who addr : Nat) (bytes : List UInt8)

inductive Reply where
  | accepted (n : Nat)
  | refused
  deriving DecidableEq, Repr

/-- `bytes` written at `addr` over memory `m`. -/
def writeBytes (m : Nat → UInt8) (addr : Nat) (bytes : List UInt8) : Nat → UInt8 :=
  fun a => if addr ≤ a ∧ a < addr + bytes.length then bytes.getD (a - addr) 0 else m a

/-- `len` bytes of `m` at `addr`. -/
def readBytes (m : Nat → UInt8) (addr len : Nat) : List UInt8 :=
  (List.range len).map fun i => m (addr + i)

/-- `m` with subject `who`'s memory replaced by `f`. -/
def update (m : Nat → Nat → UInt8) (who : Nat) (f : Nat → UInt8) : Nat → Nat → UInt8 :=
  fun x => if x = who then f else m x

/-- The fetch the kernel accepts: from the holder, with a frame pending, into
a range of its window. -/
def fetchOk (w : Window) (s : State) (who addr : Nat) : Bool :=
  who == network && s.rxPending && s.rx.length ≤ maxFrame && w.covers addr s.rx.length

/-- The send the kernel accepts: from the holder, no reply pending, a frame
length, from a range of its window. -/
def sendOk (w : Window) (s : State) (who addr len : Nat) : Bool :=
  who == network && !s.txPending && minFrame ≤ len && len ≤ maxFrame && w.covers addr len

/-- One endpoint transition. -/
def step (w : Window) (s : State) : Op → State × Reply
  | .deliver f =>
    if !s.rxPending && f.length ≤ maxFrame then
      ({ s with rx := f, rxPending := true }, .accepted f.length)
    else (s, .refused)
  | .fetch who addr =>
    if fetchOk w s who addr then
      ({ s with mem := update s.mem network (writeBytes (s.mem network) addr s.rx),
                rxPending := false }, .accepted s.rx.length)
    else (s, .refused)
  | .send who addr len =>
    if sendOk w s who addr len then
      ({ s with tx := readBytes (s.mem network) addr len, txPending := true }, .accepted 0)
    else (s, .refused)
  | .transmit => ({ s with tx := [], txPending := false }, .accepted s.tx.length)
  | .write who addr bytes =>
    ({ s with mem := update s.mem who (writeBytes (s.mem who) addr bytes) }, .accepted 0)

/-- Run a list of transitions. -/
def run (w : Window) (s : State) : List Op → State
  | [] => s
  | op :: ops => run w (step w s op).1 ops

/-! ## Only the holder reaches frames -/

/-- A `fetch` or `send` by a subject other than the network subject is
refused and changes nothing. -/
theorem nonholder_refused (w : Window) (s : State) (who : Nat) (h : who ≠ network) :
    (∀ addr, step w s (.fetch who addr) = (s, .refused)) ∧
    (∀ addr len, step w s (.send who addr len) = (s, .refused)) := by
  have hb : (who == network) = false := by simpa using h
  constructor
  · intro addr; simp [step, fetchOk, hb]
  · intro addr len; simp [step, sendOk, hb]

/-! ## Its own buffer only -/

theorem writeBytes_outside (m : Nat → UInt8) (addr : Nat) (bytes : List UInt8) (a : Nat)
    (h : ¬(addr ≤ a ∧ a < addr + bytes.length)) : writeBytes m addr bytes a = m a := by
  simp [writeBytes, h]

/-- A changed byte of any subject's memory is that subject's own store, or
an accepted endpoint copy into the network subject's window. -/
theorem step_mem_changed (w : Window) (s : State) (op : Op) (x a : Nat)
    (h : (step w s op).1.mem x a ≠ s.mem x a) :
    (∃ addr bytes, op = .write x addr bytes) ∨
    (x = network ∧ w.contains a ∧ ∃ addr, op = .fetch network addr) := by
  cases op with
  | deliver f =>
    simp only [step] at h; split at h <;> exact absurd rfl h
  | send who addr len =>
    simp only [step] at h; split at h <;> exact absurd rfl h
  | transmit => exact absurd rfl h
  | write who addr bytes =>
    simp only [step, update] at h
    by_cases hx : x = who
    · subst hx; exact Or.inl ⟨addr, bytes, rfl⟩
    · simp [hx] at h
  | fetch who addr =>
    simp only [step] at h
    split at h
    · rename_i hok
      simp only [fetchOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
        Window.covers] at hok
      obtain ⟨⟨⟨hwho, -⟩, -⟩, hb, hl⟩ := hok
      simp only [update] at h
      by_cases hx : x = network
      · subst hx
        simp only [↓reduceIte] at h
        by_cases hin : addr ≤ a ∧ a < addr + s.rx.length
        · refine Or.inr ⟨rfl, ⟨by omega, by omega⟩, addr, by rw [hwho]⟩
        · exact absurd (writeBytes_outside _ _ _ _ hin) h
      · simp [hx] at h
    · exact absurd rfl h

/-- Across any run, memory that no store of its owner touched changes only
inside the network subject's window: outside it, the kernel never writes a
frame byte into any subject. -/
theorem run_mem_outside_window (w : Window) :
    ∀ (s : State) (ops : List Op) (x a : Nat),
      (∀ op ∈ ops, ∀ addr bytes, op ≠ .write x addr bytes) →
      ¬(x = network ∧ w.contains a) →
      (run w s ops).mem x a = s.mem x a
  | _, [], _, _, _, _ => rfl
  | s, op :: ops, x, a, hw, hout => by
    simp only [run]
    rw [run_mem_outside_window w (step w s op).1 ops x a
      (fun op' hmem => hw op' (List.mem_cons_of_mem _ hmem)) hout]
    by_cases hc : (step w s op).1.mem x a = s.mem x a
    · exact hc
    · rcases step_mem_changed w s op x a hc with ⟨addr, bytes, hop⟩ | ⟨hx, hin, -⟩
      · exact absurd hop (hw op (List.mem_cons_self ..) addr bytes)
      · exact absurd ⟨hx, hin⟩ hout

/-- In particular the driver subject's memory changes only by its own
stores: it never receives a frame byte from the endpoint. -/
theorem run_driver_mem (w : Window) (s : State) (ops : List Op) (a : Nat)
    (hw : ∀ op ∈ ops, ∀ addr bytes, op ≠ .write driver addr bytes) :
    (run w s ops).mem driver a = s.mem driver a :=
  run_mem_outside_window w s ops driver a hw (by simp [driver, network])

/-! ## Frames cross only through the endpoint -/

/-- The receive slot changes only when the driver program delivers. -/
theorem step_rx_changed (w : Window) (s : State) (op : Op)
    (h : (step w s op).1.rx ≠ s.rx) : ∃ f, op = .deliver f ∧ (step w s op).1.rx = f := by
  cases op with
  | deliver f =>
    refine ⟨f, rfl, ?_⟩
    simp only [step] at h ⊢
    split
    · rfl
    · rename_i hn; simp only [hn] at h; exact absurd rfl h
  | fetch who addr => simp only [step] at h; split at h <;> exact absurd rfl h
  | send who addr len => simp only [step] at h; split at h <;> exact absurd rfl h
  | transmit => exact absurd rfl h
  | write => exact absurd rfl h

/-- The transmit slot changes only by the network subject's accepted send,
which carries exactly bytes of its window, or by the driver program taking
the reply. -/
theorem step_tx_changed (w : Window) (s : State) (op : Op)
    (h : (step w s op).1.tx ≠ s.tx) :
    op = .transmit ∨
    ∃ addr len, op = .send network addr len ∧ w.covers addr len = true ∧
      (step w s op).1.tx = readBytes (s.mem network) addr len := by
  cases op with
  | deliver f => simp only [step] at h; split at h <;> exact absurd rfl h
  | fetch who addr => simp only [step] at h; split at h <;> exact absurd rfl h
  | transmit => exact Or.inl rfl
  | write => exact absurd rfl h
  | send who addr len =>
    simp only [step] at h ⊢
    split at h
    · rename_i hok
      have hok' := hok
      simp only [sendOk, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not,
        Bool.not_true, decide_eq_true_eq] at hok'
      obtain ⟨⟨⟨⟨hwho, -⟩, -⟩, -⟩, hcov⟩ := hok'
      subst hwho
      exact Or.inr ⟨addr, len, rfl, hcov, by simp [hok]⟩
    · exact absurd rfl h

/-! ## No device authority -/

/-- The network subject is never granted a device capability: after any
device run without a grant to it, each `bind` or `invoke` it attempts is
denied and leaves the device system, every device's state included,
unchanged. The installed device authority is the keyboard-echo image's
(`KeyboardEcho.bootDeviceCaps`: only the driver subject holds device 0). -/
theorem network_no_device_effects {σ} (models : Nat → Wifi.Sim.Device σ)
    (sys : DeviceCapability.System σ) (hcaps : sys.deviceCaps = KeyboardEcho.bootDeviceCaps)
    (ts : List DeviceCapability.Transition)
    (hg : ∀ d, DeviceCapability.Transition.grant network d ∉ ts) :
    (∀ program, DeviceCapability.step models (DeviceCapability.run models sys ts)
        (.bind network program) = (DeviceCapability.run models sys ts, .denied)) ∧
    (∀ fuel, DeviceCapability.step models (DeviceCapability.run models sys ts)
        (.invoke network fuel) = (DeviceCapability.run models sys ts, .denied)) :=
  DeviceCapability.ungranted_subject_no_device_effects models sys network ts
    (by rw [hcaps]; decide) hg

/-- The generated device witness the kernel checks refuses the network
subject every device. -/
theorem deviceAuthorize_network (device : UInt64) :
    KeyboardEcho.deviceAuthorize (network.toUInt64) device = ConsoleServer.refuseCode := by
  simp [KeyboardEcho.deviceAuthorize, network, ConsoleServer.refuseCode]

/-! ## The kernel's generated check -/

/-- Operation codes of `frameCopyDecide`. -/
def opFetch : UInt64 := 1
def opSend : UInt64 := 2

/-- Range check without overflow: `[addr, addr + len)` inside
`[base, limit)`. -/
@[inline] def rangeOk (addr len base limit : UInt64) : Bool :=
  base ≤ addr && addr ≤ limit && len ≤ limit - addr

/-- The decision behind `frameCopyCheck`: 0 accepts; 1 the caller is not the endpoint holder; 2
the endpoint is in the wrong state (no frame pending for a fetch, a reply
already pending for a send); 3 a length outside the frame bounds; 4 a range
outside the window; 5 an unknown operation. `pending` is 1 when the slot the
operation needs is full. -/
def frameCopyDecide (subject op addr len pending base limit : UInt64) : UInt64 :=
  if subject != 3 then 1
  else if op == 1 then
    if pending != 1 then 2
    else if len > 1514 then 3
    else if rangeOk addr len base limit then 0 else 4
  else if op == 2 then
    if pending != 0 then 2
    else if len < 14 || len > 1514 then 3
    else if rangeOk addr len base limit then 0 else 4
  else 5

theorem rangeOk_iff (addr len base limit : UInt64) :
    rangeOk addr len base limit = true ↔
      (Window.covers ⟨base.toNat, limit.toNat⟩ addr.toNat len.toNat = true) := by
  simp only [rangeOk, Window.covers, Bool.and_eq_true, decide_eq_true_eq,
    UInt64.le_iff_toNat_le]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr h2)] at h3
    omega
  · rintro ⟨h1, h2⟩
    have h2' : addr.toNat ≤ limit.toNat := by omega
    refine ⟨⟨h1, h2'⟩, ?_⟩
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr h2')]
    omega

theorem gt1514_iff (len : UInt64) : len > 1514 ↔ ¬ len.toNat ≤ maxFrame := by
  rw [gt_iff_lt, UInt64.lt_iff_toNat_lt]; simp [maxFrame]

theorem lt14_iff (len : UInt64) : len < 14 ↔ ¬ minFrame ≤ len.toNat := by
  rw [UInt64.lt_iff_toNat_lt]; simp [minFrame]

/-- The witness accepts a fetch exactly from subject 3, with a frame pending,
of at most `maxFrame` bytes, into a range of the window `[base, limit)`. -/
theorem frameCopyDecide_fetch_iff (subject addr len pending base limit : UInt64) :
    frameCopyDecide subject opFetch addr len pending base limit = 0 ↔
      subject = 3 ∧ pending = 1 ∧ len.toNat ≤ maxFrame ∧
        Window.covers ⟨base.toNat, limit.toNat⟩ addr.toNat len.toNat = true := by
  rw [← rangeOk_iff]
  unfold frameCopyDecide opFetch
  by_cases hs : subject = 3
  · subst hs
    by_cases hp : pending = 1
    · subst hp
      by_cases hl : len > 1514
      · have := (gt1514_iff len).mp hl
        simp [hl, this]
      · have hle : len.toNat ≤ maxFrame :=
          Classical.not_not.mp (fun h => hl ((gt1514_iff len).mpr h))
        simp only [hl, hle, ite_false, bne_self_eq_false, Bool.false_eq_true,
          beq_self_eq_true, ite_true, bne_iff_ne, ne_eq, true_and]
        split <;> simp_all
    · simp [hp]
  · simp [hs]

/-- The witness accepts a send exactly from subject 3, with no reply pending,
of a frame length, from a range of the window `[base, limit)`. -/
theorem frameCopyDecide_send_iff (subject addr len pending base limit : UInt64) :
    frameCopyDecide subject opSend addr len pending base limit = 0 ↔
      subject = 3 ∧ pending = 0 ∧ minFrame ≤ len.toNat ∧ len.toNat ≤ maxFrame ∧
        Window.covers ⟨base.toNat, limit.toNat⟩ addr.toNat len.toNat = true := by
  rw [← rangeOk_iff]
  unfold frameCopyDecide opSend
  by_cases hs : subject = 3
  · subst hs
    by_cases hp : pending = 0
    · subst hp
      by_cases h14 : len < 14
      · have := (lt14_iff len).mp h14
        simp [h14, this]
      · by_cases h1514 : len > 1514
        · have := (gt1514_iff len).mp h1514
          simp [h14, h1514, this]
        · have hmin : minFrame ≤ len.toNat :=
            Classical.not_not.mp (fun h => h14 ((lt14_iff len).mpr h))
          have hmax : len.toNat ≤ maxFrame :=
            Classical.not_not.mp (fun h => h1514 ((gt1514_iff len).mpr h))
          simp only [h14, h1514, hmin, hmax, decide_false, Bool.or_false, ite_false,
            bne_self_eq_false, Bool.false_eq_true, true_and]
          split <;> simp_all
    · simp [hp]
  · simp [hs]

/-- For the network subject, the witness accepts a fetch exactly when the
model's `fetchOk` does, given the pending flag and the pending frame's length. -/
theorem frameCopyDecide_fetch (w : Window) (s : State) (addr base limit : UInt64)
    (hw : w = ⟨base.toNat, limit.toNat⟩) (hlen : s.rx.length < 2 ^ 64) :
    frameCopyDecide 3 opFetch addr s.rx.length.toUInt64
        (if s.rxPending then 1 else 0) base limit = 0 ↔
      fetchOk w s network addr.toNat = true := by
  subst hw
  have hl : (s.rx.length.toUInt64).toNat = s.rx.length := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt hlen
  rw [frameCopyDecide_fetch_iff, hl]
  cases hp : s.rxPending <;> simp [fetchOk, network, hp]

/-- For the network subject, the witness accepts a send exactly when the
model's `sendOk` does, given the pending flag. -/
theorem frameCopyDecide_send (w : Window) (s : State) (addr len base limit : UInt64)
    (hw : w = ⟨base.toNat, limit.toNat⟩) :
    frameCopyDecide 3 opSend addr len (if s.txPending then 1 else 0) base limit = 0 ↔
      sendOk w s network addr.toNat len.toNat = true := by
  subst hw
  rw [frameCopyDecide_send_iff]
  cases hp : s.txPending <;> simp [sendOk, network, hp, and_assoc]

/-- Every other subject is refused by the witness whatever it asks. -/
theorem frameCopyDecide_nonholder (subject op addr len pending base limit : UInt64)
    (h : subject ≠ 3) : frameCopyDecide subject op addr len pending base limit = 1 := by
  simp [frameCopyDecide, h]

/-! ### The exported witness

The kernel passes the operation and the slot's state in one request word,
`op ||| pending <<< 8`, so the witness has the six fixed-width arguments
every boot export may take. -/

/-- The request word of a fetch (`pending`: a frame is waiting). -/
def fetchRequest (pending : Bool) : UInt64 := if pending then 0x101 else 0x001

/-- The request word of a send (`pending`: a reply is already waiting). -/
def sendRequest (pending : Bool) : UInt64 := if pending then 0x102 else 0x002

/-- Allocation-free witness of `fetchOk`/`sendOk`, exported as
`leanos_frame_copy_check`, which the kernel calls on every frame copy request
(`subject`, the request word, the buffer address and length, and the
holder's window `[base, limit)`); 0 accepts, any other value is
`frameCopyDecide`'s reason. -/
@[export leanos_frame_copy_check]
def frameCopyCheck (subject request addr len base limit : UInt64) : UInt64 :=
  frameCopyDecide subject (request &&& 0xff) addr len (request >>> 8) base limit

theorem frameCopyCheck_fetchRequest (subject addr len base limit : UInt64) (p : Bool) :
    frameCopyCheck subject (fetchRequest p) addr len base limit =
      frameCopyDecide subject opFetch addr len (if p then 1 else 0) base limit := by
  cases p <;> rfl

theorem frameCopyCheck_sendRequest (subject addr len base limit : UInt64) (p : Bool) :
    frameCopyCheck subject (sendRequest p) addr len base limit =
      frameCopyDecide subject opSend addr len (if p then 1 else 0) base limit := by
  cases p <;> rfl

/-- The exported witness accepts the network subject's fetch exactly when the
model's `fetchOk` does. -/
theorem frameCopyCheck_fetch (w : Window) (s : State) (addr base limit : UInt64)
    (hw : w = ⟨base.toNat, limit.toNat⟩) (hlen : s.rx.length < 2 ^ 64) :
    frameCopyCheck 3 (fetchRequest s.rxPending) addr s.rx.length.toUInt64 base limit = 0 ↔
      fetchOk w s network addr.toNat = true := by
  rw [frameCopyCheck_fetchRequest]; exact frameCopyDecide_fetch w s addr base limit hw hlen

/-- The exported witness accepts the network subject's send exactly when the
model's `sendOk` does. -/
theorem frameCopyCheck_send (w : Window) (s : State) (addr len base limit : UInt64)
    (hw : w = ⟨base.toNat, limit.toNat⟩) :
    frameCopyCheck 3 (sendRequest s.txPending) addr len base limit = 0 ↔
      sendOk w s network addr.toNat len.toNat = true := by
  rw [frameCopyCheck_sendRequest]; exact frameCopyDecide_send w s addr len base limit hw

/-- Every other subject is refused by the exported witness whatever it asks. -/
theorem frameCopyCheck_nonholder (subject request addr len base limit : UInt64)
    (h : subject ≠ 3) : frameCopyCheck subject request addr len base limit = 1 :=
  frameCopyDecide_nonholder subject _ addr len _ base limit h

end LeanOS.NetworkSubject
