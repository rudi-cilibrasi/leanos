/-!
# Group-key rotation in the WiFi driver (issue #557)

An access point rotates its group temporal key (GTK) every few minutes or
hours. It sends each associated station an EAPOL-Key **group message 1**
(IEEE 802.11-2016 12.7.7), protected by the station's pairwise key (TK) and
carrying the new GTK wrapped with the KEK, an EAPOL replay counter and the
new key's receive sequence counter (Key RSC). The station answers with
**group message 2** and from then on decrypts broadcast and multicast frames
with the new key, whose key id alternates between 1 and 2.

The BCM43224 driver program keeps this exchange to itself
(`LeanOS.Wifi.Responder.respond.groupKey`, used by both the ring-0 responder
and the frame endpoint `LeanOS.Wifi.Endpoint.handleFrame`): the ring-3
network subjects never see a key. This module models what the program does
with one received protected data frame, with the key material abstract (two
keys are the same exactly when they are equal):

* **Decapsulation** (`DevCcmp.ccmpDecap`): key id 0 selects the TK, the
  installed GTK's key id selects the GTK, any other key id is dropped; a
  frame protected with other key material fails its MIC.
* **Replay check** (`Responder.replayCheck`): the frame's packet number must
  exceed the last one accepted under that key (pairwise or group), and is
  then recorded.
* **Group message 1** (`Responder.respond.groupKey`): accepted only with an
  EAPOL replay counter above the last one and a valid MIC, which then
  advances the counter; with an unwrapped GTK of key id 1–3
  (`Handshake.installGtk`) it installs the key, seeds its packet-number floor
  from the Key RSC and answers with message 2 echoing the counter.
* **Data**: delivered (to the frame endpoint, or answered by the ring-0
  responder).

What is proved:

* **Replay-counter monotonicity across rekeys**: no step lowers the EAPOL
  replay counter (`step_replay_mono`, `run_replay_mono`); every message 2
  echoes a counter above every earlier one (`msg2_replay`, `run_msg2_gt`),
  so across any run the answered counters strictly increase
  (`run_msg2_sorted`) and a group message is answered at most once
  (`msg2_once`).
* **Packet-number monotonicity**: a delivered frame's packet number exceeds
  the last one accepted under its key and becomes the new floor
  (`deliver_pn`); the pairwise floor never decreases (`step_pnTk_mono`), and
  the group floor never decreases except when a new GTK is installed
  (`step_pnGtk_mono`), when it becomes that key's Key RSC (`msg2_installs`).
* **Key-id rollover**: an answered message 1 installs exactly its key and
  key id, never key id 0 (`msg2_installs`); a frame under the new key id and
  key with a packet number above the Key RSC is delivered
  (`delivered_after_rekey`), while a frame under the previous key id
  (`stale_id_dropped`), under stale material for the new key id
  (`stale_material_dropped`) or with a packet number at or below the floor
  (`replayed_pn_dropped`) is dropped without changing anything.
* **The q35 fixture**: the frame sequence of the `gtk-rekey` scenario
  rotates the key 1 → 2 → 1 and has exactly the outcomes its transcript
  shows (`scenario_outcomes`); `LeanOS.Net.RekeySource` builds its frames
  and checks the program's behaviour against these outcomes.

Not modelled: the cryptography (`tests/WifiDevCcmp.lean`,
`tests/WifiDevCrypto.lean` check it against the reference library), frame
parsing, and the device. The program is tested, not proved, against this
model: `tests/WifiRekeySim.lean` runs the device program in the simulator on
random frame sequences and requires the model's outcome for every frame.
-/

namespace LeanOS.GtkRekey

/-- Abstract key material. -/
abbrev Key := Nat

/-- The driver's key state. -/
structure State where
  /-- The pairwise key (from the 4-way handshake; never rotated here). -/
  tk : Key
  /-- The installed group key and its key id. -/
  gtk : Key
  gtkId : Nat
  /-- The last EAPOL replay counter accepted. -/
  replay : Nat
  /-- The last packet number accepted under the TK and under the GTK. -/
  pnTk : Nat
  pnGtk : Nat
  deriving DecidableEq, Repr

/-- A group message 1 as the program sees it once decapsulated: its replay
counter, whether its MIC verifies under the KCK, whether its key data
unwraps under the KEK to a GTK KDE, and that KDE's key id, key and Key RSC. -/
structure GroupMsg1 where
  replay : Nat
  micOk : Bool
  unwrapOk : Bool
  keyId : Nat
  gtk : Key
  rsc : Nat
  deriving DecidableEq, Repr

inductive Body where
  | groupMsg1 (m : GroupMsg1)
  | data (payload : Nat)
  deriving DecidableEq, Repr

/-- A received protected data frame from the BSSID: the key id of its CCMP
header, the key material it was actually protected with, its packet number
and its body. -/
structure Frame where
  keyId : Nat
  key : Key
  pn : Nat
  body : Body
  deriving DecidableEq, Repr

inductive Drop where
  /-- No key for the key id: neither 0 nor the installed GTK's. -/
  | unknownKey
  /-- The CCMP MIC fails: other key material. -/
  | mic
  /-- The packet number is at or below the last one accepted. -/
  | replayedPn
  /-- A group message 1 whose replay counter is not above the last one. -/
  | replayedCounter
  /-- A group message 1 whose EAPOL MIC fails. -/
  | groupMic
  /-- A group message 1 without a usable GTK (unwrap or KDE, key id 0). -/
  | noGtk
  deriving DecidableEq, Repr

inductive Out where
  | deliver (payload : Nat)
  | msg2 (replay : Nat)
  | drop (why : Drop)
  deriving DecidableEq, Repr

/-- The key decapsulation uses for key id `id`. -/
def keyFor (s : State) (id : Nat) : Option Key :=
  if id = 0 then some s.tk else if id = s.gtkId then some s.gtk else none

/-- The last packet number accepted under key id `id`'s key. -/
def lastPn (s : State) (id : Nat) : Nat := if id = 0 then s.pnTk else s.pnGtk

def recordPn (s : State) (id pn : Nat) : State :=
  if id = 0 then { s with pnTk := pn } else { s with pnGtk := pn }

/-- Key ids a GTK may take: the KDE's two bits, never 0 (the TK's). -/
def gtkIdOk (id : Nat) : Bool := id == 1 || id == 2 || id == 3

/-- Group message 1, once its frame passed decapsulation and the replay
check. -/
def group (s : State) (m : GroupMsg1) : State × Out :=
  if m.replay ≤ s.replay then (s, .drop .replayedCounter)
  else if !m.micOk then (s, .drop .groupMic)
  else
    let s := { s with replay := m.replay }
    if !m.unwrapOk || !gtkIdOk m.keyId then (s, .drop .noGtk)
    else ({ s with gtk := m.gtk, gtkId := m.keyId, pnGtk := m.rsc }, .msg2 m.replay)

/-- One received frame. -/
def step (s : State) (f : Frame) : State × Out :=
  match keyFor s f.keyId with
  | none => (s, .drop .unknownKey)
  | some k =>
    if k ≠ f.key then (s, .drop .mic)
    else if f.pn ≤ lastPn s f.keyId then (s, .drop .replayedPn)
    else
      match f.body with
      | .groupMsg1 m => group (recordPn s f.keyId f.pn) m
      | .data p => (recordPn s f.keyId f.pn, .deliver p)

/-- A run over a sequence of frames: the final state and every outcome. -/
def run : State → List Frame → State × List Out
  | s, [] => (s, [])
  | s, f :: fs => ((run (step s f).1 fs).1, (step s f).2 :: (run (step s f).1 fs).2)

/-- The replay counters a list of outcomes answers with message 2. -/
def msg2s : List Out → List Nat
  | [] => []
  | .msg2 r :: os => r :: msg2s os
  | _ :: os => msg2s os

/-- The frame passes decapsulation and the replay check. -/
def Accepts (s : State) (f : Frame) : Prop :=
  keyFor s f.keyId = some f.key ∧ lastPn s f.keyId < f.pn

theorem step_rejects (s : State) (f : Frame) (h : ¬ Accepts s f) :
    ∃ d, step s f = (s, .drop d) := by
  unfold step
  cases hk : keyFor s f.keyId with
  | none => exact ⟨_, rfl⟩
  | some k =>
    by_cases hkey : k = f.key
    · subst hkey
      have : f.pn ≤ lastPn s f.keyId := by
        unfold Accepts at h; rw [hk] at h
        exact Nat.le_of_not_lt fun hl => h ⟨rfl, hl⟩
      simp only [ne_eq, not_true_eq_false, ite_false, ite_true, this]
      exact ⟨_, rfl⟩
    · simp only [ne_eq, hkey, not_false_eq_true, ite_true]
      exact ⟨_, rfl⟩

theorem step_unknown (s : State) (g : Frame) (hk : keyFor s g.keyId = none) :
    step s g = (s, .drop .unknownKey) := by
  unfold step; rw [hk]

theorem step_mic (s : State) (g : Frame) (k : Key) (hk : keyFor s g.keyId = some k)
    (hne : k ≠ g.key) : step s g = (s, .drop .mic) := by
  unfold step; rw [hk]; simp only [ne_eq, hne, not_false_eq_true, ↓reduceIte]

theorem step_accepts (s : State) (f : Frame) (h : Accepts s f) :
    step s f = match f.body with
      | .groupMsg1 m => group (recordPn s f.keyId f.pn) m
      | .data p => (recordPn s f.keyId f.pn, .deliver p) := by
  unfold step
  rw [h.1]
  have : ¬ f.pn ≤ lastPn s f.keyId := by have := h.2; omega
  simp only [ne_eq, not_true_eq_false, ite_false, this]

/-! ## Replay-counter monotonicity -/

theorem recordPn_replay (s : State) (id pn : Nat) : (recordPn s id pn).replay = s.replay := by
  unfold recordPn; split <;> rfl

theorem recordPn_tk (s : State) (id pn : Nat) : (recordPn s id pn).tk = s.tk := by
  unfold recordPn; split <;> rfl

theorem group_msg2 (s : State) (m : GroupMsg1) (r : Nat) (h : (group s m).2 = .msg2 r) :
    r = m.replay ∧ s.replay < m.replay ∧ m.micOk = true ∧ m.unwrapOk = true ∧
      gtkIdOk m.keyId = true ∧
      (group s m).1 = { s with replay := m.replay, gtk := m.gtk, gtkId := m.keyId,
                                pnGtk := m.rsc } := by
  unfold group at h ⊢
  by_cases h1 : m.replay ≤ s.replay
  · simp only [h1, ite_true] at h; cases h
  · simp only [h1, ite_false] at h ⊢
    cases hmic : m.micOk
    · simp only [hmic, Bool.not_false, ite_true] at h; cases h
    · cases hun : m.unwrapOk
      · simp only [hmic, hun, Bool.not_true, Bool.not_false, Bool.true_or, ite_true,
          Bool.false_eq_true, ite_false] at h; cases h
      · cases hid : gtkIdOk m.keyId
        · simp only [hmic, hun, hid, Bool.not_true, Bool.not_false, Bool.or_true, ite_true,
            Bool.false_eq_true, ite_false] at h; cases h
        · simp only [hmic, hun, hid, Bool.not_true, Bool.or_false, Bool.false_eq_true,
            ite_false] at h ⊢
          cases h
          refine ⟨rfl, by omega, ?_, ?_, ?_, ?_⟩ <;> trivial

theorem group_replay_mono (s : State) (m : GroupMsg1) : s.replay ≤ (group s m).1.replay := by
  unfold group
  split
  · exact Nat.le_refl _
  · split
    · exact Nat.le_refl _
    · split <;> simp only <;> omega

/-- No step lowers the EAPOL replay counter. -/
theorem step_replay_mono (s : State) (f : Frame) : s.replay ≤ (step s f).1.replay := by
  by_cases h : Accepts s f
  · rw [step_accepts s f h]
    cases f.body with
    | groupMsg1 m =>
      have := group_replay_mono (recordPn s f.keyId f.pn) m
      rw [recordPn_replay] at this; exact this
    | data p => simp only [recordPn_replay]; exact Nat.le_refl _
  · obtain ⟨d, hd⟩ := step_rejects s f h
    rw [hd]; exact Nat.le_refl _

/-- Over any run, the replay counter never decreases. -/
theorem run_replay_mono (s : State) (fs : List Frame) : s.replay ≤ (run s fs).1.replay := by
  induction fs generalizing s with
  | nil => exact Nat.le_refl _
  | cons f fs ih => exact Nat.le_trans (step_replay_mono s f) (ih _)

/-- What an answered frame is: an accepted group message 1. -/
theorem step_msg2 (s : State) (f : Frame) (r : Nat) (h : (step s f).2 = .msg2 r) :
    Accepts s f ∧ ∃ m, f.body = .groupMsg1 m ∧
      (step s f) = group (recordPn s f.keyId f.pn) m := by
  by_cases ha : Accepts s f
  · refine ⟨ha, ?_⟩
    rw [step_accepts s f ha] at h ⊢
    cases hb : f.body with
    | groupMsg1 m => exact ⟨m, rfl, rfl⟩
    | data p => rw [hb] at h; cases h
  · obtain ⟨d, hd⟩ := step_rejects s f ha
    rw [hd] at h; cases h

/-- A message 2 echoes the message's replay counter, which is above the last
one accepted and becomes the new last one. -/
theorem msg2_replay (s : State) (f : Frame) (r : Nat) (h : (step s f).2 = .msg2 r) :
    s.replay < r ∧ (step s f).1.replay = r := by
  obtain ⟨-, m, -, hs⟩ := step_msg2 s f r h
  rw [hs] at h ⊢
  obtain ⟨hr, hlt, -, -, -, hg⟩ := group_msg2 _ m r h
  rw [recordPn_replay] at hlt
  rw [hg, hr]
  exact ⟨hlt, rfl⟩

/-- Every message 2 later in a run echoes a counter above the replay
counter at its start. -/
theorem run_msg2_gt (s : State) (fs : List Frame) :
    ∀ r ∈ msg2s (run s fs).2, s.replay < r := by
  induction fs generalizing s with
  | nil => intro r hr; simp [run, msg2s] at hr
  | cons f fs ih =>
    intro r hr
    have hmono := step_replay_mono s f
    simp only [run] at hr
    cases ho : (step s f).2 with
    | msg2 r0 =>
      rw [ho] at hr
      simp only [msg2s, List.mem_cons] at hr
      have hlt := (msg2_replay s f r0 ho).1
      rcases hr with rfl | hr
      · exact hlt
      · exact Nat.lt_of_le_of_lt hmono (ih _ r hr)
    | deliver p =>
      rw [ho] at hr; simp only [msg2s] at hr
      exact Nat.lt_of_le_of_lt hmono (ih _ r hr)
    | drop d =>
      rw [ho] at hr; simp only [msg2s] at hr
      exact Nat.lt_of_le_of_lt hmono (ih _ r hr)

/-- Across any run, including any number of rekeys, the replay counters
answered with message 2 strictly increase. -/
theorem run_msg2_sorted (s : State) (fs : List Frame) :
    (msg2s (run s fs).2).Pairwise (· < ·) := by
  induction fs generalizing s with
  | nil => simp [run, msg2s]
  | cons f fs ih =>
    simp only [run]
    cases ho : (step s f).2 with
    | msg2 r0 =>
      simp only [msg2s, List.pairwise_cons]
      refine ⟨fun r hr => ?_, ih _⟩
      have h := run_msg2_gt (step s f).1 fs r hr
      rw [(msg2_replay s f r0 ho).2] at h
      exact h
    | deliver p => simp only [msg2s]; exact ih _
    | drop d => simp only [msg2s]; exact ih _

/-- The same frame received again right after it was answered (the access
point's retransmission, or a replay) is not answered again. -/
theorem msg2_once (s : State) (f : Frame) (r : Nat) (h : (step s f).2 = .msg2 r) :
    ∃ d, (step (step s f).1 f).2 = .drop d := by
  have hs := msg2_replay s f r h
  obtain ⟨-, m, hb, hst⟩ := step_msg2 s f r h
  rw [hst] at h
  have hr := (group_msg2 _ m r h).1
  by_cases ha : Accepts (step s f).1 f
  · have hle : m.replay ≤ (recordPn (step s f).1 f.keyId f.pn).replay := by
      rw [recordPn_replay, hs.2, hr]; exact Nat.le_refl _
    rw [step_accepts _ f ha, hb]
    simp only [group, hle, ite_true]
    exact ⟨_, rfl⟩
  · obtain ⟨d, hd⟩ := step_rejects _ f ha
    rw [hd]; exact ⟨d, rfl⟩

/-! ## Packet-number monotonicity -/

theorem lastPn_recordPn (s : State) (id pn : Nat) : lastPn (recordPn s id pn) id = pn := by
  unfold lastPn recordPn; split <;> simp_all

/-- A delivered frame's packet number exceeds the last one accepted under
its key, and becomes the new floor. -/
theorem deliver_pn (s : State) (f : Frame) (p : Nat) (h : (step s f).2 = .deliver p) :
    f.body = .data p ∧ keyFor s f.keyId = some f.key ∧ lastPn s f.keyId < f.pn ∧
      lastPn (step s f).1 f.keyId = f.pn := by
  by_cases ha : Accepts s f
  · rw [step_accepts s f ha] at h ⊢
    cases hb : f.body with
    | groupMsg1 m =>
      rw [hb] at h
      simp only at h
      exfalso
      unfold group at h
      split at h
      · cases h
      · split at h
        · cases h
        · split at h <;> cases h
    | data q =>
      rw [hb] at h
      cases h
      exact ⟨rfl, ha.1, ha.2, lastPn_recordPn _ _ _⟩
  · obtain ⟨d, hd⟩ := step_rejects s f ha
    rw [hd] at h; cases h

theorem group_pnTk (s : State) (m : GroupMsg1) : (group s m).1.pnTk = s.pnTk := by
  unfold group; split
  · rfl
  · split
    · rfl
    · split <;> rfl

theorem recordPn_pnTk (s : State) (f : Frame) (h : Accepts s f) :
    s.pnTk ≤ (recordPn s f.keyId f.pn).pnTk := by
  have h2 := h.2
  unfold lastPn at h2; unfold recordPn
  split
  · rename_i h0; simp only [h0, ite_true] at h2; simp only; omega
  · exact Nat.le_refl _

theorem recordPn_pnGtk (s : State) (f : Frame) (h : Accepts s f) :
    s.pnGtk ≤ (recordPn s f.keyId f.pn).pnGtk := by
  have h2 := h.2
  unfold lastPn at h2; unfold recordPn
  split
  · exact Nat.le_refl _
  · rename_i h0; simp only [h0, ite_false] at h2; simp only; omega

/-- The pairwise packet-number floor never decreases. -/
theorem step_pnTk_mono (s : State) (f : Frame) : s.pnTk ≤ (step s f).1.pnTk := by
  by_cases ha : Accepts s f
  · rw [step_accepts s f ha]
    cases f.body with
    | groupMsg1 m => simp only; rw [group_pnTk]; exact recordPn_pnTk s f ha
    | data p => exact recordPn_pnTk s f ha
  · obtain ⟨d, hd⟩ := step_rejects s f ha
    rw [hd]; exact Nat.le_refl _

/-- The group packet-number floor never decreases, except when a new GTK is
installed (a message 2 is sent), when it becomes the Key RSC. -/
theorem step_pnGtk_mono (s : State) (f : Frame) (h : ∀ r, (step s f).2 ≠ .msg2 r) :
    s.pnGtk ≤ (step s f).1.pnGtk := by
  by_cases ha : Accepts s f
  · have hr := recordPn_pnGtk s f ha
    rw [step_accepts s f ha] at h ⊢
    cases hb : f.body with
    | groupMsg1 m =>
      rw [hb] at h
      simp only at h ⊢
      unfold group at h ⊢
      split
      · exact hr
      · rename_i h1
        simp only [h1, ite_false] at h
        split
        · exact hr
        · rename_i h2
          simp only [h2] at h
          split
          · exact hr
          · rename_i h3
            simp only [h3] at h
            exact absurd rfl (h m.replay)
    | data p => exact hr
  · obtain ⟨d, hd⟩ := step_rejects s f ha
    rw [hd]; exact Nat.le_refl _

/-! ## Key-id rollover -/

/-- An answered group message 1 installs exactly its key and key id (1–3,
never the TK's 0), with the Key RSC as the new key's packet-number floor,
and leaves the TK alone. -/
theorem msg2_installs (s : State) (f : Frame) (r : Nat) (h : (step s f).2 = .msg2 r) :
    ∃ m, f.body = .groupMsg1 m ∧ r = m.replay ∧ m.micOk = true ∧ m.unwrapOk = true ∧
      (m.keyId = 1 ∨ m.keyId = 2 ∨ m.keyId = 3) ∧
      (step s f).1.gtkId = m.keyId ∧ (step s f).1.gtk = m.gtk ∧
      (step s f).1.pnGtk = m.rsc ∧ (step s f).1.tk = s.tk := by
  obtain ⟨-, m, hb, hs⟩ := step_msg2 s f r h
  rw [hs] at h ⊢
  obtain ⟨hr, -, hmic, hun, hid, hg⟩ := group_msg2 _ m r h
  rw [hg]
  refine ⟨m, hb, hr, hmic, hun, ?_, rfl, rfl, rfl, recordPn_tk _ _ _⟩
  simp only [gtkIdOk, Bool.or_eq_true, beq_iff_eq] at hid
  omega

/-- After a rekey, a frame under the new key id and key whose packet number
is above the Key RSC is decrypted and delivered. -/
theorem delivered_after_rekey (s : State) (f g : Frame) (r : Nat) (m : GroupMsg1) (p : Nat)
    (h : (step s f).2 = .msg2 r) (hm : f.body = .groupMsg1 m)
    (hid : g.keyId = m.keyId) (hkey : g.key = m.gtk) (hpn : m.rsc < g.pn)
    (hb : g.body = .data p) :
    (step (step s f).1 g).2 = .deliver p := by
  obtain ⟨m', hm', -, -, -, hrange, hgid, hgtk, hpnG, -⟩ := msg2_installs s f r h
  rw [hm] at hm'; cases hm'
  have h0 : g.keyId ≠ 0 := by omega
  have ha : Accepts (step s f).1 g := by
    refine ⟨?_, ?_⟩
    · have he : g.keyId = (step s f).1.gtkId := by rw [hgid, hid]
      have h0' : (step s f).1.gtkId ≠ 0 := by rw [hgid]; omega
      unfold keyFor; rw [he]; simp only [h0', ↓reduceIte, hgtk, hkey]
    · unfold lastPn; simp only [h0, ite_false, hpnG]; exact hpn
  rw [step_accepts _ g ha, hb]

/-- After a rekey to another key id, a frame under the previous key id is
dropped and changes nothing. -/
theorem stale_id_dropped (s : State) (f g : Frame) (r : Nat) (m : GroupMsg1)
    (h : (step s f).2 = .msg2 r) (hm : f.body = .groupMsg1 m)
    (h0 : g.keyId ≠ 0) (hid : g.keyId ≠ m.keyId) :
    step (step s f).1 g = ((step s f).1, .drop .unknownKey) := by
  obtain ⟨m', hm', -, -, -, -, hgid, -⟩ := msg2_installs s f r h
  rw [hm] at hm'; cases hm'
  have hk : keyFor (step s f).1 g.keyId = none := by
    have he : ¬ g.keyId = (step s f).1.gtkId := by rw [hgid]; exact hid
    unfold keyFor; simp only [h0, he, ↓reduceIte]
  exact step_unknown _ g hk

/-- After a rekey, a frame under the new key id but other key material (the
previous key that had this id) fails its MIC, is dropped and changes
nothing. -/
theorem stale_material_dropped (s : State) (f g : Frame) (r : Nat) (m : GroupMsg1)
    (h : (step s f).2 = .msg2 r) (hm : f.body = .groupMsg1 m)
    (hid : g.keyId = m.keyId) (hkey : g.key ≠ m.gtk) :
    step (step s f).1 g = ((step s f).1, .drop .mic) := by
  obtain ⟨m', hm', -, -, -, hrange, hgid, hgtk, -⟩ := msg2_installs s f r h
  rw [hm] at hm'; cases hm'
  have h0 : g.keyId ≠ 0 := by omega
  have hk : keyFor (step s f).1 g.keyId = some m.gtk := by
    have he : g.keyId = (step s f).1.gtkId := by rw [hgid, hid]
    have h0' : (step s f).1.gtkId ≠ 0 := by rw [hgid]; omega
    unfold keyFor; rw [he]; simp only [h0', ↓reduceIte, hgtk]
  exact step_mic _ g m.gtk hk fun e => hkey e.symm

/-- A frame whose packet number is at or below the last one accepted under
its key is dropped and changes nothing: replays never reach the network
subject, before or after a rekey. -/
theorem replayed_pn_dropped (s : State) (g : Frame) (hk : keyFor s g.keyId = some g.key)
    (hpn : g.pn ≤ lastPn s g.keyId) :
    step s g = (s, .drop .replayedPn) := by
  unfold step
  rw [hk]
  simp only [ne_eq, not_true_eq_false, ite_false, hpn, ite_true]

/-! ## The q35 fixture -/

/-- The fixture's keys: the TK, the first GTK (key id 1), the GTK of the
first rotation (key id 2) and of the second (key id 1 again). -/
def tk0 : Key := 10
def gtk1 : Key := 21
def gtk2 : Key := 22
def gtk3 : Key := 23

/-- After the 4-way handshake: GTK `gtk1` with key id 1, replay counter 2. -/
def start : State := { tk := tk0, gtk := gtk1, gtkId := 1, replay := 2, pnTk := 0, pnGtk := 0 }

def msg1 (replay keyId : Nat) (gtk : Key) (rsc : Nat) (micOk unwrapOk : Bool := true) :
    GroupMsg1 :=
  { replay, micOk, unwrapOk, keyId, gtk, rsc }

/-- Payload names: 0, 1, 3 broadcast ARP requests for the host, 2 an ICMP
echo request to it. -/
def arpBefore : Nat := 0
def arpAfter : Nat := 1
def ping : Nat := 2
def arpRolled : Nat := 3

/-- The `gtk-rekey` scenario's frames, in order. -/
def scenario : List Frame := [
  -- broadcast ARP under the first GTK
  { keyId := 1, key := gtk1, pn := 1, body := .data arpBefore },
  -- rotation 1 → 2: message 1 with replay counter 3 and Key RSC 4
  { keyId := 0, key := tk0, pn := 1, body := .groupMsg1 (msg1 3 2 gtk2 4) },
  -- a broadcast still under key id 1: dropped
  { keyId := 1, key := gtk1, pn := 2, body := .data arpBefore },
  -- key id 2 at the Key RSC itself: dropped
  { keyId := 2, key := gtk2, pn := 4, body := .data arpAfter },
  -- broadcast ARP under the new key: delivered
  { keyId := 2, key := gtk2, pn := 5, body := .data arpAfter },
  -- the same frame replayed: dropped
  { keyId := 2, key := gtk2, pn := 5, body := .data arpAfter },
  -- message 1 retransmitted with the same replay counter: not answered again
  { keyId := 0, key := tk0, pn := 2, body := .groupMsg1 (msg1 3 2 gtk2 4) },
  -- message 1 with a bad MIC: dropped
  { keyId := 0, key := tk0, pn := 3, body := .groupMsg1 (msg1 4 1 gtk3 0 false) },
  -- unicast ping under the TK: delivered
  { keyId := 0, key := tk0, pn := 4, body := .data ping },
  -- rotation 2 → 1: message 1 with replay counter 5 and Key RSC 0
  { keyId := 0, key := tk0, pn := 5, body := .groupMsg1 (msg1 5 1 gtk3 0) },
  -- key id 1 under the old first GTK: dropped (MIC)
  { keyId := 1, key := gtk1, pn := 9, body := .data arpRolled },
  -- key id 2, no longer installed: dropped
  { keyId := 2, key := gtk2, pn := 6, body := .data arpRolled },
  -- broadcast ARP under the newest key: delivered
  { keyId := 1, key := gtk3, pn := 1, body := .data arpRolled },
  -- message 1 for key id 0 with counter 6: the counter advances, nothing is
  -- installed
  { keyId := 0, key := tk0, pn := 6, body := .groupMsg1 (msg1 6 0 gtk2 0) },
  -- message 1 with counter 6 again: dropped as stale
  { keyId := 0, key := tk0, pn := 7, body := .groupMsg1 (msg1 6 2 gtk2 0) }]

/-- The model's outcome for every frame of the scenario. -/
def scenarioOutcomes : List Out := [
  .deliver arpBefore, .msg2 3, .drop .unknownKey, .drop .replayedPn, .deliver arpAfter,
  .drop .replayedPn, .drop .replayedCounter, .drop .groupMic, .deliver ping, .msg2 5,
  .drop .mic, .drop .unknownKey, .deliver arpRolled, .drop .noGtk, .drop .replayedCounter]

/-- The scenario rotates the group key 1 → 2 → 1 and has exactly the
outcomes the transcript shows. -/
theorem scenario_outcomes : (run start scenario).2 = scenarioOutcomes := by decide

/-- It ends with the third GTK under key id 1 and replay counter 6. -/
theorem scenario_final :
    (run start scenario).1 =
      { tk := tk0, gtk := gtk3, gtkId := 1, replay := 6, pnTk := 7, pnGtk := 1 } := by
  decide

end LeanOS.GtkRekey
