import LeanOS.NetworkSubject
import LeanOS.Net.Echo

/-!
# The DHCP subject and the echo subject on one frame endpoint (issue #556)

Issue #450 moved ARP, ICMP echo and UDP echo out of the BCM43224 driver
into a ring-3 network subject (`LeanOS.NetworkSubject`), but left the DHCP
client in the driver: the driver chose the address the network subject
answered for, and told it in a configuration record. Issue #556 moves the
client into a ring-3 subject of its own. Three subjects share the frame
endpoint:

* the **driver** subject (1) holds the device capability; its program
  delivers records (the link record, ticks, frames) and transmits replies;
* the **DHCP** subject (2) holds a frame port with its own window;
* the **echo** subject (3) holds another frame port with another window.

The endpoint serves one port at a time, its `route`: the DHCP subject's
first. When the DHCP subject has a lease it **hands it off** to the echo
subject over IPC: the echo subject receives the hardware address and the
leased IPv4 address, and from then on the endpoint serves the echo subject.
The driver gives no address: it never sends a configuration record.

This module models the endpoint, every subject's memory and the hand-off,
and proves the confinement the issue asks for:

* **Only the routed port holder reaches frames**: a fetch or send by the
  driver or any other non-holder is refused and changes nothing
  (`nonholder_refused`), and so is one by the holder the endpoint does not
  serve (`unrouted_refused`).
* **Each subject its own window**: across any run, a byte of a subject's
  memory changes only by that subject's own store, or by an endpoint copy
  into that same subject's own window (`step_mem_changed`,
  `run_mem_outside_windows`); the driver never receives a frame byte
  (`run_driver_mem`), and neither port holder's window ever receives the
  other's frame.
* **Frames cross only through the endpoint**: the transmit slot changes only
  by the routed holder's accepted send, carrying exactly bytes of its own
  window, or by the driver program taking it (`step_tx_changed`).
* **The lease signal carries one bit**: the word the kernel shows the
  driver (`leaseSignal`, issue #573) is a function of the route alone; it is
  set only by the DHCP subject's accepted hand-off (`step_leaseSignal_set`),
  never unset (`step_leaseSignal_stays`), and in every reachable state it is
  set exactly when the echo subject holds a lease
  (`run_leaseSignal_iff_lease`).
* **The lease comes from the DHCP subject**: the echo subject's address
  changes only by the DHCP subject's accepted hand-off (`step_lease_changed`,
  `handoff_refused`), the endpoint serves the echo subject only after it
  (`run_routed_leased`, `echo_fetch_leased`), and the reference responder
  answers only frames addressed to the address it is given
  (`Echo.replyFrame_for_ip`): the echo subject answers only for the lease.
* **No device authority**: neither the DHCP subject nor the echo subject is
  granted a device capability, so every device `bind` or `invoke` either
  attempts is denied without effect (`dhcp_no_device_effects`,
  `echo_no_device_effects`).
* **The kernel's check**: the allocation-free witness `framePortCheck`
  (exported as `leanos_frame_port_check`), which the kernel calls on every
  copy request, accepts exactly the requests `step` accepts
  (`framePortCheck_fetch`, `framePortCheck_send`), refuses every non-holder
  (`framePortCheck_nonholder`), and admits each subject only for its own
  window (`framePortCheck_own_window`).

Not modelled: the ring-3 code (the client's logic is checked against the
reference client `LeanOS.Wifi.Dhcp.Client` by hosted vectors), the IPC
exchange (checked separately against `leanos_blocking_ipc_event`), the
device program, scheduling and the executor. The booted kernel is tested,
not proved, against this model.
-/

namespace LeanOS.DhcpSubject

open NetworkSubject (Window writeBytes readBytes update minFrame maxFrame)

/-- Subject codes of the `dhcp-subject` image. -/
def driver : Nat := 1
def dhcp : Nat := 2
def echo : Nat := 3

/-- The two port holders' windows. -/
structure Ports where
  dhcpWin : Window
  echoWin : Window

/-- Subject `who`'s window, if it holds a port. -/
def Ports.window (p : Ports) (who : Nat) : Option Window :=
  if who = dhcp then some p.dhcpWin else if who = echo then some p.echoWin else none

/-- Each subject's memory, the endpoint's two slots, the port it serves and
the lease the echo subject was handed (hardware address, IPv4 address). -/
structure State where
  mem : Nat → Nat → UInt8
  rx : List UInt8
  rxPending : Bool
  tx : List UInt8
  txPending : Bool
  route : Nat
  lease : Option (UInt64 × UInt32)

/-- The state at boot: the endpoint serves the DHCP subject and the echo
subject holds no lease. -/
def State.boot (mem : Nat → Nat → UInt8) : State :=
  { mem, rx := [], rxPending := false, tx := [], txPending := false, route := dhcp,
    lease := none }

inductive Op where
  /-- The driver program leaves a record in scratch and yields. -/
  | deliver (record : List UInt8)
  /-- `who` asks the kernel to copy the pending record to `addr`. -/
  | fetch (who addr : Nat)
  /-- `who` asks the kernel to copy `len` bytes at `addr` out as a frame. -/
  | send (who addr len : Nat)
  /-- The driver program takes the frame and transmits it. -/
  | transmit
  /-- `who` stores `bytes` at `addr` in its own memory. -/
  | write (who addr : Nat) (bytes : List UInt8)
  /-- `who` hands the lease (`mac`, `ip`) to the echo subject over IPC. -/
  | handoff (who : Nat) (mac : UInt64) (ip : UInt32)

inductive Reply where
  | accepted (n : Nat)
  | refused
  deriving DecidableEq, Repr

/-- The fetch the kernel accepts: from the routed port holder, with a record
pending, into a range of its own window. -/
def fetchOk (p : Ports) (s : State) (who addr : Nat) : Bool :=
  match p.window who with
  | some w => who == s.route && s.rxPending && s.rx.length ≤ maxFrame &&
      w.covers addr s.rx.length
  | none => false

/-- The send the kernel accepts: from the routed port holder, no frame
pending, a frame length, from a range of its own window. -/
def sendOk (p : Ports) (s : State) (who addr len : Nat) : Bool :=
  match p.window who with
  | some w => who == s.route && !s.txPending && minFrame ≤ len && len ≤ maxFrame &&
      w.covers addr len
  | none => false

/-- One endpoint transition. -/
def step (p : Ports) (s : State) : Op → State × Reply
  | .deliver f =>
    if !s.rxPending && f.length ≤ maxFrame then
      ({ s with rx := f, rxPending := true }, .accepted f.length)
    else (s, .refused)
  | .fetch who addr =>
    if fetchOk p s who addr then
      ({ s with mem := update s.mem who (writeBytes (s.mem who) addr s.rx),
                rxPending := false }, .accepted s.rx.length)
    else (s, .refused)
  | .send who addr len =>
    if sendOk p s who addr len then
      ({ s with tx := readBytes (s.mem who) addr len, txPending := true }, .accepted 0)
    else (s, .refused)
  | .transmit => ({ s with tx := [], txPending := false }, .accepted s.tx.length)
  | .write who addr bytes =>
    ({ s with mem := update s.mem who (writeBytes (s.mem who) addr bytes) }, .accepted 0)
  | .handoff who mac ip =>
    if who = dhcp ∧ s.route = dhcp then
      ({ s with route := echo, lease := some (mac, ip) }, .accepted 0)
    else (s, .refused)

/-- Run a list of transitions. -/
def run (p : Ports) (s : State) : List Op → State
  | [] => s
  | op :: ops => run p (step p s op).1 ops

theorem window_some {p : Ports} {who : Nat} {w : Window} (h : p.window who = some w) :
    who = dhcp ∨ who = echo := by
  unfold Ports.window at h
  by_cases h2 : who = dhcp
  · exact Or.inl h2
  · by_cases h3 : who = echo
    · exact Or.inr h3
    · simp [h2, h3] at h

theorem window_none {p : Ports} {who : Nat} (h2 : who ≠ dhcp) (h3 : who ≠ echo) :
    p.window who = none := by
  simp [Ports.window, h2, h3]

theorem fetchOk_route {p : Ports} {s : State} {who addr : Nat}
    (h : fetchOk p s who addr = true) :
    who = s.route ∧ ∃ w, p.window who = some w ∧ w.covers addr s.rx.length = true := by
  unfold fetchOk at h
  split at h
  · rename_i w hw
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨h.1.1.1, w, hw, h.2⟩
  · exact absurd h (by simp)

theorem sendOk_route {p : Ports} {s : State} {who addr len : Nat}
    (h : sendOk p s who addr len = true) :
    who = s.route ∧ ∃ w, p.window who = some w ∧ w.covers addr len = true := by
  unfold sendOk at h
  split at h
  · rename_i w hw
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨h.1.1.1.1, w, hw, h.2⟩
  · exact absurd h (by simp)

/-! ## Only the routed port holder reaches frames -/

/-- A fetch or send by a subject holding no port (the driver included) is
refused and changes nothing. -/
theorem nonholder_refused (p : Ports) (s : State) (who : Nat) (h2 : who ≠ dhcp)
    (h3 : who ≠ echo) :
    (∀ addr, step p s (.fetch who addr) = (s, .refused)) ∧
    (∀ addr len, step p s (.send who addr len) = (s, .refused)) := by
  have hw := window_none (p := p) h2 h3
  constructor
  · intro addr; simp [step, fetchOk, hw]
  · intro addr len; simp [step, sendOk, hw]

/-- In particular the driver subject's fetches and sends are refused. -/
theorem driver_refused (p : Ports) (s : State) :
    (∀ addr, step p s (.fetch driver addr) = (s, .refused)) ∧
    (∀ addr len, step p s (.send driver addr len) = (s, .refused)) :=
  nonholder_refused p s driver (by decide) (by decide)

/-- A port holder the endpoint does not serve is refused too. -/
theorem unrouted_refused (p : Ports) (s : State) (who : Nat) (h : who ≠ s.route) :
    (∀ addr, step p s (.fetch who addr) = (s, .refused)) ∧
    (∀ addr len, step p s (.send who addr len) = (s, .refused)) := by
  constructor
  · intro addr
    have : fetchOk p s who addr = false := by
      cases hf : fetchOk p s who addr
      · rfl
      · exact absurd (fetchOk_route hf).1 h
    simp [step, this]
  · intro addr len
    have : sendOk p s who addr len = false := by
      cases hf : sendOk p s who addr len
      · rfl
      · exact absurd (sendOk_route hf).1 h
    simp [step, this]

/-! ## Each subject its own window -/

/-- A changed byte of any subject's memory is that subject's own store, or
an accepted endpoint copy into that same subject's own window. -/
theorem step_mem_changed (p : Ports) (s : State) (op : Op) (x a : Nat)
    (h : (step p s op).1.mem x a ≠ s.mem x a) :
    (∃ addr bytes, op = .write x addr bytes) ∨
    (∃ w, p.window x = some w ∧ w.contains a ∧ ∃ addr, op = .fetch x addr) := by
  cases op with
  | deliver f =>
    simp only [step] at h; split at h <;> exact absurd rfl h
  | send who addr len =>
    simp only [step] at h; split at h <;> exact absurd rfl h
  | transmit => exact absurd rfl h
  | handoff who mac ip =>
    simp only [step] at h; split at h <;> exact absurd rfl h
  | write who addr bytes =>
    simp only [step, update] at h
    by_cases hx : x = who
    · subst hx; exact Or.inl ⟨addr, bytes, rfl⟩
    · simp [hx] at h
  | fetch who addr =>
    simp only [step] at h
    split at h
    · rename_i hok
      obtain ⟨-, w, hw, hcov⟩ := fetchOk_route hok
      simp only [Window.covers, Bool.and_eq_true, decide_eq_true_eq] at hcov
      simp only [update] at h
      by_cases hx : x = who
      · subst hx
        simp only [↓reduceIte] at h
        by_cases hin : addr ≤ a ∧ a < addr + s.rx.length
        · exact Or.inr ⟨w, hw, ⟨by omega, by omega⟩, addr, rfl⟩
        · exact absurd (NetworkSubject.writeBytes_outside _ _ _ _ hin) h
      · simp [hx] at h
    · exact absurd rfl h

/-- Subject `x`'s own window contains `a`. -/
def inOwnWindow (p : Ports) (x a : Nat) : Prop := ∃ w, p.window x = some w ∧ w.contains a

/-- Across any run, memory that no store of its owner touched changes only
inside that owner's own window: the kernel copies no frame byte into the
driver, into any subject without a port, or into a port holder outside its
own window. -/
theorem run_mem_outside_windows (p : Ports) :
    ∀ (s : State) (ops : List Op) (x a : Nat),
      (∀ op ∈ ops, ∀ addr bytes, op ≠ .write x addr bytes) →
      ¬ inOwnWindow p x a →
      (run p s ops).mem x a = s.mem x a
  | _, [], _, _, _, _ => rfl
  | s, op :: ops, x, a, hw, hout => by
    simp only [run]
    rw [run_mem_outside_windows p (step p s op).1 ops x a
      (fun op' hmem => hw op' (List.mem_cons_of_mem _ hmem)) hout]
    by_cases hc : (step p s op).1.mem x a = s.mem x a
    · exact hc
    · rcases step_mem_changed p s op x a hc with ⟨addr, bytes, hop⟩ | ⟨w, hwin, hin, -⟩
      · exact absurd hop (hw op (List.mem_cons_self ..) addr bytes)
      · exact absurd ⟨w, hwin, hin⟩ hout

/-- The driver subject's memory changes only by its own stores. -/
theorem run_driver_mem (p : Ports) (s : State) (ops : List Op) (a : Nat)
    (hw : ∀ op ∈ ops, ∀ addr bytes, op ≠ .write driver addr bytes) :
    (run p s ops).mem driver a = s.mem driver a :=
  run_mem_outside_windows p s ops driver a hw (by
    rintro ⟨w, hwin, -⟩
    rcases window_some hwin with h | h <;> simp [driver, dhcp, echo] at h)

/-- A port holder's memory outside its own window never receives a frame
byte: in particular the DHCP subject never receives the echo subject's
frames outside its own window, and the echo subject never the DHCP
subject's. -/
theorem run_port_holder_mem (p : Ports) (s : State) (ops : List Op) (x a : Nat)
    (hw : ∀ op ∈ ops, ∀ addr bytes, op ≠ .write x addr bytes)
    (hout : ∀ w, p.window x = some w → ¬ w.contains a) :
    (run p s ops).mem x a = s.mem x a :=
  run_mem_outside_windows p s ops x a hw (by
    rintro ⟨w, hwin, hin⟩; exact hout w hwin hin)

/-! ## Frames cross only through the endpoint -/

/-- The receive slot changes only when the driver program delivers. -/
theorem step_rx_changed (p : Ports) (s : State) (op : Op)
    (h : (step p s op).1.rx ≠ s.rx) : ∃ f, op = .deliver f ∧ (step p s op).1.rx = f := by
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
  | handoff => simp only [step] at h; split at h <;> exact absurd rfl h

/-- The transmit slot changes only by the routed port holder's accepted
send, which carries exactly bytes of its own window, or by the driver
program taking the frame. -/
theorem step_tx_changed (p : Ports) (s : State) (op : Op)
    (h : (step p s op).1.tx ≠ s.tx) :
    op = .transmit ∨
    ∃ who addr len w, op = .send who addr len ∧ who = s.route ∧ p.window who = some w ∧
      w.covers addr len = true ∧ (step p s op).1.tx = readBytes (s.mem who) addr len := by
  cases op with
  | deliver f => simp only [step] at h; split at h <;> exact absurd rfl h
  | fetch who addr => simp only [step] at h; split at h <;> exact absurd rfl h
  | transmit => exact Or.inl rfl
  | write => exact absurd rfl h
  | handoff => simp only [step] at h; split at h <;> exact absurd rfl h
  | send who addr len =>
    simp only [step] at h ⊢
    split at h
    · rename_i hok
      obtain ⟨hr, w, hw, hcov⟩ := sendOk_route hok
      exact Or.inr ⟨who, addr, len, w, rfl, hr, hw, hcov, by simp [hok]⟩
    · exact absurd rfl h

/-! ## The lease comes from the DHCP subject -/

/-- A hand-off by any subject but the DHCP subject is refused and changes
nothing. -/
theorem handoff_refused (p : Ports) (s : State) (who : Nat) (h : who ≠ dhcp)
    (mac : UInt64) (ip : UInt32) : step p s (.handoff who mac ip) = (s, .refused) := by
  simp [step, h]

/-- The echo subject's lease changes only by the DHCP subject's accepted
hand-off, and then it is exactly the handed address. -/
theorem step_lease_changed (p : Ports) (s : State) (op : Op)
    (h : (step p s op).1.lease ≠ s.lease) :
    ∃ mac ip, op = .handoff dhcp mac ip ∧ s.route = dhcp ∧
      (step p s op).1.lease = some (mac, ip) := by
  cases op with
  | deliver f => simp only [step] at h; split at h <;> exact absurd rfl h
  | fetch who addr => simp only [step] at h; split at h <;> exact absurd rfl h
  | send who addr len => simp only [step] at h; split at h <;> exact absurd rfl h
  | transmit => exact absurd rfl h
  | write => exact absurd rfl h
  | handoff who mac ip =>
    simp only [step] at h ⊢
    split at h
    · rename_i hok
      obtain ⟨hw, hr⟩ := hok
      subst hw
      exact ⟨mac, ip, rfl, hr, by simp [hr]⟩
    · exact absurd rfl h

/-- The route changes only by the DHCP subject's accepted hand-off, from the
DHCP subject to the echo subject. -/
theorem step_route_changed (p : Ports) (s : State) (op : Op)
    (h : (step p s op).1.route ≠ s.route) :
    s.route = dhcp ∧ (step p s op).1.route = echo ∧ ∃ mac ip, op = .handoff dhcp mac ip := by
  cases op with
  | deliver f => simp only [step] at h; split at h <;> exact absurd rfl h
  | fetch who addr => simp only [step] at h; split at h <;> exact absurd rfl h
  | send who addr len => simp only [step] at h; split at h <;> exact absurd rfl h
  | transmit => exact absurd rfl h
  | write => exact absurd rfl h
  | handoff who mac ip =>
    simp only [step] at h ⊢
    split at h
    · rename_i hok
      obtain ⟨hw, hr⟩ := hok
      subst hw
      exact ⟨hr, by simp [hr], mac, ip, rfl⟩
    · exact absurd rfl h

/-- The invariant of every reachable state: the endpoint serves the DHCP
subject, or it serves the echo subject and the echo subject holds a lease. -/
def Routed (s : State) : Prop := s.route = dhcp ∨ (s.route = echo ∧ s.lease.isSome)

theorem boot_routed (mem : Nat → Nat → UInt8) : Routed (State.boot mem) := Or.inl rfl

theorem step_routed (p : Ports) (s : State) (op : Op) (h : Routed s) :
    Routed (step p s op).1 := by
  cases op with
  | handoff who mac ip =>
    simp only [step]
    split
    · exact Or.inr ⟨rfl, rfl⟩
    · exact h
  | deliver f => simp only [step]; split <;> exact h
  | fetch who addr => simp only [step]; split <;> exact h
  | send who addr len => simp only [step]; split <;> exact h
  | transmit => exact h
  | write => exact h

/-- Every run from a routed state stays routed: the endpoint never serves
the echo subject before it holds a lease. -/
theorem run_routed (p : Ports) : ∀ (s : State) (ops : List Op), Routed s → Routed (run p s ops)
  | _, [], h => h
  | s, op :: ops, h => run_routed p (step p s op).1 ops (step_routed p s op h)

/-- From boot, the echo subject's lease is the one the DHCP subject handed
over, and the endpoint serves the echo subject only once it holds it. -/
theorem run_routed_leased (p : Ports) (mem : Nat → Nat → UInt8) (ops : List Op) :
    (run p (State.boot mem) ops).route = echo →
      (run p (State.boot mem) ops).lease.isSome :=
  fun hr => by
    rcases run_routed p _ ops (boot_routed mem) with h | ⟨-, hl⟩
    · rw [hr] at h; exact absurd h (by decide)
    · exact hl

/-- An accepted fetch by the echo subject happens only once it holds a
lease. -/
theorem echo_fetch_leased (p : Ports) (s : State) (addr : Nat) (hr : Routed s)
    (h : fetchOk p s echo addr = true) : s.lease.isSome := by
  have := (fetchOk_route h).1
  rcases hr with hd | ⟨-, hl⟩
  · rw [hd] at this; exact absurd this (by decide)
  · exact hl

/-! ## The lease signal (issue #573)

The BCM43224 serve program separates the time it allows for a lease from
the time it serves after the lease. It does not parse DHCP: the kernel
stores 1 in the lease signal word of the driver's scratch
(`LeanOS.Net.FrameSource.leaseSignalAt`) when the endpoint's route moves to
the echo subject, and the driver reads that word. In this model the word is
`leaseSignal`, a function of the route alone: it carries one bit, never the
leased address. -/

/-- The lease signal word the kernel shows the driver: whether the endpoint
serves the echo subject. -/
def leaseSignal (s : State) : Bool := s.route == echo

/-- At boot the signal is unset. -/
theorem leaseSignal_boot (mem : Nat → Nat → UInt8) : leaseSignal (State.boot mem) = false :=
  rfl

/-- The signal is set only by the DHCP subject's accepted hand-off. -/
theorem step_leaseSignal_set (p : Ports) (s : State) (op : Op)
    (h0 : leaseSignal s = false) (h1 : leaseSignal (step p s op).1 = true) :
    ∃ mac ip, op = .handoff dhcp mac ip ∧ s.route = dhcp := by
  have hne : (step p s op).1.route ≠ s.route := by
    intro he
    simp only [leaseSignal] at h0 h1
    rw [he] at h1
    rw [h0] at h1
    exact Bool.false_ne_true h1
  obtain ⟨hr, -, mac, ip, hop⟩ := step_route_changed p s op hne
  exact ⟨mac, ip, hop, hr⟩

/-- Once set, the signal stays set: no transition moves the route back. -/
theorem step_leaseSignal_stays (p : Ports) (s : State) (op : Op) (h : leaseSignal s = true) :
    leaseSignal (step p s op).1 = true := by
  by_cases he : (step p s op).1.route = s.route
  · simp only [leaseSignal] at h ⊢; rw [he]; exact h
  · obtain ⟨hr, -⟩ := step_route_changed p s op he
    simp only [leaseSignal, hr] at h
    exact absurd h (by decide)

/-- In every reachable state the signal is set exactly when the echo subject
holds a lease: the driver's serve window starts only after a lease was
handed off, and a handed-off lease always shows. -/
theorem run_leaseSignal_iff_lease (p : Ports) (mem : Nat → Nat → UInt8) (ops : List Op) :
    leaseSignal (run p (State.boot mem) ops) = (run p (State.boot mem) ops).lease.isSome := by
  suffices ∀ (s : State) (ops : List Op), leaseSignal s = s.lease.isSome →
      leaseSignal (run p s ops) = (run p s ops).lease.isSome from
    this _ ops rfl
  intro s ops
  induction ops generalizing s with
  | nil => exact id
  | cons op ops ih =>
    intro h
    apply ih
    cases op with
    | handoff who mac ip =>
      simp only [step]
      split
      · rfl
      · exact h
    | deliver f => simp only [step]; split <;> exact h
    | fetch who addr => simp only [step]; split <;> exact h
    | send who addr len => simp only [step]; split <;> exact h
    | transmit => exact h
    | write => exact h

/-! ## The echo subject answers only for the lease -/

open Net.Echo (Buf word rd16 rd32 reply replyFrame drop arp ipv4) in
/-- The IPv4 address frame `f` asks for, as the responder reads it: for an
ARP frame (ethertype 0x0806) the target protocol address, the big-endian
word at offset 38; otherwise the IPv4 destination, the word at offset 30. -/
def askedFor (f : ByteArray) : UInt32 :=
  let b : Buf := { data := f }
  if word (rd16 b 12) == 0x0806 then word (rd32 b 38) else word (rd32 b 30)

open Net.Echo (Buf word rd16 rd32 reply replyFrame drop arp ipv4) in
/-- The responder's model reading delivers a reply only for a frame that
asks for its address `ip`. -/
theorem reply_for_ip (b : Buf) (len : UInt32) (mac : UInt64) (ip : UInt32)
    (h : (reply b len mac ip).v ≠ 0) : askedFor b.data = ip := by
  unfold reply at h
  split at h
  · exact absurd rfl h
  unfold askedFor
  by_cases harp : word (rd16 b 12) == 0x0806
  · have harp' : (word (rd16 ({ data := b.data } : Buf) 12) == 0x0806) = true := harp
    simp only [harp', ite_true]
    simp only [harp, ite_true, arp] at h
    split at h
    · exact absurd rfl h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact hc.2
    · exact absurd rfl h
  · have harp' : ¬ (word (rd16 ({ data := b.data } : Buf) 12) == 0x0806) = true := harp
    simp only [harp', Bool.false_eq_true, ite_false]
    simp only [harp, Bool.false_eq_true, ite_false] at h
    split at h
    · unfold ipv4 at h
      dsimp only at h
      split at h
      · exact absurd rfl h
      split at h
      · exact absurd rfl h
      · rename_i hc
        simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, not_or,
          Decidable.not_not] at hc
        exact hc.1.1.2
    · exact absurd rfl h

/-- The reference responder `Echo.replyFrame`, which the echo subject's
generated C is checked against, answers only frames that ask for the
address it is given. -/
theorem replyFrame_for_ip (f : ByteArray) (mac : UInt64) (ip : UInt32) (r : ByteArray)
    (h : Net.Echo.replyFrame f mac ip = some r) : askedFor f = ip := by
  unfold Net.Echo.replyFrame at h
  dsimp only at h
  split at h
  · exact absurd h (by simp)
  · rename_i hv
    exact reply_for_ip { data := f } f.size.toUInt32 mac ip
      (fun h0 => hv (beq_iff_eq.mpr h0))

/-- In every reachable state the echo subject answers only for its lease:
once the endpoint serves it, it holds the lease the DHCP subject handed
over, and the responder answers a frame only when the frame asks for that
leased address. -/
theorem echo_answers_only_lease (p : Ports) (mem : Nat → Nat → UInt8) (ops : List Op)
    (hr : (run p (State.boot mem) ops).route = echo) :
    ∃ mac ip, (run p (State.boot mem) ops).lease = some (mac, ip) ∧
      ∀ f r, Net.Echo.replyFrame f mac ip = some r → askedFor f = ip := by
  have hl := run_routed_leased p mem ops hr
  match hlease : (run p (State.boot mem) ops).lease, hl with
  | some (mac, ip), _ => exact ⟨mac, ip, rfl, fun f r h => replyFrame_for_ip f mac ip r h⟩

/-! ## No device authority -/

/-- The DHCP subject is never granted a device capability: after any device
run without a grant to it, each `bind` or `invoke` it attempts is denied and
leaves the device system unchanged. The installed device authority is the
keyboard-echo image's (`KeyboardEcho.bootDeviceCaps`: only the driver
subject holds device 0). -/
theorem dhcp_no_device_effects {σ} (models : Nat → Wifi.Sim.Device σ)
    (sys : DeviceCapability.System σ) (hcaps : sys.deviceCaps = KeyboardEcho.bootDeviceCaps)
    (ts : List DeviceCapability.Transition)
    (hg : ∀ d, DeviceCapability.Transition.grant dhcp d ∉ ts) :
    (∀ program, DeviceCapability.step models (DeviceCapability.run models sys ts)
        (.bind dhcp program) = (DeviceCapability.run models sys ts, .denied)) ∧
    (∀ fuel, DeviceCapability.step models (DeviceCapability.run models sys ts)
        (.invoke dhcp fuel) = (DeviceCapability.run models sys ts, .denied)) :=
  DeviceCapability.ungranted_subject_no_device_effects models sys dhcp ts
    (by rw [hcaps]; decide) hg

/-- The echo subject is never granted a device capability either. -/
theorem echo_no_device_effects {σ} (models : Nat → Wifi.Sim.Device σ)
    (sys : DeviceCapability.System σ) (hcaps : sys.deviceCaps = KeyboardEcho.bootDeviceCaps)
    (ts : List DeviceCapability.Transition)
    (hg : ∀ d, DeviceCapability.Transition.grant echo d ∉ ts) :
    (∀ program, DeviceCapability.step models (DeviceCapability.run models sys ts)
        (.bind echo program) = (DeviceCapability.run models sys ts, .denied)) ∧
    (∀ fuel, DeviceCapability.step models (DeviceCapability.run models sys ts)
        (.invoke echo fuel) = (DeviceCapability.run models sys ts, .denied)) :=
  DeviceCapability.ungranted_subject_no_device_effects models sys echo ts
    (by rw [hcaps]; decide) hg

/-- The generated device witness the kernel checks refuses both subjects
every device. -/
theorem deviceAuthorize_ports (device : UInt64) :
    KeyboardEcho.deviceAuthorize (dhcp.toUInt64) device = ConsoleServer.refuseCode ∧
    KeyboardEcho.deviceAuthorize (echo.toUInt64) device = ConsoleServer.refuseCode := by
  simp [KeyboardEcho.deviceAuthorize, dhcp, echo, ConsoleServer.refuseCode]

/-! ## The kernel's generated check -/

/-- Operation codes. -/
def opFetch : UInt64 := 1
def opSend : UInt64 := 2

/-- The decision behind `framePortCheck` for a request by `subject`: 0
accepts; 1 the caller holds no port; 2 the window is not the caller's own
(`owner`); 3 the endpoint serves the other port (`route`); 4 the endpoint is
in the wrong state (no record pending for a fetch, a frame already pending
for a send); 5 a length outside the bounds; 6 a range outside the window;
7 an unknown operation. `pending` is 1 when the slot the operation needs is
full. -/
@[inline] def framePortDecide (subject op pending route owner addr len base limit : UInt64) : UInt64 :=
  if subject != 2 && subject != 3 then 1
  else if owner != subject then 2
  else if route != subject then 3
  else if op == 1 then
    if pending != 1 then 4
    else if len > 1514 then 5
    else if NetworkSubject.rangeOk addr len base limit then 0 else 6
  else if op == 2 then
    if pending != 0 then 4
    else if len < 14 || len > 1514 then 5
    else if NetworkSubject.rangeOk addr len base limit then 0 else 6
  else 7

/-- The decision accepts only a port holder, only for a window labelled its
own, and only when the endpoint serves it. -/
theorem framePortDecide_accept (subject op pending route owner addr len base limit : UInt64)
    (h : framePortDecide subject op pending route owner addr len base limit = 0) :
    (subject = 2 ∨ subject = 3) ∧ owner = subject ∧ route = subject ∧
      NetworkSubject.Window.covers ⟨base.toNat, limit.toNat⟩ addr.toNat len.toNat = true := by
  unfold framePortDecide at h
  by_cases hs : subject != 2 && subject != 3
  · simp [hs] at h
  · simp only [hs, ite_false, Bool.false_eq_true] at h
    have hs' : subject = 2 ∨ subject = 3 := by
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, not_and, Decidable.not_not] at hs
      by_cases h2 : subject = 2
      · exact Or.inl h2
      · exact Or.inr (Decidable.not_not.mp (fun h3 => h2 (Classical.byContradiction
          (fun h2' => h3 (by have := hs h2'; exact this)))))
    by_cases ho : owner != subject
    · simp [ho] at h
    · simp only [ho, ite_false, Bool.false_eq_true] at h
      have ho' : owner = subject := by simpa using ho
      by_cases hr : route != subject
      · simp [hr] at h
      · simp only [hr, ite_false, Bool.false_eq_true] at h
        have hr' : route = subject := by simpa using hr
        refine ⟨hs', ho', hr', ?_⟩
        rw [← NetworkSubject.rangeOk_iff]
        split at h
        · split at h
          · exact absurd h (by decide)
          · split at h
            · exact absurd h (by decide)
            · split at h
              · assumption
              · exact absurd h (by decide)
        · split at h
          · split at h
            · exact absurd h (by decide)
            · split at h
              · exact absurd h (by decide)
              · split at h
                · assumption
                · exact absurd h (by decide)
          · exact absurd h (by decide)

/-- The witness accepts a fetch exactly from a port holder, for its own
window, while the endpoint serves it, with a record pending, of at most
`maxFrame` bytes, into a range of the window. -/
theorem framePortDecide_fetch_iff (subject pending route owner addr len base limit : UInt64) :
    framePortDecide subject opFetch pending route owner addr len base limit = 0 ↔
      (subject = 2 ∨ subject = 3) ∧ owner = subject ∧ route = subject ∧ pending = 1 ∧
        len.toNat ≤ maxFrame ∧
        NetworkSubject.Window.covers ⟨base.toNat, limit.toNat⟩ addr.toNat len.toNat = true := by
  constructor
  · intro h
    obtain ⟨hs, ho, hr, hcov⟩ := framePortDecide_accept _ _ _ _ _ _ _ _ _ h
    subst ho hr
    refine ⟨hs, rfl, rfl, ?_, ?_, hcov⟩
    · by_cases hp : pending = 1
      · exact hp
      · rcases hs with hs | hs <;> subst hs <;> simp [framePortDecide, opFetch, hp] at h
    · by_cases hl : len > 1514
      · rcases hs with hs | hs <;> subst hs <;>
          simp [framePortDecide, opFetch, hl] at h <;> split at h <;> simp_all
      · exact Classical.not_not.mp (fun hn => hl ((NetworkSubject.gt1514_iff len).mpr hn))
  · rintro ⟨hs, ho, hr, hp, hl, hcov⟩
    subst ho hr hp
    rw [← NetworkSubject.rangeOk_iff] at hcov
    have hl' : ¬ len > 1514 := fun h => (NetworkSubject.gt1514_iff len).mp h hl
    rcases hs with hs | hs <;> subst hs <;> simp [framePortDecide, opFetch, hl', hcov]

/-- The witness accepts a send exactly from a port holder, for its own
window, while the endpoint serves it, with no frame pending, of a frame
length, from a range of the window. -/
theorem framePortDecide_send_iff (subject pending route owner addr len base limit : UInt64) :
    framePortDecide subject opSend pending route owner addr len base limit = 0 ↔
      (subject = 2 ∨ subject = 3) ∧ owner = subject ∧ route = subject ∧ pending = 0 ∧
        minFrame ≤ len.toNat ∧ len.toNat ≤ maxFrame ∧
        NetworkSubject.Window.covers ⟨base.toNat, limit.toNat⟩ addr.toNat len.toNat = true := by
  constructor
  · intro h
    obtain ⟨hs, ho, hr, hcov⟩ := framePortDecide_accept _ _ _ _ _ _ _ _ _ h
    subst ho hr
    refine ⟨hs, rfl, rfl, ?_, ?_, ?_, hcov⟩
    · by_cases hp : pending = 0
      · exact hp
      · rcases hs with hs | hs <;> subst hs <;> simp [framePortDecide, opSend, hp] at h
    · by_cases hl : len < 14
      · rcases hs with hs | hs <;> subst hs <;>
          simp [framePortDecide, opSend, hl] at h <;> split at h <;> simp_all
      · exact Classical.not_not.mp (fun hn => hl ((NetworkSubject.lt14_iff len).mpr hn))
    · by_cases hl : len > 1514
      · rcases hs with hs | hs <;> subst hs <;>
          simp [framePortDecide, opSend, hl] at h <;> split at h <;> simp_all
      · exact Classical.not_not.mp (fun hn => hl ((NetworkSubject.gt1514_iff len).mpr hn))
  · rintro ⟨hs, ho, hr, hp, hmin, hmax, hcov⟩
    subst ho hr hp
    rw [← NetworkSubject.rangeOk_iff] at hcov
    have h14 : ¬ len < 14 := fun h => (NetworkSubject.lt14_iff len).mp h hmin
    have h1514 : ¬ len > 1514 := fun h => (NetworkSubject.gt1514_iff len).mp h hmax
    rcases hs with hs | hs <;> subst hs <;> simp [framePortDecide, opSend, h14, h1514, hcov]

/-- Every subject holding no port is refused whatever it asks. -/
theorem framePortDecide_nonholder (subject op pending route owner addr len base limit : UInt64)
    (h2 : subject ≠ 2) (h3 : subject ≠ 3) :
    framePortDecide subject op pending route owner addr len base limit = 1 := by
  simp [framePortDecide, h2, h3]

/-! ### The exported witness

The kernel passes the operation, the slot's state, the port the endpoint
serves and the owner of the window it passes in one request word,
`op ||| pending <<< 8 ||| route <<< 16 ||| owner <<< 24`, so the witness has
the six fixed-width arguments every boot export may take. -/

/-- The request word. -/
def request (op : UInt64) (pending : Bool) (route owner : UInt64) : UInt64 :=
  op ||| (if pending then (0x100 : UInt64) else 0) ||| ((route &&& 0xff) <<< 16) |||
    ((owner &&& 0xff) <<< 24)

/-- Allocation-free witness of `fetchOk`/`sendOk`, exported as
`leanos_frame_port_check`, which the kernel calls on every frame copy
request (`subject`, the request word, the buffer address and length, and the
window `[base, limit)` of the request word's owner); 0 accepts, any other
value is `framePortDecide`'s reason. -/
@[export leanos_frame_port_check]
def framePortCheck (subject req addr len base limit : UInt64) : UInt64 :=
  framePortDecide subject (req &&& 0xff) ((req >>> 8) &&& 0xff) ((req >>> 16) &&& 0xff)
    ((req >>> 24) &&& 0xff) addr len base limit

/-- The request word's fields, for the operations and the two ports. -/
theorem request_fields (op route owner : UInt64) (p : Bool) (hop : op = 1 ∨ op = 2)
    (hr : route = 2 ∨ route = 3) (ho : owner = 2 ∨ owner = 3) :
    request op p route owner &&& 0xff = op ∧
    (request op p route owner >>> 8) &&& 0xff = (if p then 1 else 0) ∧
    (request op p route owner >>> 16) &&& 0xff = route ∧
    (request op p route owner >>> 24) &&& 0xff = owner := by
  rcases hop with h | h <;> subst h <;> rcases hr with h | h <;> subst h <;>
    rcases ho with h | h <;> subst h <;> cases p <;> decide

theorem framePortCheck_request (subject op route owner addr len base limit : UInt64) (p : Bool)
    (hop : op = 1 ∨ op = 2) (hr : route = 2 ∨ route = 3) (ho : owner = 2 ∨ owner = 3) :
    framePortCheck subject (request op p route owner) addr len base limit =
      framePortDecide subject op (if p then 1 else 0) route owner addr len base limit := by
  obtain ⟨h1, h2, h3, h4⟩ := request_fields op route owner p hop hr ho
  simp only [framePortCheck, h1, h2, h3, h4]

/-- The exported witness admits each subject only for a window labelled its
own: whatever the request, an accepted copy names the caller as the
window's owner and as the port the endpoint serves. -/
theorem framePortCheck_own_window (subject req addr len base limit : UInt64)
    (h : framePortCheck subject req addr len base limit = 0) :
    (subject = 2 ∨ subject = 3) ∧ (req >>> 24) &&& 0xff = subject ∧
      (req >>> 16) &&& 0xff = subject ∧
      NetworkSubject.Window.covers ⟨base.toNat, limit.toNat⟩ addr.toNat len.toNat = true := by
  obtain ⟨hs, ho, hr, hcov⟩ := framePortDecide_accept _ _ _ _ _ _ _ _ _ h
  exact ⟨hs, ho, hr, hcov⟩

/-- Every subject holding no port is refused by the exported witness. -/
theorem framePortCheck_nonholder (subject req addr len base limit : UInt64)
    (h2 : subject ≠ 2) (h3 : subject ≠ 3) :
    framePortCheck subject req addr len base limit = 1 :=
  framePortDecide_nonholder subject _ _ _ _ addr len base limit h2 h3

theorem port_toUInt64 {x : Nat} (h : x = dhcp ∨ x = echo) :
    x.toUInt64 = 2 ∨ x.toUInt64 = 3 := by
  rcases h with h | h <;> subst h <;> decide

theorem port_toUInt64_eq {x y : Nat} (hx : x = dhcp ∨ x = echo) (hy : y = dhcp ∨ y = echo) :
    x.toUInt64 = y.toUInt64 ↔ y = x := by
  rcases hx with h | h <;> subst h <;> rcases hy with h' | h' <;> subst h' <;> decide

/-- Every reachable route is one of the two ports. -/
theorem Routed.port {s : State} (h : Routed s) : s.route = dhcp ∨ s.route = echo := by
  rcases h with h | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr h

/-- For the windows `p` and a port holder `who` whose window is
`[base, limit)`, in a reachable state, the exported witness accepts a fetch
exactly when the model's `fetchOk` does. -/
theorem framePortCheck_fetch (p : Ports) (s : State) (who : Nat) (addr base limit : UInt64)
    (hwho : who = dhcp ∨ who = echo) (hw : p.window who = some ⟨base.toNat, limit.toNat⟩)
    (hlen : s.rx.length < 2 ^ 64) (hroute : Routed s) :
    framePortCheck who.toUInt64 (request opFetch s.rxPending s.route.toUInt64 who.toUInt64)
        addr s.rx.length.toUInt64 base limit = 0 ↔
      fetchOk p s who addr.toNat = true := by
  rw [framePortCheck_request _ opFetch _ _ _ _ _ _ _ (Or.inl rfl) (port_toUInt64 hroute.port)
    (port_toUInt64 hwho), framePortDecide_fetch_iff]
  have hl : (s.rx.length.toUInt64).toNat = s.rx.length := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt hlen
  have hrt := port_toUInt64_eq hroute.port hwho
  unfold fetchOk
  rw [hw, hl]
  simp only [port_toUInt64 hwho, true_and, hrt, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq]
  cases hp : s.rxPending <;> simp [and_assoc]

/-- For a port holder `who` whose window is `[base, limit)`, in a reachable
state, the exported witness accepts a send exactly when the model's
`sendOk` does. -/
theorem framePortCheck_send (p : Ports) (s : State) (who : Nat) (addr len base limit : UInt64)
    (hwho : who = dhcp ∨ who = echo) (hw : p.window who = some ⟨base.toNat, limit.toNat⟩)
    (hroute : Routed s) :
    framePortCheck who.toUInt64 (request opSend s.txPending s.route.toUInt64 who.toUInt64)
        addr len base limit = 0 ↔
      sendOk p s who addr.toNat len.toNat = true := by
  rw [framePortCheck_request _ opSend _ _ _ _ _ _ _ (Or.inr rfl) (port_toUInt64 hroute.port)
    (port_toUInt64 hwho), framePortDecide_send_iff]
  have hrt := port_toUInt64_eq hroute.port hwho
  unfold sendOk
  rw [hw]
  simp only [port_toUInt64 hwho, true_and, hrt, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq, Bool.not_eq_true']
  cases hp : s.txPending <;> simp [and_assoc]

end LeanOS.DhcpSubject
