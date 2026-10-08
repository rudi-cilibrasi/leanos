import LeanOS.ConsoleServer
import LeanOS.DeviceCapability

/-!
# Keyboard echo: device and console authority stay apart (issue #493)

The `keyboard-echo` boot image puts the device service of issue #449 inside
the console-server image of issue #472. Subject `a` holds the device
capability for the assigned keyboard and a send-only endpoint capability to
the console server; the `server` holds the console capability; `b` holds
nothing. Each key the bound device program yields to `a` is sent to the
server, which writes it through the console capability, so the kernel never
prints the echo on a subject's behalf.

This module composes the two existing models without changing either:
`ConsoleServer` for the console object and endpoint, and `DeviceCapability`
for device capabilities and device state. It proves:

* **Separation** of the installed authority: the device holder holds no
  console capability, and the console holder holds no device capability
  (`device_holder_not_console`, `console_holder_no_device`).
* **Composed confinement**: in the composed system only a console-capability
  holder's action changes the console trace (`composed_console_only_by_holder`),
  and only an invocation by a device-capability holder changes a device's
  state (`composed_device_only_by_holder`, from
  `DeviceCapability.device_state_changes_only_by_holder`). For the installed
  authority the two causes are different subjects (`boot_causes_distinct`).
* **The echo subject cannot invoke the device**: the server is never granted
  the device, so every `bind` or `invoke` it attempts is denied and changes
  nothing (`server_no_device_effects`, from
  `DeviceCapability.ungranted_subject_no_device_effects`).
* **The boot run**: `bootScript` is the booted run as a console-model script;
  its console trace is exactly the typed keys (`boot_output`).

Not modelled: the ring-3 code, the kernel's device capability table (it is
checked at boot against the generated console witness, not derived from this
module), scheduling and the executor. No refinement claim is made.
-/

namespace LeanOS.KeyboardEcho

open LeanOS.ConsoleServer

/-- Boot subject ids, numbered as `ConsoleServer.subjectCode` numbers them
(A = 1, B = 2, server C = 3). -/
def subjectId (s : Subject) : Capability.SubjectId := (subjectCode s).toNat

/-- The device authority the keyboard-echo image installs: only `a` holds a
device capability, for the one assigned device `0` (the q35 xHCI). -/
def bootDeviceCaps : Capability.SubjectId → Option DeviceCapability.DeviceCap :=
  fun s => if s = subjectId .a then some ⟨0⟩ else none

/-! ## Separation of the installed authority -/

/-- The device holder holds no console capability. -/
theorem device_holder_not_console (s : Subject)
    (h : (bootDeviceCaps (subjectId s)).isSome = true) :
    bootAuthority.console s = false := by
  cases s <;> simp_all [bootDeviceCaps, subjectId, subjectCode, bootAuthority]

/-- The console holder holds no device capability. -/
theorem console_holder_no_device (s : Subject) (h : bootAuthority.console s = true) :
    bootDeviceCaps (subjectId s) = none := by
  cases s <;> simp_all [bootDeviceCaps, subjectId, subjectCode, bootAuthority]

/-- The device holder's console write is refused without effect. -/
theorem device_holder_write_refused (st : State) (byte : Nat) :
    step bootAuthority st .a (.write byte) = (st, [(.a, refused)]) :=
  step_of_not_permitted bootAuthority st .a (.write byte) rfl

/-! ## Only console holders change the console trace -/

/-- A step by a subject without the console capability leaves the console
trace unchanged; its send only queues a word for the server. -/
theorem step_output_of_not_console (auth : Authority) (s : State) (who : Subject)
    (op : Op) (h : auth.console who = false) : (step auth s who op).1.output = s.output := by
  cases op <;> simp only [step, h, Bool.false_eq_true, ↓reduceIte] <;> split <;> rfl

/-- A script in which no console holder acts leaves the console trace
unchanged. -/
theorem run_output_without_console (auth : Authority) :
    ∀ (s : State) (script : List (Subject × Op)),
      (∀ action ∈ script, auth.console action.1 = false) →
      (run auth s script).1.output = s.output
  | _, [], _ => rfl
  | s, (who, op) :: rest, h => by
    have hwho := h (who, op) (List.mem_cons_self ..)
    have hrest := run_output_without_console auth (step auth s who op).1 rest
      (fun action hmem => h action (List.mem_cons_of_mem _ hmem))
    simp only [run]
    rw [hrest, step_output_of_not_console auth s who op hwho]

/-! ## The composed system -/

/-- The console object and endpoint, beside the device-capability system. -/
structure Composed (σ : Type) where
  console : State
  device : DeviceCapability.System σ

/-- An action is either a subject's console or endpoint operation, or a
device-capability transition. -/
inductive Action where
  | console (who : Subject) (op : Op)
  | device (t : DeviceCapability.Transition)

/-- One composed step: each action changes only its own half. -/
def cstep {σ} (models : Nat → Wifi.Sim.Device σ) (auth : Authority) (c : Composed σ) :
    Action → Composed σ
  | .console who op => { c with console := (step auth c.console who op).1 }
  | .device t => { c with device := (DeviceCapability.step models c.device t).1 }

/-- Only an action of a console-capability holder changes the console trace. -/
theorem composed_console_only_by_holder {σ} (models : Nat → Wifi.Sim.Device σ)
    (auth : Authority) (c : Composed σ) (action : Action)
    (h : (cstep models auth c action).console.output ≠ c.console.output) :
    ∃ who op, action = .console who op ∧ auth.console who = true := by
  cases action with
  | console who op =>
    refine ⟨who, op, rfl, ?_⟩
    cases hc : auth.console who
    · exact absurd (step_output_of_not_console auth c.console who op hc) h
    · rfl
  | device t => exact absurd rfl h

/-- Only an invocation by a holder of device `k`'s capability changes `k`'s
state. -/
theorem composed_device_only_by_holder {σ} (models : Nat → Wifi.Sim.Device σ)
    (auth : Authority) (c : Composed σ) (action : Action) (k : Nat)
    (h : (cstep models auth c action).device.devState k ≠ c.device.devState k) :
    ∃ subject fuel, action = .device (.invoke subject fuel) ∧
      c.device.deviceCaps subject = some ⟨k⟩ := by
  cases action with
  | console who op => exact absurd rfl h
  | device t =>
    obtain ⟨subject, fuel, ht, hcap⟩ :=
      DeviceCapability.device_state_changes_only_by_holder models c.device t k h
    exact ⟨subject, fuel, by rw [ht], hcap⟩

/-- Under the installed authority, a console byte is caused only by the
server, and a device effect only by `a`. -/
theorem boot_causes_distinct {σ} (models : Nat → Wifi.Sim.Device σ) (c : Composed σ)
    (hcaps : c.device.deviceCaps = bootDeviceCaps) (action : Action) :
    ((cstep models bootAuthority c action).console.output ≠ c.console.output →
      ∃ op, action = .console .server op) ∧
    (∀ k, (cstep models bootAuthority c action).device.devState k ≠ c.device.devState k →
      ∃ fuel, action = .device (.invoke (subjectId .a) fuel)) := by
  constructor
  · intro h
    obtain ⟨who, op, hact, hcon⟩ := composed_console_only_by_holder models bootAuthority c action h
    cases who <;> simp_all [bootAuthority]
  · intro k h
    obtain ⟨subject, fuel, hact, hcap⟩ := composed_device_only_by_holder models bootAuthority c action k h
    rw [hcaps] at hcap
    by_cases hs : subject = subjectId .a
    · exact ⟨fuel, by rw [hact, hs]⟩
    · simp [bootDeviceCaps, hs] at hcap

/-- The echo subject, the console server, is never granted the device: after
any device run without a grant to it, each `bind` or `invoke` it attempts is
denied and leaves the device system, every device's state included,
unchanged. -/
theorem server_no_device_effects {σ} (models : Nat → Wifi.Sim.Device σ)
    (sys : DeviceCapability.System σ) (hcaps : sys.deviceCaps = bootDeviceCaps)
    (ts : List DeviceCapability.Transition)
    (hg : ∀ d, DeviceCapability.Transition.grant (subjectId .server) d ∉ ts) :
    (∀ program, DeviceCapability.step models (DeviceCapability.run models sys ts)
        (.bind (subjectId .server) program) = (DeviceCapability.run models sys ts, .denied)) ∧
    (∀ fuel, DeviceCapability.step models (DeviceCapability.run models sys ts)
        (.invoke (subjectId .server) fuel) = (DeviceCapability.run models sys ts, .denied)) :=
  DeviceCapability.ungranted_subject_no_device_effects models sys (subjectId .server) ts
    (by rw [hcaps]; decide) hg

/-! ## The booted keyboard-echo run -/

/-- The keys typed through QMP in the boot run: `lean ipc` and Enter. -/
def bootKeys : List Nat := [108, 101, 97, 110, 32, 105, 112, 99, 10]

/-- The keyboard-echo boot run as a console-model script: the server reads
the console (no input) and blocks; `b` tries a console write, a send and a
console read; `a` tries a console write; then for each key `a` sends it, the
server receives it, writes it and blocks again. -/
def bootScript : List (Subject × Op) :=
  [(.server, .read), (.server, .receive),
   (.b, .write 88), (.b, .send 66), (.b, .read),
   (.a, .write 65)] ++
  bootKeys.flatMap fun key =>
    [(.a, .send key), (.server, .receive), (.server, .write key), (.server, .receive)]

/-- The boot run's console trace is exactly the typed keys. -/
theorem boot_output : (run bootAuthority initial bootScript).1.output = bootKeys := by
  decide

/-- `b` observes three refusals, one per attempt. -/
theorem boot_b_refused :
    observations .b (run bootAuthority initial bootScript).2 = [refused, refused, refused] := by
  decide

/-- `a`, the device holder, observes its console write refused and every key
send accepted. -/
theorem boot_a_observations :
    observations .a (run bootAuthority initial bootScript).2 =
      refused :: bootKeys.map fun _ => accepted := by
  decide

end LeanOS.KeyboardEcho
