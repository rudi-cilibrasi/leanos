/-!
# Console-server confinement model (issue #472)

Three fixed subjects share one console: the client `a`, a subject `b` with no
console authority, and the console `server`. The console capability, the
authority to emit and to read console bytes, is a kernel object whose
operations are capability-checked (design (a) of #472: the kernel keeps the
UART). Other subjects reach the console only through a send-only endpoint
capability whose receiver is the server.

Authority is static in this model: it has no capability transfer, so the
theorems are about a fixed authority assignment, the one the boot image
installs. The console trace is the console object's byte stream; the kernel's
own diagnostic records are a separate kernel channel and are not modeled.

The two confinement theorems are about a subject `x` that holds neither the
console capability nor an endpoint capability that reaches the server:

* **Integrity** (`console_integrity`): erasing every action of `x` from a
  script leaves the final state, and in particular the console output trace,
  unchanged. Hence two scripts that differ only in `x`'s actions produce equal
  console traces (`console_integrity_pair`).
* **Confidentiality** (`console_confidentiality`): what `x` observes is one
  refusal per action of its own, whatever the console input is.

Neither theorem is a refinement claim about the booted image, a timing claim,
or a claim about the kernel diagnostic stream.
-/

namespace LeanOS.ConsoleServer

/-- The three fixed subjects of the console image. -/
inductive Subject where
  | a
  | b
  | server
  deriving DecidableEq, Repr

/-- Static authority: who holds the console capability, and who holds a
send-only endpoint capability whose receiver is the console server. -/
structure Authority where
  console : Subject → Bool
  reachesServer : Subject → Bool

/-- The authority the console image installs: only the server holds the
console capability, and only `a` holds an endpoint capability to the server. -/
def bootAuthority : Authority where
  console s := s == .server
  reachesServer s := s == .a

/-- A subject is unprivileged for the console when it holds neither the
console capability nor an endpoint capability that reaches the server. -/
def Unprivileged (auth : Authority) (x : Subject) : Prop :=
  auth.console x = false ∧ auth.reachesServer x = false

/-- Subject operations. `serve` is the server's blocking receive on its
endpoint followed by a console write of the received word. `receive` is the
receive alone: the booted server receives a word and then writes its bytes
with separate `write`s. The endpoint's receive right goes with the console
capability here, because the server holds both. -/
inductive Op where
  | send (word : Nat)
  | write (byte : Nat)
  | read
  | serve
  | receive
  deriving DecidableEq, Repr

/-- Console and endpoint state. Observations are not part of it: they are
deliveries returned by each step. -/
structure State where
  /-- Words waiting on the server's endpoint, with their senders. -/
  queue : List (Subject × Nat)
  /-- The console output trace. -/
  output : List Nat
  /-- Console input bytes not yet read. -/
  input : List Nat
  deriving DecidableEq, Repr

/-- Result words delivered to subjects. -/
def accepted : Nat := 0
def refused : Nat := 1
/-- A read of an empty console input delivers this marker. -/
def empty : Nat := 256

/-- One step: the new state and the words delivered to subjects. Every
operation the caller lacks authority for is refused without effect. -/
def step (auth : Authority) (s : State) (who : Subject) : Op → State × List (Subject × Nat)
  | .send word =>
    if auth.reachesServer who then
      ({ s with queue := s.queue ++ [(who, word)] }, [(who, accepted)])
    else (s, [(who, refused)])
  | .write byte =>
    if auth.console who then
      ({ s with output := s.output ++ [byte] }, [(who, accepted)])
    else (s, [(who, refused)])
  | .read =>
    if auth.console who then
      match s.input with
      | [] => (s, [(who, empty)])
      | byte :: rest => ({ s with input := rest }, [(who, byte)])
    else (s, [(who, refused)])
  | .serve =>
    if auth.console who then
      match s.queue with
      | [] => (s, [(who, empty)])
      | (sender, word) :: rest =>
        ({ s with queue := rest, output := s.output ++ [word] },
          [(who, word), (sender, accepted)])
    else (s, [(who, refused)])
  | .receive =>
    if auth.console who then
      match s.queue with
      | [] => (s, [(who, empty)])
      | (_, word) :: rest => ({ s with queue := rest }, [(who, word)])
    else (s, [(who, refused)])

/-- Run a script of (subject, operation) actions, collecting deliveries. -/
def run (auth : Authority) : State → List (Subject × Op) → State × List (Subject × Nat)
  | s, [] => (s, [])
  | s, (who, op) :: rest =>
    let (s', delivered) := step auth s who op
    let (final, later) := run auth s' rest
    (final, delivered ++ later)

/-- What subject `x` observes: the words delivered to it, in order. -/
def observations (x : Subject) (delivered : List (Subject × Nat)) : List Nat :=
  (delivered.filter fun d => d.1 == x).map Prod.snd

/-- The script with every action of `x` removed. -/
def erase (x : Subject) (script : List (Subject × Op)) : List (Subject × Op) :=
  script.filter fun action => action.1 != x

theorem step_unprivileged_state (auth : Authority) (s : State) (x : Subject)
    (op : Op) (hx : Unprivileged auth x) : (step auth s x op).1 = s := by
  obtain ⟨hc, hr⟩ := hx
  cases op <;> simp [step, hc, hr]

theorem step_unprivileged_delivery (auth : Authority) (s : State) (x : Subject)
    (op : Op) (hx : Unprivileged auth x) : (step auth s x op).2 = [(x, refused)] := by
  obtain ⟨hc, hr⟩ := hx
  cases op <;> simp [step, hc, hr]

/-- Integrity: erasing an unprivileged subject's actions does not change the
final state, so in particular not the console output trace. -/
theorem console_integrity (auth : Authority) (x : Subject) (hx : Unprivileged auth x)
    (s : State) (script : List (Subject × Op)) :
    (run auth s script).1 = (run auth s (erase x script)).1 := by
  induction script generalizing s with
  | nil => rfl
  | cons action rest ih =>
    obtain ⟨who, op⟩ := action
    by_cases hwho : who = x
    · subst hwho
      simp only [run, erase, List.filter_cons, bne_self_eq_false, Bool.false_eq_true,
        ↓reduceIte]
      rw [step_unprivileged_state auth s who op hx]
      exact ih s
    · have hkeep : (who != x) = true := by simpa using hwho
      simp only [run, erase, List.filter_cons, hkeep, ↓reduceIte]
      exact ih _

/-- Two scripts that differ only in an unprivileged subject's actions produce
the same console trace. -/
theorem console_integrity_pair (auth : Authority) (x : Subject) (hx : Unprivileged auth x)
    (s : State) (first second : List (Subject × Op))
    (hsame : erase x first = erase x second) :
    (run auth s first).1.output = (run auth s second).1.output := by
  rw [console_integrity auth x hx s first, console_integrity auth x hx s second, hsame]

/-- No queued word was sent by `x`. -/
def NoQueuedFrom (x : Subject) (s : State) : Prop := ∀ entry ∈ s.queue, entry.1 ≠ x

theorem step_preserves_noQueuedFrom (auth : Authority) (x : Subject)
    (hx : Unprivileged auth x) (s : State) (who : Subject) (op : Op)
    (hs : NoQueuedFrom x s) : NoQueuedFrom x (step auth s who op).1 := by
  by_cases hwho : who = x
  · subst hwho; rw [step_unprivileged_state auth s who op hx]; exact hs
  · intro entry hentry
    cases op with
    | send word =>
      simp only [step] at hentry
      split at hentry
      · simp only [List.mem_append, List.mem_singleton] at hentry
        rcases hentry with h | h
        · exact hs entry h
        · subst h; exact hwho
      · exact hs entry hentry
    | write byte =>
      simp only [step] at hentry; split at hentry <;> exact hs entry hentry
    | read =>
      simp only [step] at hentry
      split at hentry
      · split at hentry <;> exact hs entry hentry
      · exact hs entry hentry
    | serve =>
      simp only [step] at hentry
      split at hentry
      · split at hentry
        · exact hs entry hentry
        · rename_i sender word rest hqueue
          exact hs entry (by rw [hqueue]; exact List.mem_cons_of_mem _ hentry)
      · exact hs entry hentry
    | receive =>
      simp only [step] at hentry
      split at hentry
      · split at hentry
        · exact hs entry hentry
        · rename_i sender word rest hqueue
          exact hs entry (by rw [hqueue]; exact List.mem_cons_of_mem _ hentry)
      · exact hs entry hentry

theorem step_observations_other (auth : Authority) (x : Subject) (s : State)
    (who : Subject) (op : Op) (hwho : who ≠ x) (hs : NoQueuedFrom x s) :
    observations x (step auth s who op).2 = [] := by
  have hne : (who == x) = false := by simpa using hwho
  cases op with
  | send word => simp only [step]; split <;> simp [observations, hne]
  | write byte => simp only [step]; split <;> simp [observations, hne]
  | read =>
    simp only [step]; split
    · split <;> simp [observations, hne]
    · simp [observations, hne]
  | serve =>
    simp only [step]; split
    · split
      · simp [observations, hne]
      · rename_i sender word rest hqueue
        have hsender : sender ≠ x := hs (sender, word) (by rw [hqueue]; simp)
        have hsender' : (sender == x) = false := by simpa using hsender
        simp [observations, hne, hsender']
    · simp [observations, hne]
  | receive =>
    simp only [step]; split
    · split <;> simp [observations, hne]
    · simp [observations, hne]

/-- What an unprivileged subject observes is exactly one refusal per action
of its own. -/
theorem unprivileged_observations (auth : Authority) (x : Subject) (hx : Unprivileged auth x)
    (s : State) (hs : NoQueuedFrom x s) (script : List (Subject × Op)) :
    observations x (run auth s script).2 =
      ((script.filter fun action => action.1 == x).map fun _ => refused) := by
  induction script generalizing s with
  | nil => rfl
  | cons action rest ih =>
    obtain ⟨who, op⟩ := action
    have hnext := step_preserves_noQueuedFrom auth x hx s who op hs
    simp only [run, observations, List.filter_append, List.map_append] at ih ⊢
    rw [ih _ hnext]
    by_cases hwho : who = x
    · subst hwho
      rw [step_unprivileged_delivery auth s who op hx]
      simp
    · have hother := step_observations_other auth x s who op hwho hs
      simp only [observations] at hother
      have hne : (who == x) = false := by simpa using hwho
      simp [hother, hne]

/-- Confidentiality: an unprivileged subject's observations do not depend on
the console input. -/
theorem console_confidentiality (auth : Authority) (x : Subject) (hx : Unprivileged auth x)
    (s : State) (hs : NoQueuedFrom x s) (input : List Nat)
    (script : List (Subject × Op)) :
    observations x (run auth s script).2 =
      observations x (run auth { s with input := input } script).2 := by
  rw [unprivileged_observations auth x hx s hs script,
    unprivileged_observations auth x hx { s with input := input } hs script]

theorem bootAuthority_b_unprivileged : Unprivileged bootAuthority .b :=
  ⟨rfl, rfl⟩

/-- The console-image scenario: `a` sends a word, `b` tries to write the
console and to send to the server and is refused, and the server serves. -/
def initial : State := { queue := [], output := [], input := [] }

def demoScript : List (Subject × Op) :=
  [(.a, .send 42), (.b, .write 7), (.b, .send 9), (.server, .serve)]

theorem demo_output : (run bootAuthority initial demoScript).1.output = [42] := by
  decide

theorem demo_b_refused :
    observations .b (run bootAuthority initial demoScript).2 = [refused, refused] := by
  decide

theorem demo_a_accepted :
    observations .a (run bootAuthority initial demoScript).2 = [accepted, accepted] := by
  decide

/-! ## The booted console server (#472 slices 2 and 3)

The `console-server` boot image installs `bootAuthority` as a kernel
capability table: the server's slot 0 is the console object (write and read)
and its slot 1 the receive end of endpoint 12; `a`'s slot 0 is a send-only
endpoint capability to endpoint 12; `b` has no capabilities. The kernel
decides each console and endpoint request from that table and then checks
the decision against `consoleAuthorize`, the generated witness of
`permitted bootAuthority`. A table that granted more than the model would be
caught on the first accepted request outside it; this is a boot-run check,
not a refinement proof. -/

/-- Whether `auth` lets `who` perform `op`: the console capability for the
console operations (and the endpoint receive that goes with it), an endpoint
capability that reaches the server for `send`. -/
def permitted (auth : Authority) (who : Subject) : Op → Bool
  | .send _ => auth.reachesServer who
  | .write _ => auth.console who
  | .read => auth.console who
  | .serve => auth.console who
  | .receive => auth.console who

/-- A request that is not permitted is refused without effect. -/
theorem step_of_not_permitted (auth : Authority) (s : State) (who : Subject) (op : Op)
    (h : permitted auth who op = false) : step auth s who op = (s, [(who, refused)]) := by
  cases op <;> simp_all [step, permitted]

/-- A permitted console write appends exactly its byte to the trace. -/
theorem step_write_of_permitted (auth : Authority) (s : State) (who : Subject) (byte : Nat)
    (h : permitted auth who (.write byte) = true) :
    step auth s who (.write byte) = ({ s with output := s.output ++ [byte] }, [(who, accepted)]) := by
  simp_all [step, permitted]

/-- An unprivileged subject is permitted nothing. -/
theorem unprivileged_not_permitted (auth : Authority) (x : Subject) (hx : Unprivileged auth x)
    (op : Op) : permitted auth x op = false := by
  obtain ⟨hc, hr⟩ := hx
  cases op <;> simp [permitted, hc, hr]

/-- Boot ABI codes for subjects (A = 1, B = 2, server C = 3) and operations
(send 1, console write 2, console read 3, serve 4, receive 5). -/
def subjectCode : Subject → UInt64
  | .a => 1
  | .b => 2
  | .server => 3

def opCode : Op → UInt64
  | .send _ => 1
  | .write _ => 2
  | .read => 3
  | .serve => 4
  | .receive => 5

/-- Witness answers: 1 accept, 2 refuse, 0 outside the ABI. -/
def acceptCode : UInt64 := 1
def refuseCode : UInt64 := 2

/-- Allocation-free boot witness of `permitted bootAuthority`. The literals
need no Lean runtime (ADR 0002); `consoleAuthorize_agrees` ties them to the
model. -/
@[export leanos_console_authorize]
def consoleAuthorize (subject operation : UInt64) : UInt64 :=
  if operation == 0 || operation > 5 then 0
  else if subject == 3 then (if operation == 1 then 2 else 1)
  else if subject == 1 then (if operation == 1 then 1 else 2)
  else if subject == 2 then 2
  else 0

/-- The witness is exactly the model's authority decision for every subject
and operation. -/
theorem consoleAuthorize_agrees (who : Subject) (op : Op) :
    consoleAuthorize (subjectCode who) (opCode op) =
      if permitted bootAuthority who op then acceptCode else refuseCode := by
  cases who <;> cases op <;> rfl

/-- Codes outside the ABI get neither answer. -/
theorem consoleAuthorize_off_domain (subject operation : UInt64)
    (h : operation = 0 ∨ 5 < operation ∨
      (subject ≠ 1 ∧ subject ≠ 2 ∧ subject ≠ 3)) :
    consoleAuthorize subject operation = 0 := by
  unfold consoleAuthorize
  rcases h with h | h | ⟨h1, h2, h3⟩
  · simp [h]
  · simp [h]
  · simp [h1, h2, h3]

/-- Only the server is ever answered "accept" for a console operation, and
only `a` for a send. -/
theorem consoleAuthorize_accepts (subject operation : UInt64)
    (h : consoleAuthorize subject operation = acceptCode) :
    (subject = 3 ∧ operation ≠ 1) ∨ (subject = 1 ∧ operation = 1) := by
  unfold consoleAuthorize acceptCode at h
  split at h
  · exact absurd h (by decide)
  · split at h
    · rename_i hs
      split at h
      · exact absurd h (by decide)
      · rename_i hop
        exact Or.inl ⟨by simpa using hs, by simpa using hop⟩
    · split at h
      · rename_i _ hs
        split at h
        · rename_i hop
          exact Or.inr ⟨by simpa using hs, by simpa using hop⟩
        · exact absurd h (by decide)
      · split at h <;> exact absurd h (by decide)

/-- The words `a` sends in the boot run: the bytes of `hello` and `world`,
least significant byte first, as the server writes them. -/
def bootHello : Nat := 0x6f6c6c6568
def bootWorld : Nat := 0x646c726f77

/-- The console-server boot run as a model script: the server reads the
console (no input) and blocks; `b` tries a console write, a send and a
console read; `a` tries a console write and then sends two words; after each
the server receives the word, writes its five bytes and a newline, and
blocks again. -/
def bootScript : List (Subject × Op) :=
  [(.server, .read), (.server, .receive),
   (.b, .write 88), (.b, .send 66), (.b, .read),
   (.a, .write 65), (.a, .send bootHello),
   (.server, .receive),
   (.server, .write 104), (.server, .write 101), (.server, .write 108),
   (.server, .write 108), (.server, .write 111), (.server, .write 10),
   (.server, .receive),
   (.a, .send bootWorld),
   (.server, .receive),
   (.server, .write 119), (.server, .write 111), (.server, .write 114),
   (.server, .write 108), (.server, .write 100), (.server, .write 10),
   (.server, .receive)]

/-- The boot run's console trace is `hello\nworld\n`. -/
theorem boot_output : (run bootAuthority initial bootScript).1.output =
    [104, 101, 108, 108, 111, 10, 119, 111, 114, 108, 100, 10] := by
  decide

/-- `b` observes three refusals, one per attempt. -/
theorem boot_b_refused :
    observations .b (run bootAuthority initial bootScript).2 = [refused, refused, refused] := by
  decide

/-- `a` observes its console write refused and both sends accepted. -/
theorem boot_a_observations :
    observations .a (run bootAuthority initial bootScript).2 = [refused, accepted, accepted] := by
  decide

/-- The server observes an empty console read, then each delivered word
between empty receives. -/
theorem boot_server_receives :
    (observations .server (run bootAuthority initial bootScript).2).filter (· ≠ accepted) =
      [empty, empty, bootHello, empty, bootWorld, empty] := by
  decide

end LeanOS.ConsoleServer
