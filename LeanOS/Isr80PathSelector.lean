/-!
# isr80's return-path selector (issue #560)

After `syscall_handler` returns, `isr80` in `boot/boot.S` picks the path that
leaves the kernel: return to the caller with the reply word in `rax`, or one
of the switch paths that save the caller and restore another subject.

Until #560 that choice compared the reply word itself with fixed values
(`0xbeef`, `0xcafe`, `0xfeed`, `0xa55a`, `0x3c01`…`0x3c07`, `0x5c01`,
`0x5c02`).  Some replies carry a word a subject chose, so a subject that got
the kernel to reply with one of those values steered `isr80` onto another
path.  Each such path then stopped the machine before `iretq`, so nothing
leaked, but a subject could still crash the kernel on purpose.

Now the choice is a separate typed selector.  `isr80` stores
`LEANOS_ISR80_PATH_REPLY` in the kernel-owned word `isr80_return_path`
before the call.  Only `isr80_select` in `boot/kernel.c` writes it, and a
handler calls it only after its model step has been checked.  After the call
`isr80` loads that word into `rdx` and compares only `rdx`.  A selector the
image does not handle runs `ud2`.

This module describes that ladder as data and proves what the ladder does:

* `dispatch_reads_selector_only`: the ladder reads `rdx` and nothing else;
* `dispatch_function_of_step_path`: the selected target is a function of the
  model's step result alone, and of its `path` field only, not of the reply
  word or the caller's saved registers;
* `dispatch_enter`: a step whose path the image handles selects exactly that
  path;
* `former_magic_inert`: a reply word equal to each former magic value does
  not change the path;
* `legacy_reply_steered`: the old ladder, which compared `rax`, sent an
  ordinary reply equal to a magic value onto a switch path.

`scripts/check-entry-policy.sh` ties the data to the binary:

* the names, codes and asm labels of `Path` must equal
  `include/leanos/isr80-path.h` and the `cmp`/`je` pairs of `isr80`;
* in every final ELF the ladder must be one load of `isr80_return_path`
  into `rdx`, then only `cmp $code,%rdx; je` pairs, then `ud2`.

What this does not prove:

* **No x86 semantics.**  The meaning of `cmp`/`je` is read from the x86
  manual.  The check is that the binary has this shape.
* **The handlers' choices.**  Which path a handler selects is the hand-written
  C in `boot/kernel.c`.  Each switch path's own checks (`switch_complete`,
  `validate_user_return`) still apply after the selection.
-/
namespace LeanOS.Isr80PathSelector

/-- The paths `isr80` can take after `syscall_handler` returns.  Each image
handles the subset its scenario uses. -/
inductive Path where
  /-- Return to the caller with the reply word in `rax`. -/
  | reply
  /-- Install B's complete kernel-owned initial context. -/
  | dispatchFreshB
  /-- B blocked: save B and enter A fresh. -/
  | blockBEnterA
  /-- A's send woke B: save A and restore B. -/
  | wakeB
  /-- B blocked again: save B and resume A (ipc-stream images). -/
  | blockBResumeA
  /-- C blocked on endpoint 12: save C and enter B's initial context. -/
  | blockCEnterB
  /-- B reported: save B and enter A fresh. -/
  | reportBEnterA
  /-- A's send woke C: save A and restore C. -/
  | wakeC
  /-- The server C blocked again: save C and resume its client. -/
  | serverCResumesClient
  /-- The timer server C blocked again: save C and resume A. -/
  | timerCResumesA
  /-- A waits on its wake notification: save A and resume B. -/
  | timerAWaits
  /-- The frame server C decided A's request: save C and resume A. -/
  | frameCResumesA
  /-- B's request woke the frame server: save B and restore C. -/
  | frameBWakesC
  /-- The frame server C decided B's request: save C and resume B. -/
  | frameCResumesB
  /-- B waits for its loaded child: save B and enter the child fresh. -/
  | loaderEnterChild
  /-- The loaded child sent its word: discard it and restore B. -/
  | loaderChildSent
  deriving DecidableEq, Repr

/-- The selector word for each path (`include/leanos/isr80-path.h`). -/
def Path.code : Path → UInt64
  | .reply => 0
  | .dispatchFreshB => 1
  | .blockBEnterA => 2
  | .wakeB => 3
  | .blockBResumeA => 4
  | .blockCEnterB => 5
  | .reportBEnterA => 6
  | .wakeC => 7
  | .serverCResumesClient => 8
  | .timerCResumesA => 9
  | .timerAWaits => 10
  | .frameCResumesA => 11
  | .frameBWakesC => 12
  | .frameCResumesB => 13
  | .loaderEnterChild => 14
  | .loaderChildSent => 15

/-- The C and assembler name of each selector word. -/
def Path.macroName : Path → String
  | .reply => "LEANOS_ISR80_PATH_REPLY"
  | .dispatchFreshB => "LEANOS_ISR80_PATH_DISPATCH_FRESH_B"
  | .blockBEnterA => "LEANOS_ISR80_PATH_BLOCK_B_ENTER_A"
  | .wakeB => "LEANOS_ISR80_PATH_WAKE_B"
  | .blockBResumeA => "LEANOS_ISR80_PATH_BLOCK_B_RESUME_A"
  | .blockCEnterB => "LEANOS_ISR80_PATH_BLOCK_C_ENTER_B"
  | .reportBEnterA => "LEANOS_ISR80_PATH_REPORT_B_ENTER_A"
  | .wakeC => "LEANOS_ISR80_PATH_WAKE_C"
  | .serverCResumesClient => "LEANOS_ISR80_PATH_SERVER_C_RESUMES_CLIENT"
  | .timerCResumesA => "LEANOS_ISR80_PATH_TIMER_C_RESUMES_A"
  | .timerAWaits => "LEANOS_ISR80_PATH_TIMER_A_WAITS"
  | .frameCResumesA => "LEANOS_ISR80_PATH_FRAME_C_RESUMES_A"
  | .frameBWakesC => "LEANOS_ISR80_PATH_FRAME_B_WAKES_C"
  | .frameCResumesB => "LEANOS_ISR80_PATH_FRAME_C_RESUMES_B"
  | .loaderEnterChild => "LEANOS_ISR80_PATH_LOADER_ENTER_CHILD"
  | .loaderChildSent => "LEANOS_ISR80_PATH_LOADER_CHILD_SENT"

/-- The local label in `isr80` that each path's `je` targets. -/
def Path.label : Path → Nat
  | .reply => 7
  | .dispatchFreshB => 11
  | .blockBEnterA => 8
  | .wakeB => 9
  | .blockBResumeA => 10
  | .blockCEnterB => 30
  | .reportBEnterA => 31
  | .wakeC => 32
  | .serverCResumesClient => 33
  | .timerCResumesA => 34
  | .timerAWaits => 35
  | .frameCResumesA => 40
  | .frameBWakesC => 41
  | .frameCResumesB => 42
  | .loaderEnterChild => 50
  | .loaderChildSent => 51

/-- Every path. -/
def allPaths : List Path :=
  [.reply, .dispatchFreshB, .blockBEnterA, .wakeB, .blockBResumeA,
   .blockCEnterB, .reportBEnterA, .wakeC, .serverCResumesClient,
   .timerCResumesA, .timerAWaits, .frameCResumesA, .frameBWakesC,
   .frameCResumesB, .loaderEnterChild, .loaderChildSent]

/-- Distinct paths have distinct selector words. -/
theorem code_injective (a b : Path) (h : a.code = b.code) : a = b := by
  revert h
  cases a <;> cases b <;> decide

/-! ## The machine state the ladder sees -/

/-- The registers and saved frame when the ladder starts: the reply word in
`rax`, the selector in `rdx`, and the caller's twenty saved words (registers
and `iretq` frame), which the caller controls. -/
structure Regs where
  rax : UInt64
  rdx : UInt64
  frame : Fin 20 → UInt64

/-- What one `cmp` may read. -/
inductive Operand where
  | rax
  | rdx
  | frame (index : Fin 20)
  deriving DecidableEq, Repr

def Operand.read : Operand → Regs → UInt64
  | .rax, regs => regs.rax
  | .rdx, regs => regs.rdx
  | .frame index, regs => regs.frame index

/-- Where the ladder can go. -/
inductive Target where
  | path (path : Path)
  | failStop
  deriving DecidableEq, Repr

/-- One rung: `cmp $imm, operand; je target`. -/
structure Rung where
  operand : Operand
  imm : UInt64
  target : Path
  deriving DecidableEq, Repr

/-- Run a ladder: the first rung whose comparison holds wins; otherwise the
ladder falls through to `fallthrough`. -/
def run : List Rung → Target → Regs → Target
  | [], fallthrough, _ => fallthrough
  | rung :: rest, fallthrough, regs =>
      if rung.operand.read regs = rung.imm then .path rung.target
      else run rest fallthrough regs

/-- The reviewed ladder for an image that handles `paths`: one
`cmp $code, %rdx; je label` per path, then `ud2`. -/
def ladder (paths : List Path) : List Rung :=
  paths.map fun path => { operand := .rdx, imm := path.code, target := path }

/-- `isr80`'s choice in an image that handles `paths`. -/
def dispatch (paths : List Path) (regs : Regs) : Target :=
  run (ladder paths) .failStop regs

/-- The model's step result: the reply word and the path the kernel chose. -/
structure Step where
  reply : UInt64
  path : Path

/-- The state the ladder starts from after a step: `rax` holds the reply,
`rdx` the word `isr80` loaded from `isr80_return_path`, and the frame is
whatever the caller left. -/
def enter (step : Step) (frame : Fin 20 → UInt64) : Regs :=
  { rax := step.reply, rdx := step.path.code, frame := frame }

/-! ## The ladder reads only the selector -/

/-- A ladder whose rungs all read `rdx` gives the same result on any two
states with the same `rdx`. -/
theorem run_reads_rdx_only (rungs : List Rung) (fallthrough : Target)
    (hrdx : ∀ rung ∈ rungs, rung.operand = .rdx) (left right : Regs)
    (hsame : left.rdx = right.rdx) :
    run rungs fallthrough left = run rungs fallthrough right := by
  induction rungs with
  | nil => rfl
  | cons rung rest ih =>
      have hoperand : rung.operand = .rdx := hrdx rung (by simp)
      have hrest : ∀ r ∈ rest, r.operand = .rdx :=
        fun r hr => hrdx r (by simp [hr])
      simp only [run, hoperand, Operand.read, hsame, ih hrest]

/-- The reviewed ladder reads `rdx` and nothing else: not the reply word and
not the caller's saved registers. -/
theorem dispatch_reads_selector_only (paths : List Path) (left right : Regs)
    (hsame : left.rdx = right.rdx) :
    dispatch paths left = dispatch paths right := by
  unfold dispatch
  apply run_reads_rdx_only _ _ _ left right hsame
  intro rung hrung
  simp only [ladder, List.mem_map] at hrung
  obtain ⟨_, _, rfl⟩ := hrung
  rfl

/-- The selected target is a function of the step's path alone: two steps
with the same path select the same target, whatever their reply words and
whatever the callers' saved registers. -/
theorem dispatch_function_of_step_path (paths : List Path) (left right : Step)
    (leftFrame rightFrame : Fin 20 → UInt64) (hpath : left.path = right.path) :
    dispatch paths (enter left leftFrame) = dispatch paths (enter right rightFrame) :=
  dispatch_reads_selector_only paths _ _ (by simp [enter, hpath])

/-- The ladder selects the first handled path whose code is the selector. -/
theorem run_ladder_code (paths : List Path) (path : Path) (regs : Regs)
    (hcode : regs.rdx = path.code) :
    run (ladder paths) .failStop regs =
      if path ∈ paths then .path path else .failStop := by
  induction paths with
  | nil => simp [ladder, run]
  | cons head rest ih =>
      simp only [ladder, List.map_cons, run, Operand.read, hcode]
      by_cases hhead : path = head
      · subst hhead
        simp
      · have hne : path.code ≠ head.code := fun h => hhead (code_injective _ _ h)
        simp only [ladder] at ih
        simp [hne, hhead, ih]

/-- A step whose path the image handles selects exactly that path. -/
theorem dispatch_enter (paths : List Path) (step : Step)
    (frame : Fin 20 → UInt64) (hhandled : step.path ∈ paths) :
    dispatch paths (enter step frame) = .path step.path := by
  unfold dispatch
  rw [run_ladder_code paths step.path _ rfl]
  simp [hhandled]

/-- A step whose path the image does not handle stops the machine. -/
theorem dispatch_unhandled_fail_stop (paths : List Path) (step : Step)
    (frame : Fin 20 → UInt64) (hunhandled : step.path ∉ paths) :
    dispatch paths (enter step frame) = .failStop := by
  unfold dispatch
  rw [run_ladder_code paths step.path _ rfl]
  simp [hunhandled]

/-- A selector word that is no path's code stops the machine. -/
theorem dispatch_unknown_selector_fail_stop (paths : List Path) (regs : Regs)
    (hunknown : ∀ path : Path, path.code ≠ regs.rdx) :
    dispatch paths regs = .failStop := by
  unfold dispatch
  induction paths with
  | nil => rfl
  | cons head rest ih =>
      have hne : regs.rdx ≠ head.code := fun h => hunknown head h.symm
      simp only [ladder, List.map_cons, run, Operand.read, hne, ite_false]
      exact ih

/-! ## The former magic values -/

/-- The reply words the old ladder compared, with the path each one chose in
the images that compared it.  `0x3c04` and `0x3c05` chose different paths in
different images; each pair below is one image's choice. -/
def formerMagic : List (UInt64 × Path) :=
  [(0xfeed, .dispatchFreshB), (0xbeef, .blockBEnterA), (0xcafe, .wakeB),
   (0xa55a, .blockBResumeA), (0x3c01, .blockCEnterB),
   (0x3c02, .reportBEnterA), (0x3c03, .wakeC),
   (0x3c04, .serverCResumesClient), (0x3c04, .timerCResumesA),
   (0x3c05, .timerAWaits), (0x3c05, .frameCResumesA),
   (0x3c06, .frameBWakesC), (0x3c07, .frameCResumesB),
   (0x5c01, .loaderEnterChild), (0x5c02, .loaderChildSent)]

/-- A reply word equal to each former magic value does not change the path:
the step selects its own path in every image that handles it. -/
theorem former_magic_inert (paths : List Path) (step : Step)
    (frame : Fin 20 → UInt64) (hhandled : step.path ∈ paths) :
    ∀ magic ∈ formerMagic,
      dispatch paths (enter { step with reply := magic.1 } frame) =
        .path step.path := by
  intro magic _
  exact dispatch_enter paths { step with reply := magic.1 } frame hhandled

/-- In particular an ordinary reply whose word equals a former magic value
returns to the caller. -/
theorem former_magic_reply_returns (paths : List Path)
    (frame : Fin 20 → UInt64) (hreply : Path.reply ∈ paths) :
    ∀ magic ∈ formerMagic,
      dispatch paths (enter { reply := magic.1, path := .reply } frame) =
        .path .reply := by
  intro magic hmagic
  exact former_magic_inert paths { reply := 0, path := .reply } frame hreply
    magic hmagic

/-! ## The old ladder, kept as a record -/

/-- The old ladder of one image: compare `rax` with that image's magic
values, and return to the caller on no match. -/
def legacyDispatch (image : UInt64 × Path) (regs : Regs) : Target :=
  run [{ operand := .rax, imm := image.1, target := image.2 }] (.path .reply) regs

/-- The old ladder was steered by the reply word: for every former magic
value, an ordinary reply carrying it went onto a switch path instead of
back to the caller. -/
theorem legacy_reply_steered (frame : Fin 20 → UInt64) :
    ∀ magic ∈ formerMagic,
      legacyDispatch magic (enter { reply := magic.1, path := .reply } frame) =
          .path magic.2 ∧
        magic.2 ≠ .reply := by
  intro magic hmagic
  simp only [formerMagic, List.mem_cons, List.not_mem_nil, or_false] at hmagic
  rcases hmagic with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst h <;> simp [legacyDispatch, run, enter, Operand.read, Path.code]

end LeanOS.Isr80PathSelector
