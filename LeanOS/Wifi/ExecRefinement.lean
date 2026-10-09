import LeanOS.Wifi.Exec
import LeanOS.DeviceProgramConfinement

/-
The generated executor step is the simulator step (issue #494, ADR 0020).

`LeanOS.Wifi.Exec.step` is generic in its hook carrier. Here the hooks are
read over a simulator `Machine` (`St`, `instHooksSt`): every state hook is
the corresponding update of the machine, every device hook the corresponding
`Device` function, every image hook a field of the `Program`. Under that
reading the step *is* `Sim.step`:

* `step_eq`: on every machine a run can reach (`Inv`: scratch of the
  executor's size, the declared descriptor map holding only scratch pointers),
  for every program the C image parser accepts (`WF`), `decode (Exec.step …)`
  is `Sim.step p d m`;
* `loop_eq`, `run_eq`: the generated loop is `Sim.loop`/`Sim.run`, so
* `run_confined_generated`: `DeviceProgramConfinement.run_confined` holds of
  the generated executor.

What remains trusted is named: the Lean compiler and the C compiler (as for
every boot export, ADR 0002), and that each C hook `wifi_gen_*` in
`hardware/wifi/wifi-gen-exec.h` implements its reading here.
-/
namespace LeanOS.Wifi.ExecRefinement

open LeanOS.Wifi.Bytecode LeanOS.Wifi.Sim
open LeanOS.Wifi.Exec (Hooks stHalt stFail stBadPc stBadOffset stBadOpcode stStack stBadBlob
  stBadMem stPolicy stYield stNext scratch32)

/-! ## The model reading of the hooks -/

/-- A simulator machine with the program and device it runs, the value the
last hook delivered, and the status and code of a finished step. -/
structure St (σ : Type) where
  p : Program
  d : Device σ
  m : Machine σ
  v : UInt64 := 0
  st : UInt32 := stNext
  code : UInt32 := 0

/-- The policy's address sinks (none without a policy). -/
def sinks (p : Program) : List UInt32 := (p.policy.map (·.addrSinks)).getD []

/-- The policy's descriptor map (none without a policy). -/
def descs (p : Program) : List Descriptor := (p.policy.map (·.descriptors)).getD []

/-- Field `i` of an instruction word (`wifi_gen_fetch`). -/
def field (w : Word4) (i : UInt32) : UInt32 :=
  if i = 0 then w.op else if i = 1 then w.a else if i = 2 then w.b else if i = 3 then w.c else 0

def boolVal (b : Bool) : UInt64 := if b then 1 else 0

variable {σ : Type}

/-- The hooks over a machine: `hardware/wifi/wifi-gen-exec.h` implements
each of them in C over `struct wifi_vm` and the WH_* device hooks. -/
instance instHooksSt : Hooks (St σ) where
  val s := s.v
  withVal s x := { s with v := x }
  window s := s.p.effTarget.windowBytes
  blobLen s := s.p.blob.size.toUInt32
  blobWord s off := le32 s.p.blob off.toNat
  polPresent s := if s.p.policy.isSome then 1 else 0
  polDma s := if (s.p.policy.map (·.dma)).getD false then 1 else 0
  polCfgRead s := (s.p.policy.map (·.cfgRead)).getD 0
  polCfgWrite s := (s.p.policy.map (·.cfgWrite)).getD 0
  polCmdClear s := (s.p.policy.map (·.cmdClear)).getD 0
  polCmdSet s := (s.p.policy.map (·.cmdSet)).getD 0
  polSinks s := (sinks s.p).length.toUInt32
  polSink s i := (sinks s.p).getD i.toNat 0
  polDescs s := (descs s.p).length.toUInt32
  polDescTrb s k := if ((descs s.p).getD k.toNat default).trb then 1 else 0
  polDescStart s k := ((descs s.p).getD k.toNat default).start
  polDescCount s k := ((descs s.p).getD k.toNat default).count
  polDescStride s k := ((descs s.p).getD k.toNat default).stride
  pcOk s := { s with v := boolVal (decide (s.m.pc < s.p.words.size)) }
  fetch s i := { s with v := (field (s.p.words.getD s.m.pc default) i).toUInt64 }
  advance s := { s with m := { s.m with pc := s.m.pc + 1, steps := s.m.steps + 1 } }
  jump s target := { s with m := { s.m with pc := target.toNat } }
  stackFull s := { s with v := boolVal (decide (s.m.stack.length ≥ 16)) }
  stackEmpty s := { s with v := boolVal s.m.stack.isEmpty }
  call s target := { s with m := { s.m with stack := s.m.pc :: s.m.stack, pc := target.toNat } }
  ret s := match s.m.stack with
    | [] => s
    | r :: rest => { s with m := { s.m with stack := rest, pc := r } }
  regGet s r := { s with v := (s.m.reg r).toUInt64 }
  regSet s r x := { s with m := s.m.setReg r x }
  memLoad s at_ w := { s with v := (memLoad s.m.mem at_.toNat w.toNat).toUInt64 }
  memStore s at_ w x := { s with m := { s.m with mem := memStore s.m.mem at_.toNat w.toNat x } }
  mmioRead32 s off :=
    let r := s.d.read32 s.m.dev off
    { s with v := r.1.toUInt64, m := { s.m with dev := r.2 } }
  mmioRead16 s off :=
    let r := s.d.read16 s.m.dev off
    { s with v := r.1.toUInt32.toUInt64, m := { s.m with dev := r.2 } }
  mmioRead8 s off :=
    let r := s.d.read8 s.m.dev off
    { s with v := r.1.toUInt32.toUInt64, m := { s.m with dev := r.2 } }
  mmioWrite32 s off x := { s with m := { s.m with dev := s.d.write32 s.m.dev off x } }
  mmioWrite16 s off x := { s with m := { s.m with dev := s.d.write16 s.m.dev off x.toUInt16 } }
  mmioWrite8 s off x := { s with m := { s.m with dev := s.d.write8 s.m.dev off x.toUInt8 } }
  cfgRead s off :=
    let r := s.d.cfgRead32 s.m.dev off
    { s with v := r.1.toUInt64, m := { s.m with dev := r.2 } }
  cfgWrite s off x := { s with m := { s.m with dev := s.d.cfgWrite32 s.m.dev off x } }
  cfgUpdate s off c t := { s with m := { s.m with dev := s.d.cfgUpdate32 s.m.dev off c t } }
  phys s off :=
    let r := s.d.phys s.m.dev off
    { s with v := r.1.toUInt64, m := { s.m with dev := r.2 } }
  physBase s := { s with v := (s.d.phys s.m.dev 0).1.toUInt64 }
  delay s _ := s
  print s tag x := { s with m := { s.m with prints := s.m.prints.push (tag, x) } }
  done s st code := { s with st, code }

/-! ### The hooks unfolded -/

@[simp] theorem hook_val (s : St σ) :
    Hooks.val s = s.v := rfl

@[simp] theorem hook_withVal (s : St σ) (x : UInt64) :
    Hooks.withVal s x = { s with v := x } := rfl

@[simp] theorem hook_window (s : St σ) :
    Hooks.window s = s.p.effTarget.windowBytes := rfl

@[simp] theorem hook_blobLen (s : St σ) :
    Hooks.blobLen s = s.p.blob.size.toUInt32 := rfl

@[simp] theorem hook_blobWord (s : St σ) (off : UInt32) :
    Hooks.blobWord s off = le32 s.p.blob off.toNat := rfl

@[simp] theorem hook_polPresent (s : St σ) :
    Hooks.polPresent s = if s.p.policy.isSome then 1 else 0 := rfl

@[simp] theorem hook_polDma (s : St σ) :
    Hooks.polDma s = if (s.p.policy.map (·.dma)).getD false then 1 else 0 := rfl

@[simp] theorem hook_polCfgRead (s : St σ) :
    Hooks.polCfgRead s = (s.p.policy.map (·.cfgRead)).getD 0 := rfl

@[simp] theorem hook_polCfgWrite (s : St σ) :
    Hooks.polCfgWrite s = (s.p.policy.map (·.cfgWrite)).getD 0 := rfl

@[simp] theorem hook_polCmdClear (s : St σ) :
    Hooks.polCmdClear s = (s.p.policy.map (·.cmdClear)).getD 0 := rfl

@[simp] theorem hook_polCmdSet (s : St σ) :
    Hooks.polCmdSet s = (s.p.policy.map (·.cmdSet)).getD 0 := rfl

@[simp] theorem hook_polSinks (s : St σ) :
    Hooks.polSinks s = (sinks s.p).length.toUInt32 := rfl

@[simp] theorem hook_polSink (s : St σ) (i : UInt32) :
    Hooks.polSink s i = (sinks s.p).getD i.toNat 0 := rfl

@[simp] theorem hook_polDescs (s : St σ) :
    Hooks.polDescs s = (descs s.p).length.toUInt32 := rfl

@[simp] theorem hook_polDescTrb (s : St σ) (k : UInt32) :
    Hooks.polDescTrb s k = if ((descs s.p).getD k.toNat default).trb then 1 else 0 := rfl

@[simp] theorem hook_polDescStart (s : St σ) (k : UInt32) :
    Hooks.polDescStart s k = ((descs s.p).getD k.toNat default).start := rfl

@[simp] theorem hook_polDescCount (s : St σ) (k : UInt32) :
    Hooks.polDescCount s k = ((descs s.p).getD k.toNat default).count := rfl

@[simp] theorem hook_polDescStride (s : St σ) (k : UInt32) :
    Hooks.polDescStride s k = ((descs s.p).getD k.toNat default).stride := rfl

@[simp] theorem hook_pcOk (s : St σ) :
    Hooks.pcOk s = { s with v := boolVal (decide (s.m.pc < s.p.words.size)) } := rfl

@[simp] theorem hook_fetch (s : St σ) (i : UInt32) :
    Hooks.fetch s i = { s with v := (field (s.p.words.getD s.m.pc default) i).toUInt64 } := rfl

@[simp] theorem hook_advance (s : St σ) :
    Hooks.advance s = { s with m := { s.m with pc := s.m.pc + 1, steps := s.m.steps + 1 } } := rfl

@[simp] theorem hook_jump (s : St σ) (target : UInt32) :
    Hooks.jump s target = { s with m := { s.m with pc := target.toNat } } := rfl

@[simp] theorem hook_stackFull (s : St σ) :
    Hooks.stackFull s = { s with v := boolVal (decide (s.m.stack.length ≥ 16)) } := rfl

@[simp] theorem hook_stackEmpty (s : St σ) :
    Hooks.stackEmpty s = { s with v := boolVal s.m.stack.isEmpty } := rfl

@[simp] theorem hook_call (s : St σ) (target : UInt32) :
    Hooks.call s target = { s with m := { s.m with stack := s.m.pc :: s.m.stack, pc := target.toNat } } := rfl

@[simp] theorem hook_ret (s : St σ) :
    Hooks.ret s = match s.m.stack with
      | [] => s
      | r :: rest => { s with m := { s.m with stack := rest, pc := r } } := rfl

@[simp] theorem hook_regGet (s : St σ) (r : UInt32) :
    Hooks.regGet s r = { s with v := (s.m.reg r).toUInt64 } := rfl

@[simp] theorem hook_regSet (s : St σ) (r : UInt32) (x : UInt32) :
    Hooks.regSet s r x = { s with m := s.m.setReg r x } := rfl

@[simp] theorem hook_memLoad (s : St σ) (at_ : UInt32) (w : UInt32) :
    Hooks.memLoad s at_ w = { s with v := (memLoad s.m.mem at_.toNat w.toNat).toUInt64 } := rfl

@[simp] theorem hook_memStore (s : St σ) (at_ : UInt32) (w : UInt32) (x : UInt32) :
    Hooks.memStore s at_ w x = { s with m := { s.m with mem := memStore s.m.mem at_.toNat w.toNat x } } := rfl

@[simp] theorem hook_mmioRead32 (s : St σ) (off : UInt32) :
    Hooks.mmioRead32 s off =
      { s with v := (s.d.read32 s.m.dev off).1.toUInt64, m := { s.m with dev := (s.d.read32 s.m.dev off).2 } } := rfl

@[simp] theorem hook_mmioRead16 (s : St σ) (off : UInt32) :
    Hooks.mmioRead16 s off =
      { s with v := (s.d.read16 s.m.dev off).1.toUInt32.toUInt64,
               m := { s.m with dev := (s.d.read16 s.m.dev off).2 } } := rfl

@[simp] theorem hook_mmioRead8 (s : St σ) (off : UInt32) :
    Hooks.mmioRead8 s off =
      { s with v := (s.d.read8 s.m.dev off).1.toUInt32.toUInt64,
               m := { s.m with dev := (s.d.read8 s.m.dev off).2 } } := rfl

@[simp] theorem hook_mmioWrite32 (s : St σ) (off : UInt32) (x : UInt32) :
    Hooks.mmioWrite32 s off x = { s with m := { s.m with dev := s.d.write32 s.m.dev off x } } := rfl

@[simp] theorem hook_mmioWrite16 (s : St σ) (off : UInt32) (x : UInt32) :
    Hooks.mmioWrite16 s off x = { s with m := { s.m with dev := s.d.write16 s.m.dev off x.toUInt16 } } := rfl

@[simp] theorem hook_mmioWrite8 (s : St σ) (off : UInt32) (x : UInt32) :
    Hooks.mmioWrite8 s off x = { s with m := { s.m with dev := s.d.write8 s.m.dev off x.toUInt8 } } := rfl

@[simp] theorem hook_cfgRead (s : St σ) (off : UInt32) :
    Hooks.cfgRead s off =
      { s with v := (s.d.cfgRead32 s.m.dev off).1.toUInt64,
               m := { s.m with dev := (s.d.cfgRead32 s.m.dev off).2 } } := rfl

@[simp] theorem hook_cfgWrite (s : St σ) (off : UInt32) (x : UInt32) :
    Hooks.cfgWrite s off x = { s with m := { s.m with dev := s.d.cfgWrite32 s.m.dev off x } } := rfl

@[simp] theorem hook_cfgUpdate (s : St σ) (off : UInt32) (c : UInt32) (t : UInt32) :
    Hooks.cfgUpdate s off c t = { s with m := { s.m with dev := s.d.cfgUpdate32 s.m.dev off c t } } := rfl

@[simp] theorem hook_phys (s : St σ) (off : UInt32) :
    Hooks.phys s off =
      { s with v := (s.d.phys s.m.dev off).1.toUInt64, m := { s.m with dev := (s.d.phys s.m.dev off).2 } } := rfl

@[simp] theorem hook_physBase (s : St σ) :
    Hooks.physBase s = { s with v := (s.d.phys s.m.dev 0).1.toUInt64 } := rfl

@[simp] theorem hook_delay (s : St σ) (x : UInt32) :
    Hooks.delay s x = s := rfl

@[simp] theorem hook_print (s : St σ) (tag : UInt32) (x : UInt32) :
    Hooks.print s tag x = { s with m := { s.m with prints := s.m.prints.push (tag, x) } } := rfl

theorem hook_done (s : St σ) (st : UInt32) (code : UInt32) :
    Hooks.done s st code = { s with st, code } := rfl

/-- The simulator status a finished step's code names. -/
def statusOf (st code : UInt32) : Status :=
  if st = stHalt then .halt else if st = stFail then .fail code
  else if st = stYield then .yield code
  else .error (if st = stBadPc then "bad-pc" else if st = stBadOffset then "bad-offset"
    else if st = stBadOpcode then "bad-opcode" else if st = stStack then "stack"
    else if st = stBadBlob then "bad-blob" else if st = stBadMem then "bad-mem"
    else if st = stPolicy then "policy" else "unknown")

/-- The simulator result of a finished step. -/
def decode (s : St σ) : Step σ :=
  if s.st = stNext then .next s.m else .stop (statusOf s.st s.code) s.m

/-! ## Fixed-width checks equal the simulator's -/

theorem mmioOk_eq (window off w : UInt32) : Exec.mmioOk window off w = Sim.mmioOk window off w := by
  unfold Exec.mmioOk Sim.mmioOk
  have := off.toNat_lt
  have := w.toNat_lt
  have h : (off.toUInt64 + w.toUInt64 ≤ window.toUInt64) ↔ off.toNat + w.toNat ≤ window.toNat := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_add]
    simp only [UInt32.toNat_toUInt64]
    omega
  simp only [h]

theorem ptrOk_eq (base lo hi : UInt32) : Exec.ptrOk base lo hi = Bytecode.ptrOk base lo hi := rfl

theorem cfgAllowed_eq (bits : UInt64) (off : UInt32) :
    Exec.cfgAllowed bits off = Bytecode.cfgAllowed bits off := rfl

theorem cfgOffOk_eq (off : UInt32) : Exec.cfgOffOk off = Sim.cfgOffOk off := rfl

theorem trbPtr_eq (ctl : UInt32) : Exec.trbPtr ctl = Descriptor.trbParamIsPtr ctl := rfl

theorem aluOp_eq (sub x v : UInt32) :
    Sim.aluOp sub x v = if Exec.aluKnown sub then some (Exec.alu sub x v) else none := by
  unfold Sim.aluOp
  split
  any_goals rfl
  rename_i h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  have : ¬ sub ≤ 14 := by
    simp only [UInt32.le_iff_toNat_le, ← UInt32.toNat_inj, UInt32.reduceToNat, imp_false] at *
    omega
  simp [Exec.aluKnown, this]

theorem condOp_eq (sub x v : UInt32) :
    Sim.condOp sub x v = if Exec.condKnown sub then some (Exec.cond sub x v) else none := by
  unfold Sim.condOp
  split
  any_goals rfl
  rename_i h0 h1 h2 h3 h4 h5
  have : ¬ sub ≤ 5 := by
    simp only [UInt32.le_iff_toNat_le, ← UInt32.toNat_inj, UInt32.reduceToNat, imp_false] at *
    omega
  simp [Exec.condKnown, this]


@[simp] theorem decode_next (s : St σ) : decode (Hooks.done s stNext 0) = .next s.m := rfl
@[simp] theorem decode_halt (s : St σ) : decode (Hooks.done s stHalt 0) = .stop .halt s.m := rfl
@[simp] theorem decode_fail (s : St σ) (c : UInt32) :
    decode (Hooks.done s stFail c) = .stop (.fail c) s.m := rfl
@[simp] theorem decode_yield (s : St σ) (c : UInt32) :
    decode (Hooks.done s stYield c) = .stop (.yield c) s.m := rfl
@[simp] theorem decode_badPc (s : St σ) :
    decode (Hooks.done s stBadPc 0) = .stop (.error "bad-pc") s.m := rfl
@[simp] theorem decode_badOffset (s : St σ) :
    decode (Hooks.done s stBadOffset 0) = .stop (.error "bad-offset") s.m := rfl
@[simp] theorem decode_badOpcode (s : St σ) :
    decode (Hooks.done s stBadOpcode 0) = .stop (.error "bad-opcode") s.m := rfl
@[simp] theorem decode_stack (s : St σ) :
    decode (Hooks.done s stStack 0) = .stop (.error "stack") s.m := rfl
@[simp] theorem decode_badBlob (s : St σ) :
    decode (Hooks.done s stBadBlob 0) = .stop (.error "bad-blob") s.m := rfl
@[simp] theorem decode_badMem (s : St σ) :
    decode (Hooks.done s stBadMem 0) = .stop (.error "bad-mem") s.m := rfl
@[simp] theorem decode_policy (s : St σ) :
    decode (Hooks.done s stPolicy 0) = .stop (.error "policy") s.m := rfl

@[simp] theorem operand_eq (s : St σ) (imm : Bool) (x : UInt32) :
    Exec.operand s imm x = { s with v := if imm then s.v else (s.m.reg x).toUInt64 } := by
  cases imm <;> rfl

@[simp] theorem operandVal_eq (p : Program) (d : Device σ) (m : Machine σ) (w : UInt64)
    (st code : UInt32) (imm : Bool) (x : UInt32) :
    Exec.operandVal ({ p, d, m, v := if imm then w else (m.reg x).toUInt64, st, code } : St σ) imm x =
      if imm then x else m.reg x := by
  cases imm <;> simp [Exec.operandVal, Exec.word]

@[simp] theorem flag_ne (b : Bool) : ((if b then (1 : UInt32) else 0) != 0) = b := by
  cases b <;> rfl

@[simp] theorem flag_beq (b : Bool) : ((if b then (1 : UInt32) else 0) == 0) = !b := by
  cases b <;> rfl

theorem ite_next (c : Prop) [Decidable c] (x y : Machine σ) :
    (if c then Step.next x else Step.next y) = Step.next (if c then x else y) := by
  split <;> rfl

theorem scratch32_toNat : scratch32.toNat = scratchBytes := rfl

@[simp] theorem boolVal_ne (b : Bool) : (boolVal b != 0) = b := by cases b <;> rfl

@[simp] theorem flag64_ne (b : Bool) : ((if b then (1 : UInt64) else 0) != 0) = b := by
  cases b <;> rfl

/-! ## Policy loops -/

theorem toNat_succ {i n : UInt32} (h : i < n) : (i + 1).toNat = i.toNat + 1 := by
  have hi : i.toNat < n.toNat := h
  have := n.toNat_lt
  rw [UInt32.toNat_add]; simp only [UInt32.toNat_one]; omega

theorem lt_len {i : UInt32} {l : List α} (hl : l.length < 2 ^ 32) :
    i < l.length.toUInt32 ↔ i.toNat < l.length := by
  rw [UInt32.lt_iff_toNat_lt, Nat.toUInt32, UInt32.toNat_ofNat']
  rw [Nat.mod_eq_of_lt hl]

theorem getD_lt {l : List α} {i : Nat} {d : α} (h : i < l.length) : l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

theorem sinkTouchFrom_eq (s : St σ) (off : UInt32) (h : (sinks s.p).length < 2 ^ 32) (i : UInt32) :
    Exec.sinkTouchFrom s off i = ((sinks s.p).drop i.toNat).any (fun x => off - x < 8) := by
  fun_induction Exec.sinkTouchFrom s off i with
  | case1 i hi hc =>
    rw [hook_polSinks, lt_len h] at hi
    rw [hook_polSink, getD_lt hi] at hc
    rw [List.drop_eq_getElem_cons hi, List.any_cons]
    simp [hc]
  | case2 i hi hc ih =>
    have hs := toNat_succ hi
    rw [hook_polSinks, lt_len h] at hi
    rw [hook_polSink, getD_lt hi] at hc
    rw [List.drop_eq_getElem_cons hi, List.any_cons, ih, hs]
    simp [hc]
  | case3 i hi =>
    rw [hook_polSinks, lt_len h] at hi
    rw [List.drop_eq_nil_of_le (by omega)]
    rfl

theorem sinkIsFrom_eq (s : St σ) (off : UInt32) (h : (sinks s.p).length < 2 ^ 32) (i : UInt32) :
    Exec.sinkIsFrom s off i = ((sinks s.p).drop i.toNat).any (fun x => x == off) := by
  fun_induction Exec.sinkIsFrom s off i with
  | case1 i hi hc =>
    rw [hook_polSinks, lt_len h] at hi
    rw [hook_polSink, getD_lt hi] at hc
    rw [List.drop_eq_getElem_cons hi, List.any_cons]
    simp [hc]
  | case2 i hi hc ih =>
    have hs := toNat_succ hi
    rw [hook_polSinks, lt_len h] at hi
    rw [hook_polSink, getD_lt hi] at hc
    rw [List.drop_eq_getElem_cons hi, List.any_cons, ih, hs]
    simp [hc]
  | case3 i hi =>
    rw [hook_polSinks, lt_len h] at hi
    rw [List.drop_eq_nil_of_le (by omega)]
    rfl

/-- `Descriptor.limit` in 64-bit arithmetic. -/
def limit64 (d : Descriptor) : UInt64 :=
  d.start.toUInt64 + d.stride.toUInt64 * (if d.count == 0 then 0 else d.count - 1).toUInt64 +
    (if (if d.trb then (1 : UInt32) else 0) != 0 then 16 else 8)

@[simp] theorem one_bne_zero : ((1 : UInt32) != 0) = true := rfl

theorem limit64_toNat (d : Descriptor) : (limit64 d).toNat = d.limit := by
  have h1 := d.start.toNat_lt
  have h2 := d.stride.toNat_lt
  have h3 := d.count.toNat_lt
  have hc : (if d.count == 0 then (0 : UInt32) else d.count - 1).toNat = d.count.toNat - 1 := by
    by_cases h : d.count = 0
    · simp [h]
    · have : d.count.toNat ≠ 0 := by
        intro h'; exact h (UInt32.toNat_inj.mp (by simpa using h'))
      simp only [beq_iff_eq, h, ite_false, UInt32.toNat_sub, UInt32.toNat_one]
      omega
  have hm : d.stride.toNat * (d.count.toNat - 1) < 2 ^ 64 := by
    have : d.stride.toNat * (d.count.toNat - 1) ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have : (2 ^ 32 - 1) * (2 ^ 32 - 1) < 2 ^ 64 := by decide
    omega
  have hm' : d.stride.toNat * (d.count.toNat - 1) ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  simp only [limit64, Descriptor.limit, Descriptor.addr, Descriptor.size]
  cases d.trb <;>
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt32.toNat_toUInt64, hc, Bool.false_eq_true,
      ite_false, ite_true, one_bne_zero, bne_self_eq_false] <;> simp <;> omega

theorem descLimit_eq (s : St σ) {k : UInt32} (hk : k.toNat < (descs s.p).length) :
    Exec.descLimit s k = limit64 (descs s.p)[k.toNat] := by
  simp only [Exec.descLimit, hook_polDescCount, hook_polDescStart, hook_polDescStride,
    hook_polDescTrb, getD_lt hk, limit64]

theorem descTouchFrom_eq (s : St σ) (at_ len : UInt64) (h : (descs s.p).length < 2 ^ 32)
    (k : UInt32) :
    Exec.descTouchFrom s at_ len k =
      ((descs s.p).drop k.toNat).any (fun d => at_ < limit64 d && d.start.toUInt64 < at_ + len) := by
  fun_induction Exec.descTouchFrom s at_ len k with
  | case1 k hk hc =>
    rw [hook_polDescs, lt_len h] at hk
    rw [descLimit_eq s hk, hook_polDescStart, getD_lt hk] at hc
    rw [List.drop_eq_getElem_cons hk, List.any_cons, hc, Bool.true_or]
  | case2 k hk hc ih =>
    have hs := toNat_succ hk
    rw [hook_polDescs, lt_len h] at hk
    rw [descLimit_eq s hk, hook_polDescStart, getD_lt hk, Bool.not_eq_true] at hc
    rw [List.drop_eq_getElem_cons hk, List.any_cons, ih, hs, hc, Bool.false_or]
  | case3 k hk =>
    rw [hook_polDescs, lt_len h] at hk
    rw [List.drop_eq_nil_of_le (by omega)]
    rfl

/-! ## Scratch bytes -/

theorem get!_set! (b : ByteArray) (i j : Nat) (x : UInt8) :
    (b.set! i x).get! j = if i = j ∧ i < b.size then x else b.get! j := by
  cases b with
  | mk data =>
    simp only [ByteArray.set!, ByteArray.get!, ByteArray.size]
    rw [getElem!_def, getElem!_def, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    by_cases hij : i = j
    · subst hij
      by_cases hs : i < data.size
      · simp [hs]
      · simp [hs]
    · simp [hij]

theorem memStore_foldl (mem : ByteArray) (at_ w : Nat) (v : UInt32) :
    memStore mem at_ w v =
      (List.range' 0 w).foldl (fun b i => b.set! (at_ + i) (v >>> (8 * UInt32.ofNat i)).toUInt8) mem := by
  simp [memStore]

theorem foldl_set_size (v : UInt32) (at_ : Nat) :
    ∀ (l : List Nat) (mem : ByteArray),
      (l.foldl (fun b i => b.set! (at_ + i) (v >>> (8 * UInt32.ofNat i)).toUInt8) mem).size = mem.size
  | [], _ => rfl
  | i :: l, mem => by
    rw [List.foldl_cons, foldl_set_size v at_ l]
    simp

theorem memStore_size (mem : ByteArray) (at_ w : Nat) (v : UInt32) :
    (memStore mem at_ w v).size = mem.size := by
  rw [memStore_foldl, foldl_set_size]

/-- Byte `k` of a stored word. -/
def byteOf (v : UInt32) (k : Nat) : UInt8 := (v >>> (8 * UInt32.ofNat k)).toUInt8

theorem foldl_set_get (v : UInt32) (at_ j : Nat) :
    ∀ (n s : Nat) (mem : ByteArray),
      ((List.range' s n).foldl
          (fun b i => b.set! (at_ + i) (v >>> (8 * UInt32.ofNat i)).toUInt8) mem).get! j =
        if at_ + s ≤ j ∧ j < at_ + s + n ∧ j < mem.size then byteOf v (j - at_) else mem.get! j
  | 0, s, mem => by
    have : ¬(at_ + s ≤ j ∧ j < at_ + s + 0 ∧ j < mem.size) := by omega
    simp only [List.range'_zero, List.foldl_nil, this, ite_false]
  | n + 1, s, mem => by
    rw [List.range'_succ, List.foldl_cons, foldl_set_get v at_ j n (s + 1), get!_set!]
    simp only [ByteArray.size_set!]
    by_cases h1 : at_ + s = j
    · subst h1
      by_cases h2 : at_ + s < mem.size
      · simp [h2, byteOf, Nat.add_sub_cancel_left]
      · simp [h2]
    · have : (at_ + (s + 1) ≤ j ∧ j < at_ + (s + 1) + n ∧ j < mem.size) ↔
          (at_ + s ≤ j ∧ j < at_ + s + (n + 1) ∧ j < mem.size) := by omega
      simp only [this, h1, false_and, ite_false]

/-- A store changes exactly the bytes it names inside scratch. -/
theorem memStore_get (mem : ByteArray) (at_ w j : Nat) (v : UInt32) :
    (memStore mem at_ w v).get! j =
      if at_ ≤ j ∧ j < at_ + w ∧ j < mem.size then byteOf v (j - at_) else mem.get! j := by
  rw [memStore_foldl, foldl_set_get]
  simp

theorem memStore_get_out (mem : ByteArray) (at_ w j : Nat) (v : UInt32) (h : j < at_ ∨ at_ + w ≤ j) :
    (memStore mem at_ w v).get! j = mem.get! j := by
  rw [memStore_get]
  have : ¬(at_ ≤ j ∧ j < at_ + w ∧ j < mem.size) := by omega
  simp [this]

theorem memLoad_four (mem : ByteArray) (a : Nat) :
    memLoad mem a 4 = (mem.get! a).toUInt32 ||| ((mem.get! (a + 1)).toUInt32 <<< 8) |||
      ((mem.get! (a + 2)).toUInt32 <<< 16) ||| ((mem.get! (a + 3)).toUInt32 <<< 24) := by
  simp [memLoad, List.range']

theorem memLoad_one (mem : ByteArray) (a : Nat) : memLoad mem a 1 = (mem.get! a).toUInt32 := by
  simp [memLoad]

/-- A 4-byte load depends only on its four bytes. -/
theorem le32_congr {m₁ m₂ : ByteArray} {a : Nat} (h : ∀ k, k < 4 → m₁.get! (a + k) = m₂.get! (a + k)) :
    le32 m₁ a = le32 m₂ a := by
  simp only [le32, memLoad_four]
  have h0 := h 0 (by omega)
  have h1 := h 1 (by omega)
  have h2 := h 2 (by omega)
  have h3 := h 3 (by omega)
  simp only [Nat.add_zero] at h0
  rw [h0, h1, h2, h3]

/-! ## The descriptor map reads only its regions -/

theorem all_congr' {l : List α} {f g : α → Bool} (h : ∀ x ∈ l, f x = g x) : l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.all_cons]
    rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

theorem addr_le_limit (d : Descriptor) {i : Nat} (hi : i < d.count.toNat) :
    d.start.toNat ≤ d.addr i ∧ d.addr i + d.size ≤ d.limit := by
  have : d.stride.toNat * i ≤ d.stride.toNat * (d.count.toNat - 1) :=
    Nat.mul_le_mul_left _ (by omega)
  simp only [Descriptor.addr, Descriptor.limit]
  omega

/-- `descOk` depends only on the bytes of the map's regions. -/
theorem descOk_congr (π : Policy) (base : UInt32) {m₁ m₂ : ByteArray}
    (h : ∀ d ∈ π.descriptors, ∀ j, d.start.toNat ≤ j → j < d.limit → m₁.get! j = m₂.get! j) :
    descOk π base m₁ = descOk π base m₂ := by
  unfold descOk
  refine all_congr' fun d hd => all_congr' fun i hi => ?_
  have hi' : i < d.count.toNat := List.mem_range.mp hi
  obtain ⟨hlo, hhi⟩ := addr_le_limit d hi'
  have hb : ∀ k, k < d.size → m₁.get! (d.addr i + k) = m₂.get! (d.addr i + k) :=
    fun k hk => h d hd _ (by omega) (by omega)
  have h0 : le32 m₁ (d.addr i) = le32 m₂ (d.addr i) :=
    le32_congr fun k hk => hb k (by simp only [Descriptor.size]; split <;> omega)
  have h4 : le32 m₁ (d.addr i + 4) = le32 m₂ (d.addr i + 4) :=
    le32_congr fun k hk => by
      rw [Nat.add_assoc]; exact hb (4 + k) (by simp only [Descriptor.size]; split <;> omega)
  cases htrb : d.trb
  · simp only [Bool.false_and, Bool.false_or, h0, h4]
  · have hsz : d.size = 16 := by simp [Descriptor.size, htrb]
    have h12 : le32 m₁ (d.addr i + 12) = le32 m₂ (d.addr i + 12) :=
      le32_congr fun k hk => by
        rw [Nat.add_assoc]; exact hb (12 + k) (by omega)
    simp only [h0, h4, h12]

/-- **Frame.** Bytes outside `[at, at + len)` agree and no region overlaps it:
the map is as good (or bad) as before. -/
theorem descOk_frame (π : Policy) (base : UInt32) {m₁ m₂ : ByteArray} {at_ len : Nat}
    (ht : π.descTouch at_ len = false)
    (h : ∀ j, (j < at_ ∨ at_ + len ≤ j) → m₁.get! j = m₂.get! j) :
    descOk π base m₁ = descOk π base m₂ := by
  refine descOk_congr π base fun d hd j hj1 hj2 => h j ?_
  by_cases hl : len = 0
  · omega
  · have hd' : ¬(at_ < d.limit ∧ d.start.toNat < at_ + len) := by
      intro hc
      have : π.descTouch at_ len = true := by
        unfold Policy.descTouch
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, List.any_eq_true, decide_eq_true_eq]
        exact ⟨hl, d, hd, hc⟩
      simp [this] at ht
    omega

/-! ## The descriptor scan sees the stored scratch -/

theorem toNat_add_of_lt {a b : UInt32} (h : a.toNat + b.toNat < 2 ^ 32) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt32.toNat_add]; exact Nat.mod_eq_of_lt h

theorem byteOf_and (v : UInt32) (k : Nat) :
    (byteOf v k).toUInt32 = (v >>> (8 * UInt32.ofNat k)) &&& 0xFF := by
  simp only [byteOf, UInt32.toUInt32_toUInt8]
  generalize v >>> (8 * UInt32.ofNat k) = x
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_and, UInt32.toNat_mod]
  simp only [UInt32.reduceToNat]
  exact (Nat.and_two_pow_sub_one_eq_mod x.toNat 8).symm

/-- One scratch byte after the pending store of the low `ow` bytes of `ov` at `oa`. -/
theorem byteAfter_eq (p : Program) (d : Device σ) (m : Machine σ) (v : UInt64) (st code : UInt32)
    (j oa ow ov : UInt32) (ho : oa.toNat + ow.toNat ≤ m.mem.size) (hsz : m.mem.size < 2 ^ 32) :
    Exec.byteAfter ({ p, d, m, v, st, code } : St σ) j oa ow ov =
      { p, d, m, v := ((memStore m.mem oa.toNat ow.toNat ov).get! j.toNat).toUInt32.toUInt64, st, code } := by
  unfold Exec.byteAfter
  have hoa : (oa + ow).toNat = oa.toNat + ow.toNat := toNat_add_of_lt (by omega)
  rw [memStore_get]
  by_cases hin : oa ≤ j ∧ j < oa + ow
  · have h1 : oa.toNat ≤ j.toNat := UInt32.le_iff_toNat_le.mp hin.1
    have h2 : j.toNat < oa.toNat + ow.toNat := hoa ▸ UInt32.lt_iff_toNat_lt.mp hin.2
    have hc : (oa ≤ j && j < oa + ow) = true := by simp [hin.1, hin.2]
    have hsub : UInt32.ofNat (j.toNat - oa.toNat) = j - oa := by
      apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_ofNat', UInt32.toNat_sub_of_le _ _ hin.1]
      exact Nat.mod_eq_of_lt (by omega)
    have h3 : j.toNat < m.mem.size := by omega
    simp only [hc, h1, h2, h3, and_self, ↓reduceIte, byteOf_and, hsub]
    rfl
  · have hc : (oa ≤ j && j < oa + ow) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
      by_cases h : oa ≤ j
      · exact Or.inr (fun h' => hin ⟨h, h'⟩)
      · exact Or.inl h
    have hn : ¬(oa.toNat ≤ j.toNat ∧ j.toNat < oa.toNat + ow.toNat ∧ j.toNat < m.mem.size) := by
      intro ⟨h1, h2, _⟩
      exact hin ⟨UInt32.le_iff_toNat_le.mpr h1, UInt32.lt_iff_toNat_lt.mpr (hoa ▸ h2)⟩
    simp only [hc, Bool.false_eq_true, ↓reduceIte, hn]
    rw [hook_memLoad, show (1 : UInt32).toNat = 1 from rfl,
      memLoad_one]

/-- A word of scratch after the pending store (`Exec.wordAfter`). -/
theorem wordAfter_eq (p : Program) (d : Device σ) (m : Machine σ) (v : UInt64) (st code : UInt32)
    (a oa ow ov : UInt32) (ha : a.toNat + 4 < 2 ^ 32)
    (ho : oa.toNat + ow.toNat ≤ m.mem.size) (hsz : m.mem.size < 2 ^ 32) :
    Exec.wordAfter ({ p, d, m, v, st, code } : St σ) a oa ow ov =
      { p, d, m, v := (le32 (memStore m.mem oa.toNat ow.toNat ov) a.toNat).toUInt64, st, code } := by
  unfold Exec.wordAfter
  have hoa : (oa + ow).toNat = oa.toNat + ow.toNat := toNat_add_of_lt (by omega)
  have ha4 : (a + 4).toNat = a.toNat + 4 := toNat_add_of_lt (by simpa using ha)
  split
  · rename_i hc
    rw [hook_memLoad, show (4 : UInt32).toNat = 4 from rfl]
    congr 2
    refine (le32_congr fun k hk => (memStore_get_out _ _ _ _ _ ?_).symm)
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
    rcases hc with (hc | hc) | hc
    · subst hc; simp only [UInt32.toNat_zero]; omega
    · have := UInt32.le_iff_toNat_le.mp hc; omega
    · have := UInt32.le_iff_toNat_le.mp hc; omega
  · have h1 : (a + 1).toNat = a.toNat + 1 := toNat_add_of_lt (by simp; omega)
    have h2 : (a + 2).toNat = a.toNat + 2 := toNat_add_of_lt (by simp; omega)
    have h3 : (a + 3).toNat = a.toNat + 3 := toNat_add_of_lt (by simp; omega)
    simp only [byteAfter_eq _ _ _ _ _ _ _ _ _ _ ho hsz, Exec.word, hook_withVal, hook_val,
      UInt32.toUInt32_toUInt64, h1, h2, h3, le32, memLoad_four]

/-- Entry `i` of descriptor `d` holds zero or a scratch pointer (`Sim.descOk`). -/
def entryOk (d : Descriptor) (base : UInt32) (mem : ByteArray) (i : Nat) : Bool :=
  (d.trb && !Descriptor.trbParamIsPtr (le32 mem (d.addr i + 12))) ||
    Bytecode.ptrOk base (le32 mem (d.addr i)) (le32 mem (d.addr i + 4))

theorem descOk_entries (π : Policy) (base : UInt32) (mem : ByteArray) :
    descOk π base mem = π.descriptors.all fun d => (List.range d.count.toNat).all (entryOk d base mem) :=
  rfl

theorem entry_addr (dsc : Descriptor) (hlim : dsc.limit ≤ scratchBytes) {i : UInt32}
    (hi : i.toNat < dsc.count.toNat) (k : Nat) (hk : k ≤ 12) :
    (dsc.start + dsc.stride * i + UInt32.ofNat k).toNat = dsc.addr i.toNat + k ∧
      dsc.addr i.toNat + k + 4 < 2 ^ 32 := by
  have hl := addr_le_limit dsc hi
  have hsz : dsc.size ≥ 8 := by simp only [Descriptor.size]; split <;> omega
  simp only [Descriptor.addr] at hl ⊢
  have hm : dsc.stride.toNat * i.toNat < 2 ^ 32 := by unfold scratchBytes at hlim; omega
  have hmul : (dsc.stride * i).toNat = dsc.stride.toNat * i.toNat := by
    rw [UInt32.toNat_mul]; exact Nat.mod_eq_of_lt hm
  have hk' : (UInt32.ofNat k).toNat = k := by
    rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  refine ⟨?_, by unfold scratchBytes at hlim; omega⟩
  rw [UInt32.toNat_add, UInt32.toNat_add, hmul, hk']
  unfold scratchBytes at hlim
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem scanEntries_eq (p : Program) (d : Device σ) (m : Machine σ) (st code : UInt32)
    (base oa ow ov : UInt32) (dsc : Descriptor) (hlim : dsc.limit ≤ scratchBytes)
    (ho : oa.toNat + ow.toNat ≤ m.mem.size) (hsz : m.mem.size < 2 ^ 32) :
    ∀ (n : Nat) (i : UInt32) (v : UInt64), dsc.count.toNat - i.toNat = n →
      Exec.scanEntries ({ p, d, m, v, st, code } : St σ) base oa ow ov dsc.trb dsc.start
          dsc.stride dsc.count i =
        { p, d, m, st, code,
          v := boolVal ((List.range' i.toNat n).all
            (entryOk dsc base (memStore m.mem oa.toNat ow.toNat ov))) } := by
  intro n
  induction n with
  | zero =>
    intro i v hn
    have hi : ¬ i < dsc.count := by rw [UInt32.lt_iff_toNat_lt]; omega
    rw [Exec.scanEntries]
    simp only [hi, ↓reduceDIte]
    rfl
  | succ n ih =>
    intro i v hn
    have hi : i < dsc.count := by rw [UInt32.lt_iff_toNat_lt]; omega
    have hi' : i.toNat < dsc.count.toNat := by omega
    have hs := toNat_succ hi
    rw [Exec.scanEntries, List.range'_succ, List.all_cons]
    simp only [hi, ↓reduceDIte]
    obtain ⟨h0, b0⟩ := entry_addr dsc hlim hi' 0 (by omega)
    obtain ⟨h4, b4⟩ := entry_addr dsc hlim hi' 4 (by omega)
    obtain ⟨h12, b12⟩ := entry_addr dsc hlim hi' 12 (by omega)
    simp only [UInt32.reduceOfNat, UInt32.add_zero, Nat.add_zero] at h0 h4 h12 b0
    have ih' := fun v => ih (i + 1) v (by omega)
    simp only [hs] at ih'
    have w0 := fun v => wordAfter_eq p d m v st code (dsc.start + dsc.stride * i) oa ow ov
      (by rw [h0]; omega) ho hsz
    have w4 := fun v => wordAfter_eq p d m v st code (dsc.start + dsc.stride * i + 4) oa ow ov
      (by rw [h4]; omega) ho hsz
    have w12 := fun v => wordAfter_eq p d m v st code (dsc.start + dsc.stride * i + 12) oa ow ov
      (by rw [h12]; omega) ho hsz
    cases htrb : dsc.trb
    · rw [htrb] at ih'
      have he : entryOk dsc base (memStore m.mem oa.toNat ow.toNat ov) i.toNat =
          Exec.ptrOk base (le32 (memStore m.mem oa.toNat ow.toNat ov) (dsc.addr i.toNat))
            (le32 (memStore m.mem oa.toNat ow.toNat ov) (dsc.addr i.toNat + 4)) := by
        simp [entryOk, htrb, ptrOk_eq]
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_and, w0, w4,
        Exec.word, hook_val, UInt32.toUInt32_toUInt64, h0, h4, he]
      split
      · rename_i hp; rw [ih', hp, Bool.true_and]
      · rename_i hp; simp only [Bool.not_eq_true] at hp; rw [hp, Bool.false_and]; rfl
    · rw [htrb] at ih'
      have he : entryOk dsc base (memStore m.mem oa.toNat ow.toNat ov) i.toNat =
          ((!Exec.trbPtr (le32 (memStore m.mem oa.toNat ow.toNat ov) (dsc.addr i.toNat + 12))) ||
          Exec.ptrOk base (le32 (memStore m.mem oa.toNat ow.toNat ov) (dsc.addr i.toNat))
            (le32 (memStore m.mem oa.toNat ow.toNat ov) (dsc.addr i.toNat + 4))) := by
        simp [entryOk, htrb, ptrOk_eq, trbPtr_eq]
      simp only [↓reduceIte, Bool.true_and, w0, w4, w12,
        Exec.word, hook_val, UInt32.toUInt32_toUInt64, h0, h4, h12, he]
      split
      · rename_i hq; rw [ih', hq, Bool.true_or, Bool.true_and]
      · rename_i hq
        simp only [Bool.not_eq_true] at hq
        rw [hq, Bool.false_or]
        split
        · rename_i hp; rw [ih', hp, Bool.true_and]
        · rename_i hp; simp only [Bool.not_eq_true] at hp; rw [hp, Bool.false_and]; rfl

theorem scanDescs_eq (p : Program) (d : Device σ) (m : Machine σ) (st code : UInt32)
    (base oa ow ov : UInt32) (hlim : ∀ dsc ∈ descs p, dsc.limit ≤ scratchBytes)
    (hlen : (descs p).length < 2 ^ 32)
    (ho : oa.toNat + ow.toNat ≤ m.mem.size) (hsz : m.mem.size < 2 ^ 32) :
    ∀ (n : Nat) (k : UInt32) (v : UInt64), (descs p).length - k.toNat = n →
      Exec.scanDescs ({ p, d, m, v, st, code } : St σ) base oa ow ov k (descs p).length.toUInt32 =
        { p, d, m, st, code,
          v := boolVal (((descs p).drop k.toNat).all fun dsc =>
            (List.range dsc.count.toNat).all (entryOk dsc base (memStore m.mem oa.toNat ow.toNat ov))) } := by
  intro n
  induction n with
  | zero =>
    intro k v hn
    have hk : ¬ k < (descs p).length.toUInt32 := by rw [lt_len hlen]; omega
    rw [Exec.scanDescs]
    simp only [hk, ↓reduceDIte]
    rw [List.drop_eq_nil_of_le (by omega)]
    rfl
  | succ n ih =>
    intro k v hn
    have hk : k < (descs p).length.toUInt32 := by rw [lt_len hlen]; omega
    have hk' : k.toNat < (descs p).length := by omega
    have hs := toNat_succ hk
    have ih' := fun v => ih (k + 1) v (by omega)
    simp only [hs] at ih'
    rw [Exec.scanDescs]
    simp only [hk, ↓reduceDIte, hook_polDescTrb, hook_polDescStart, hook_polDescStride,
      hook_polDescCount, getD_lt hk', flag_ne]
    rw [scanEntries_eq p d m st code base oa ow ov _ (hlim _ (List.getElem_mem hk')) ho hsz _ 0 v rfl]
    rw [List.drop_eq_getElem_cons hk', List.all_cons]
    simp only [UInt32.toNat_zero, Nat.sub_zero, ← List.range_eq_range', Exec.flag, hook_val,
      boolVal_ne]
    split
    · rename_i hq; rw [ih', hq, Bool.true_and]
    · rename_i hq; simp only [Bool.not_eq_true] at hq; rw [hq, Bool.false_and]

/-! ## Transfer loops -/

theorem idx_toNat {b i n : UInt32} (hb : b.toNat + 4 * n.toNat < 2 ^ 32) (hi : i.toNat < n.toNat) :
    (b + 4 * i).toNat = b.toNat + 4 * i.toNat := by
  have : (4 * i).toNat = 4 * i.toNat := by
    rw [UInt32.toNat_mul]; simp only [UInt32.reduceToNat]; exact Nat.mod_eq_of_lt (by omega)
  rw [UInt32.toNat_add, this]; exact Nat.mod_eq_of_lt (by omega)

theorem blobStream_eq (p : Program) (d : Device σ) (v : UInt64) (st code off b n : UInt32)
    (hb : b.toNat + 4 * n.toNat < 2 ^ 32) :
    ∀ (k : Nat) (i : UInt32) (m : Machine σ), n.toNat - i.toNat = k →
      Exec.blobStream ({ p, d, m, v, st, code } : St σ) off b i n =
        { p, d, v, st, code,
          m := { m with dev := (iter (fun j s => d.write32 s off (le32 p.blob (b.toNat + 4 * j)))
            i.toNat k m.dev) } } := by
  intro k
  induction k with
  | zero =>
    intro i m hk
    have hi : ¬ i < n := by rw [UInt32.lt_iff_toNat_lt]; omega
    rw [Exec.blobStream]
    simp only [hi, ↓reduceDIte]
    rfl
  | succ k ih =>
    intro i m hk
    have hi : i < n := by rw [UInt32.lt_iff_toNat_lt]; omega
    have hs := toNat_succ hi
    rw [Exec.blobStream]
    simp only [hi, ↓reduceDIte, hook_blobWord, hook_mmioWrite32,
      idx_toNat hb (UInt32.lt_iff_toNat_lt.mp hi)]
    rw [ih (i + 1) _ (by omega), hs]
    rfl

theorem fifoIn_eq (p : Program) (d : Device σ) (st code off base n : UInt32)
    (hb : base.toNat + 4 * n.toNat < 2 ^ 32) :
    ∀ (k : Nat) (i : UInt32) (m : Machine σ) (v : UInt64), n.toNat - i.toNat = k →
      ∃ v', Exec.fifoIn ({ p, d, m, v, st, code } : St σ) off base i n =
        { p, d, v := v', st, code,
          m := let r := iter (fun j (acc : ByteArray × σ) =>
              let (x, s') := d.read32 acc.2 off
              (memStore acc.1 (base.toNat + 4 * j) 4 x, s')) i.toNat k (m.mem, m.dev)
            { m with mem := r.1, dev := r.2 } } := by
  intro k
  induction k with
  | zero =>
    intro i m v hk
    have hi : ¬ i < n := by rw [UInt32.lt_iff_toNat_lt]; omega
    refine ⟨v, ?_⟩
    rw [Exec.fifoIn]
    simp only [hi, ↓reduceDIte]
    rfl
  | succ k ih =>
    intro i m v hk
    have hi : i < n := by rw [UInt32.lt_iff_toNat_lt]; omega
    have hs := toNat_succ hi
    rw [Exec.fifoIn]
    simp only [hi, ↓reduceDIte, hook_mmioRead32, hook_memStore, Exec.word, hook_val,
      UInt32.toUInt32_toUInt64, idx_toNat hb (UInt32.lt_iff_toNat_lt.mp hi),
      show (4 : UInt32).toNat = 4 from rfl]
    obtain ⟨v', h⟩ := ih (i + 1) _ _ (by omega)
    refine ⟨v', ?_⟩
    rw [h, hs]
    rfl

theorem fifoOut_eq (p : Program) (d : Device σ) (st code off base n : UInt32)
    (hb : base.toNat + 4 * n.toNat < 2 ^ 32) (mem : ByteArray) :
    ∀ (k : Nat) (i : UInt32) (m : Machine σ) (v : UInt64), m.mem = mem → n.toNat - i.toNat = k →
      ∃ v', Exec.fifoOut ({ p, d, m, v, st, code } : St σ) off base i n =
        { p, d, v := v', st, code,
          m := { m with dev := (iter (fun j s => d.write32 s off (memLoad mem (base.toNat + 4 * j) 4))
            i.toNat k m.dev) } } := by
  intro k
  induction k with
  | zero =>
    intro i m v _ hk
    have hi : ¬ i < n := by rw [UInt32.lt_iff_toNat_lt]; omega
    refine ⟨v, ?_⟩
    rw [Exec.fifoOut]
    simp only [hi, ↓reduceDIte]
    rfl
  | succ k ih =>
    intro i m v hm hk
    have hi : i < n := by rw [UInt32.lt_iff_toNat_lt]; omega
    have hs := toNat_succ hi
    rw [Exec.fifoOut]
    simp only [hi, ↓reduceDIte, hook_memLoad, hook_mmioWrite32, Exec.word, hook_val,
      UInt32.toUInt32_toUInt64, idx_toNat hb (UInt32.lt_iff_toNat_lt.mp hi),
      show (4 : UInt32).toNat = 4 from rfl]
    obtain ⟨v', h⟩ := ih (i + 1)
      { m with dev := d.write32 m.dev off (memLoad m.mem (base.toNat + 4 * i.toNat) 4) }
      (memLoad m.mem (base.toNat + 4 * i.toNat) 4).toUInt64 hm (by omega)
    refine ⟨v', ?_⟩
    rw [h, hs]
    subst hm
    rfl

theorem fifo_frame (d : Device σ) (off : UInt32) (base : Nat) :
    ∀ (k i : Nat) (acc : ByteArray × σ) (j : Nat), (j < base + 4 * i ∨ base + 4 * (i + k) ≤ j) →
      (iter (fun j (acc : ByteArray × σ) =>
          let (x, s') := d.read32 acc.2 off
          (memStore acc.1 (base + 4 * j) 4 x, s')) i k acc).1.get! j = acc.1.get! j
  | 0, _, _, _, _ => rfl
  | k + 1, i, acc, j, hj => by
    simp only [iter]
    rw [fifo_frame d off base k (i + 1) _ j (by omega)]
    exact memStore_get_out _ _ _ _ _ (by omega)

theorem fifo_size (d : Device σ) (off : UInt32) (base : Nat) :
    ∀ (k i : Nat) (acc : ByteArray × σ),
      (iter (fun j (acc : ByteArray × σ) =>
          let (x, s') := d.read32 acc.2 off
          (memStore acc.1 (base + 4 * j) 4 x, s')) i k acc).1.size = acc.1.size
  | 0, _, _ => rfl
  | k + 1, i, acc => by
    simp only [iter]
    rw [fifo_size d off base k (i + 1) _]
    exact memStore_size _ _ _ _

/-! ## What the image parser guarantees, and what every run keeps -/

/-- Programs the C image parser accepts: a blob, sink table and descriptor
map that fit its 32-bit fields, and descriptor regions inside scratch
(`Policy.descWf`). -/
def WF (p : Program) : Prop :=
  p.blob.size < 2 ^ 32 ∧ (sinks p).length < 2 ^ 32 ∧ (descs p).length < 2 ^ 32 ∧
    ∀ dsc ∈ descs p, dsc.limit ≤ scratchBytes

/-- Machines a run reaches: scratch of the executor's size, and (under a
declared policy) a descriptor map holding only scratch pointers
(`DeviceProgramConfinement.loop_descOk`). -/
def Inv (p : Program) (d : Device σ) (m : Machine σ) : Prop :=
  m.mem.size = scratchBytes ∧ ∀ π, p.policy = some π → descOk π (d.phys m.dev 0).1 m.mem = true

theorem sinks_some {p : Program} {π : Policy} (h : p.policy = some π) : sinks p = π.addrSinks := by
  simp [sinks, h]

theorem descs_some {p : Program} {π : Policy} (h : p.policy = some π) : descs p = π.descriptors := by
  simp [descs, h]

theorem sinkTouch_eq (s : St σ) {π : Policy} (hpol : s.p.policy = some π)
    (h : (sinks s.p).length < 2 ^ 32) (off : UInt32) :
    Exec.sinkTouchFrom s off 0 = π.sinkTouch off := by
  rw [sinkTouchFrom_eq s off h, sinks_some hpol]
  rfl

theorem sinkOk_eq (s : St σ) {π : Policy} (hpol : s.p.policy = some π)
    (h : (sinks s.p).length < 2 ^ 32) (base off v : UInt32) :
    Exec.sinkOk s base off v = π.sinkOk base off v := by
  unfold Exec.sinkOk Policy.sinkOk
  rw [sinkTouch_eq s hpol h, sinkIsFrom_eq s _ h, sinkIsFrom_eq s _ h, sinks_some hpol]
  simp only [UInt32.toNat_zero, List.drop_zero, List.contains_eq_any_beq]
  have hc (y : UInt32) : (fun x : UInt32 => x == y) = (fun x => y == x) := by
    funext x
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  rw [hc, hc]
  rfl

theorem descTouch_eq (s : St σ) {π : Policy} (hpol : s.p.policy = some π)
    (h : (descs s.p).length < 2 ^ 32) (at_ len : UInt64) (hl : at_.toNat + len.toNat < 2 ^ 64) :
    Exec.descTouch s at_ len = π.descTouch at_.toNat len.toNat := by
  unfold Exec.descTouch Policy.descTouch
  rw [descTouchFrom_eq s at_ len h, descs_some hpol]
  simp only [UInt32.toNat_zero, List.drop_zero]
  have hlen : (len != 0) = (len.toNat != 0) := by
    rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne]
    constructor
    · intro h0 h'; exact h0 (UInt64.toNat_inj.mp (by simpa using h'))
    · intro h0 h'; subst h'; exact h0 rfl
  rw [hlen]
  congr 1
  apply congrArg
  funext dsc
  have hadd : (at_ + len).toNat = at_.toNat + len.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt hl
  simp only [UInt64.lt_iff_toNat_lt, limit64_toNat, hadd, UInt32.toNat_toUInt64]

theorem blobStream_m (s : St σ) (off b n : UInt32) (hb : b.toNat + 4 * n.toNat < 2 ^ 32) :
    (Exec.blobStream s off b 0 n).m =
      { s.m with dev := (iter (fun j x => s.d.write32 x off (le32 s.p.blob (b.toNat + 4 * j)))
          0 n.toNat s.m.dev) } := by
  obtain ⟨p, d, m, v, st, code⟩ := s
  rw [blobStream_eq p d v st code off b n hb n.toNat 0 m (by simp)]
  rfl

theorem fifoIn_m (s : St σ) (off base n : UInt32) (hb : base.toNat + 4 * n.toNat < 2 ^ 32) :
    (Exec.fifoIn s off base 0 n).m =
      (let r := iter (fun j (acc : ByteArray × σ) =>
          let (x, s') := s.d.read32 acc.2 off
          (memStore acc.1 (base.toNat + 4 * j) 4 x, s')) 0 n.toNat (s.m.mem, s.m.dev)
       { s.m with mem := r.1, dev := r.2 }) := by
  obtain ⟨p, d, m, v, st, code⟩ := s
  obtain ⟨v', h⟩ := fifoIn_eq p d st code off base n hb n.toNat 0 m v (by simp)
  rw [h]
  rfl

theorem fifoOut_m (s : St σ) (off base n : UInt32) (hb : base.toNat + 4 * n.toNat < 2 ^ 32) :
    (Exec.fifoOut s off base 0 n).m =
      { s.m with dev := (iter (fun j x => s.d.write32 x off (memLoad s.m.mem (base.toNat + 4 * j) 4))
          0 n.toNat s.m.dev) } := by
  obtain ⟨p, d, m, v, st, code⟩ := s
  obtain ⟨v', h⟩ := fifoOut_eq p d st code off base n hb m.mem n.toNat 0 m v rfl (by simp)
  rw [h]
  rfl

/-! ## One instruction -/

/-- Normalize the generic step read over a machine. -/
macro "exec_norm" : tactic => `(tactic| simp only [Exec.next, Exec.word, Exec.flag, operand_eq,
    operandVal_eq, UInt32.toUInt32_toUInt64, Exec.regBad, Exec.srcBad, mmioOk_eq, cfgAllowed_eq,
    cfgOffOk_eq, apply_ite decode, hook_val, hook_withVal, hook_window, hook_blobLen,
    hook_blobWord, hook_polPresent, hook_polDma, hook_polCfgRead, hook_polCfgWrite,
    hook_polCmdClear, hook_polCmdSet, hook_pcOk, hook_fetch, hook_advance, hook_jump,
    hook_stackFull, hook_stackEmpty, hook_call, hook_ret, hook_regGet, hook_regSet, hook_memLoad,
    hook_memStore, hook_mmioRead32, hook_mmioRead16, hook_mmioRead8, hook_mmioWrite32,
    hook_mmioWrite16, hook_mmioWrite8, hook_cfgRead, hook_cfgWrite, hook_cfgUpdate, hook_phys,
    hook_physBase, hook_delay, hook_print, hook_polDescs, hook_polSinks, decode_next, decode_halt, decode_fail, decode_yield,
    decode_badPc, decode_badOffset, decode_badOpcode, decode_stack, decode_badBlob,
    decode_badMem, decode_policy, flag_ne, flag64_ne, boolVal_ne])

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 8000000 in
theorem exec_eq (s : St σ) (op a b c : UInt32) (hW : WF s.p) (hI : Inv s.p s.d s.m) :
    decode (Exec.exec s op a b c) = Sim.exec s.p s.d ⟨op, a, b, c⟩ s.m := by
  obtain ⟨hblob, hsinks, hdescs, hlim⟩ := hW
  obtain ⟨hsize, hdesc⟩ := hI
  rw [Exec.exec_tree]
  unfold Exec.execMatch Sim.exec
  dsimp only
  generalize op &&& 0xFF = k
  split
  all_goals (simp only [Exec.exec0, Exec.exec1, Exec.exec2, Exec.exec3, Exec.exec4, Exec.exec5, Exec.exec6, Exec.exec7, Exec.exec8, Exec.exec9, Exec.exec10, Exec.exec11, Exec.exec12, Exec.exec13, Exec.exec14, Exec.exec15, Exec.exec16, Exec.exec17, Exec.exec18, Exec.exec19, Exec.exec20, Exec.exec21, Exec.exec22, Exec.exec23, Exec.exec24, Exec.exec25, Exec.exec26, Exec.exec27, Exec.exec28, Exec.exec29,
    Exec.execBad, Exec.immOf])
  all_goals exec_norm
  all_goals (try rfl)
  all_goals (rcases hpol : s.p.policy with _ | π)
  all_goals (try (simp only [hpol, Option.isSome_none, Option.map_none, Option.getD_none,
    Bool.false_and, Bool.not_true, Bool.false_eq_true, ↓reduceIte]))
  all_goals (try rfl)
  all_goals (try (simp only [hpol, Option.isSome_some, Option.map_some, Option.getD_some,
    Bool.true_and, Bool.false_eq_true, ↓reduceIte, sinkOk_eq (π := π), sinkTouch_eq (π := π),
    Exec.updateOk, hook_polCmdClear, hook_polCmdSet, Policy.updateOk, hsinks]))
  all_goals (try rfl)
  -- ALU and branch: the sub-operation tables
  case h_13.none | h_13.some =>
    rw [aluOp_eq]
    by_cases hk : Exec.aluKnown (op >>> 16) = true <;>
      simp only [hk, ↓reduceIte, Bool.false_eq_true] <;> rfl
  case h_14.none | h_14.some =>
    rw [condOp_eq]
    by_cases hk : Exec.condKnown (op >>> 16) = true <;>
      simp only [hk, ↓reduceIte, Bool.false_eq_true, ite_next] <;> rfl
  -- call and return
  case h_20.none | h_20.some =>
    simp only [decide_eq_true_eq]
  case h_21.none | h_21.some =>
    rcases hst : s.m.stack with _ | ⟨r, rest⟩ <;>
      simp only [hst, List.isEmpty_nil, List.isEmpty_cons, ↓reduceIte, Bool.false_eq_true,
        decode_stack, decode_next] <;> rfl
  -- physAddr
  case h_26.some =>
    simp only [gt_iff_lt, UInt32.lt_iff_toNat_lt, scratch32_toNat, flag_beq]
    rfl
  -- blobLoad32: 64-bit offset arithmetic
  case h_19.none | h_19.some =>
    have hr := (s.m.reg b).toNat_lt
    have hc := c.toNat_lt
    have e1 : (c.toUInt64 + 4 * (s.m.reg b).toUInt64).toNat = c.toNat + 4 * (s.m.reg b).toNat := by
      simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt64.reduceToNat]
      omega
    have hL : s.p.blob.size.toUInt32.toUInt64.toNat = s.p.blob.size := by
      simp only [UInt32.toNat_toUInt64, Nat.toUInt32, UInt32.toNat_ofNat']
      exact Nat.mod_eq_of_lt hblob
    have hcond : (c.toUInt64 + 4 * (s.m.reg b).toUInt64 + 4 > s.p.blob.size.toUInt32.toUInt64) ↔
        (c.toNat + 4 * (s.m.reg b).toNat + 4 > s.p.blob.size) := by
      rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, UInt64.toNat_add, e1, hL]
      simp only [UInt64.reduceToNat]
      omega
    simp only [hcond]
    by_cases h : c.toNat + 4 * (s.m.reg b).toNat + 4 > s.p.blob.size
    · simp only [h, decide_true, Bool.or_true, ↓reduceIte]
    · have hidx : (c.toUInt64 + 4 * (s.m.reg b).toUInt64).toUInt32.toNat =
          c.toNat + 4 * (s.m.reg b).toNat := by
        rw [UInt64.toNat_toUInt32, e1]; omega
      simp only [hidx]
  -- memLoad
  case h_22.none | h_22.some =>
    have hr := (s.m.reg b).toNat_lt
    have hc := c.toNat_lt
    have hs := (op >>> 16).toNat_lt
    have e1 : ((s.m.reg b).toUInt64 + c.toUInt64).toNat = (s.m.reg b).toNat + c.toNat := by
      simp only [UInt64.toNat_add, UInt32.toNat_toUInt64]; omega
    have hcond : ((s.m.reg b).toUInt64 + c.toUInt64 + (op >>> 16).toUInt64 > scratch32.toUInt64) ↔
        ((s.m.reg b).toNat + c.toNat + (op >>> 16).toNat > scratchBytes) := by
      rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, UInt64.toNat_add, e1]
      simp only [UInt32.toNat_toUInt64, scratch32_toNat]
      unfold scratchBytes; omega
    simp only [hcond]
    by_cases h : (s.m.reg b).toNat + c.toNat + (op >>> 16).toNat > scratchBytes
    · simp only [h, decide_true, Bool.true_or, ↓reduceIte]
    · have hidx : ((s.m.reg b).toUInt64 + c.toUInt64).toUInt32.toNat = (s.m.reg b).toNat + c.toNat := by
        rw [UInt64.toNat_toUInt32, e1]; unfold scratchBytes at h; omega
      simp only [hidx]
  -- blobStream32
  case h_18.none | h_18.some =>
    have hL : s.p.blob.size.toUInt32.toNat = s.p.blob.size := by
      simp only [Nat.toUInt32, UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt hblob
    by_cases hb : b.toNat > s.p.blob.size
    · have h1 : b > s.p.blob.size.toUInt32 := by
        rw [gt_iff_lt, UInt32.lt_iff_toNat_lt, hL]; exact hb
      simp only [h1, hb, decide_true, Bool.true_or, ↓reduceIte]
    · have h1 : ¬ b > s.p.blob.size.toUInt32 := by
        rw [gt_iff_lt, UInt32.lt_iff_toNat_lt, hL]; exact hb
      have h2 : (c > (s.p.blob.size.toUInt32 - b) / 4) ↔ (c.toNat > (s.p.blob.size - b.toNat) / 4) := by
        rw [gt_iff_lt, UInt32.lt_iff_toNat_lt, UInt32.toNat_div,
          UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, hL]; omega), hL]
        rfl
      simp only [h1, h2, hb, decide_false, Bool.false_or]
      by_cases hc : c.toNat > (s.p.blob.size - b.toNat) / 4
      · simp only [hc, decide_true, Bool.true_or, Bool.or_true, ↓reduceIte]
      · rw [blobStream_m s a b c (by omega)]
  -- memStore: bounds, then the descriptor map
  case h_23.none =>
    have hr := (s.m.reg a).toNat_lt
    have hb := b.toNat_lt
    have hs := (op >>> 16).toNat_lt
    have e1 : ((s.m.reg a).toUInt64 + b.toUInt64).toNat = (s.m.reg a).toNat + b.toNat := by
      simp only [UInt64.toNat_add, UInt32.toNat_toUInt64]; omega
    have hcond : ((s.m.reg a).toUInt64 + b.toUInt64 + (op >>> 16).toUInt64 > scratch32.toUInt64) ↔
        ((s.m.reg a).toNat + b.toNat + (op >>> 16).toNat > scratchBytes) := by
      rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, UInt64.toNat_add, e1]
      simp only [UInt32.toNat_toUInt64, scratch32_toNat]
      unfold scratchBytes; omega
    simp only [hcond]
    by_cases h : (s.m.reg a).toNat + b.toNat + (op >>> 16).toNat > scratchBytes
    · simp only [h, decide_true, Bool.true_or, ↓reduceIte]
    have hidx : ((s.m.reg a).toUInt64 + b.toUInt64).toUInt32.toNat = (s.m.reg a).toNat + b.toNat := by
      rw [UInt64.toNat_toUInt32, e1]; unfold scratchBytes at h; omega
    simp only [hidx]
  case h_23.some =>
    have hr := (s.m.reg a).toNat_lt
    have hb := b.toNat_lt
    have hs := (op >>> 16).toNat_lt
    have e1 : ((s.m.reg a).toUInt64 + b.toUInt64).toNat = (s.m.reg a).toNat + b.toNat := by
      simp only [UInt64.toNat_add, UInt32.toNat_toUInt64]; omega
    have hcond : ((s.m.reg a).toUInt64 + b.toUInt64 + (op >>> 16).toUInt64 > scratch32.toUInt64) ↔
        ((s.m.reg a).toNat + b.toNat + (op >>> 16).toNat > scratchBytes) := by
      rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, UInt64.toNat_add, e1]
      simp only [UInt32.toNat_toUInt64, scratch32_toNat]
      unfold scratchBytes; omega
    simp only [hcond]
    by_cases h : (s.m.reg a).toNat + b.toNat + (op >>> 16).toNat > scratchBytes
    · simp only [h, decide_true, Bool.true_or, ↓reduceIte]
    have hidx : ((s.m.reg a).toUInt64 + b.toUInt64).toUInt32.toNat = (s.m.reg a).toNat + b.toNat := by
      rw [UInt64.toNat_toUInt32, e1]; unfold scratchBytes at h; omega
    simp only [hidx]
    have hl : ((s.m.reg a).toUInt64 + b.toUInt64).toNat + (op >>> 16).toUInt64.toNat < 2 ^ 64 := by
      rw [e1]; simp only [UInt32.toNat_toUInt64]; omega
    rw [descTouch_eq (s := { s with v := if (op &&& 256 != 0) = true then (s.m.reg a).toUInt64
      else (s.m.reg c).toUInt64 }) hpol hdescs _ _ hl, e1, UInt32.toNat_toUInt64]
    have hsz : s.m.mem.size < 2 ^ 32 := by rw [hsize]; unfold scratchBytes; omega
    have ho : ((s.m.reg a).toUInt64 + b.toUInt64).toUInt32.toNat + (op >>> 16).toNat ≤ s.m.mem.size := by
      rw [hidx, hsize]; omega
    rw [scanDescs_eq s.p s.d s.m s.st s.code _ _ _ _ hlim hdescs ho hsz _ 0 _ rfl]
    simp only [hidx, UInt32.toNat_zero, List.drop_zero, boolVal_ne, descs_some hpol,
      ← descOk_entries]
    by_cases ht : π.descTouch ((s.m.reg a).toNat + b.toNat) (op >>> 16).toNat = true
    · simp only [ht, ↓reduceIte]
      by_cases hX : descOk π (s.d.phys s.m.dev 0).fst (memStore s.m.mem ((s.m.reg a).toNat + b.toNat)
        (op >>> 16).toNat (if (op &&& 256 != 0) = true then c else s.m.reg c)) = true
      · simp only [hX, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      · simp only [Bool.not_eq_true] at hX
        simp only [hX, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
    · have hframe : descOk π (s.d.phys s.m.dev 0).fst (memStore s.m.mem ((s.m.reg a).toNat + b.toNat)
          (op >>> 16).toNat (if (op &&& 256 != 0) = true then c else s.m.reg c)) = true := by
        rw [descOk_frame π _ (Bool.eq_false_iff.mpr ht) (fun j hj => memStore_get_out _ _ _ _ _ hj)]
        exact hdesc π hpol
      simp only [ht, hframe, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
  -- fifoIn: bounds, the descriptor map, and the frame of the transfer
  case h_24.none =>
    have hr := (s.m.reg b).toNat_lt
    have hc := (s.m.reg c).toNat_lt
    have e4 : (4 * (s.m.reg c).toUInt64).toNat = 4 * (s.m.reg c).toNat := by
      simp only [UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt64.reduceToNat]; omega
    have e1 : ((s.m.reg b).toUInt64 + 4 * (s.m.reg c).toUInt64).toNat =
        (s.m.reg b).toNat + 4 * (s.m.reg c).toNat := by
      rw [UInt64.toNat_add, e4, UInt32.toNat_toUInt64]; omega
    have hcond : ((s.m.reg b).toUInt64 + 4 * (s.m.reg c).toUInt64 > scratch32.toUInt64) ↔
        ((s.m.reg b).toNat + 4 * (s.m.reg c).toNat > scratchBytes) := by
      rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, e1]
      simp only [UInt32.toNat_toUInt64, scratch32_toNat]
    simp only [hcond]
    by_cases h : (s.m.reg b).toNat + 4 * (s.m.reg c).toNat > scratchBytes
    · simp only [h, ↓reduceIte]
    have hb4 : (s.m.reg b).toNat + 4 * (s.m.reg c).toNat < 2 ^ 32 := by unfold scratchBytes at h; omega
    rw [fifoIn_m _ a (s.m.reg b) (s.m.reg c) hb4]
  case h_24.some =>
    have hr := (s.m.reg b).toNat_lt
    have hc := (s.m.reg c).toNat_lt
    have e4 : (4 * (s.m.reg c).toUInt64).toNat = 4 * (s.m.reg c).toNat := by
      simp only [UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt64.reduceToNat]; omega
    have e1 : ((s.m.reg b).toUInt64 + 4 * (s.m.reg c).toUInt64).toNat =
        (s.m.reg b).toNat + 4 * (s.m.reg c).toNat := by
      rw [UInt64.toNat_add, e4, UInt32.toNat_toUInt64]; omega
    have hcond : ((s.m.reg b).toUInt64 + 4 * (s.m.reg c).toUInt64 > scratch32.toUInt64) ↔
        ((s.m.reg b).toNat + 4 * (s.m.reg c).toNat > scratchBytes) := by
      rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, e1]
      simp only [UInt32.toNat_toUInt64, scratch32_toNat]
    simp only [hcond]
    by_cases h : (s.m.reg b).toNat + 4 * (s.m.reg c).toNat > scratchBytes
    · simp only [h, ↓reduceIte]
    have hb4 : (s.m.reg b).toNat + 4 * (s.m.reg c).toNat < 2 ^ 32 := by unfold scratchBytes at h; omega
    have hl : (s.m.reg b).toUInt64.toNat + (4 * (s.m.reg c).toUInt64).toNat < 2 ^ 64 := by
      rw [e4, UInt32.toNat_toUInt64]; omega
    rw [descTouch_eq (s := { s with v := (s.m.reg c).toUInt64 }) hpol hdescs _ _ hl, e4,
      UInt32.toNat_toUInt64]
    by_cases ht : π.descTouch (s.m.reg b).toNat (4 * (s.m.reg c).toNat) = true
    · simp only [h, ht, ↓reduceIte]
    · rw [fifoIn_m _ a (s.m.reg b) (s.m.reg c) hb4]
      have hframe : descOk π (s.d.phys s.m.dev 0).fst (iter (fun j (acc : ByteArray × σ) =>
          let (x, s') := s.d.read32 acc.2 a
          (memStore acc.1 ((s.m.reg b).toNat + 4 * j) 4 x, s')) 0 (s.m.reg c).toNat
          (s.m.mem, s.m.dev)).1 = true := by
        rw [descOk_frame π _ (Bool.eq_false_iff.mpr ht)
          (fun j hj => fifo_frame s.d a _ _ 0 _ j (by omega))]
        exact hdesc π hpol
      simp only [h, ht, Bool.false_eq_true, ↓reduceIte]
      simp only [hframe, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  -- fifoOut: bounds and the transfer
  case h_25.none | h_25.some =>
    have hr := (s.m.reg b).toNat_lt
    have hc := (s.m.reg c).toNat_lt
    have e4 : (4 * (s.m.reg c).toUInt64).toNat = 4 * (s.m.reg c).toNat := by
      simp only [UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt64.reduceToNat]; omega
    have e1 : ((s.m.reg b).toUInt64 + 4 * (s.m.reg c).toUInt64).toNat =
        (s.m.reg b).toNat + 4 * (s.m.reg c).toNat := by
      rw [UInt64.toNat_add, e4, UInt32.toNat_toUInt64]; omega
    have hcond : ((s.m.reg b).toUInt64 + 4 * (s.m.reg c).toUInt64 > scratch32.toUInt64) ↔
        ((s.m.reg b).toNat + 4 * (s.m.reg c).toNat > scratchBytes) := by
      rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, e1]
      simp only [UInt32.toNat_toUInt64, scratch32_toNat]
    simp only [hcond]
    by_cases h : (s.m.reg b).toNat + 4 * (s.m.reg c).toNat > scratchBytes
    · simp only [h, ↓reduceIte]
    have hb4 : (s.m.reg b).toNat + 4 * (s.m.reg c).toNat < 2 ^ 32 := by unfold scratchBytes at h; omega
    rw [fifoOut_m _ a (s.m.reg b) (s.m.reg c) hb4]

/-! ## The step, the loop and the run -/

/-- The hooked state a step starts from. -/
def St.ofMachine (p : Program) (d : Device σ) (m : Machine σ) : St σ := { p, d, m }

@[simp] theorem field_0 (w : Word4) : field w 0 = w.op := by simp [field]
@[simp] theorem field_1 (w : Word4) : field w 1 = w.a := by simp [field]
@[simp] theorem field_2 (w : Word4) : field w 2 = w.b := by simp [field]
@[simp] theorem field_3 (w : Word4) : field w 3 = w.c := by simp [field]

/-- **The generated step is the simulator step** on every machine a run
reaches, for every program the image parser accepts. -/
theorem step_eq (p : Program) (d : Device σ) (m : Machine σ) (hW : WF p) (hI : Inv p d m) :
    decode (Exec.step (St.ofMachine p d m)) = Sim.step p d m := by
  unfold Exec.step Sim.step St.ofMachine
  simp only [hook_pcOk, Exec.flag, hook_val, boolVal_ne]
  by_cases hpc : m.pc < p.words.size
  · have hw : p.words.getD m.pc default = p.words[m.pc] := by
      simp [Array.getD, hpc]
    simp only [hpc, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte,
      hook_fetch, hook_advance, Exec.word, hw]
    rw [exec_eq _ _ _ _ _ hW ⟨hI.1, hI.2⟩]
    simp only [hook_val, UInt32.toUInt32_toUInt64, field_0, field_1, field_2, field_3]
  · simp only [hpc, decide_false, Bool.not_false, ↓reduceIte, ↓reduceDIte, decode_badPc]

/-- Every step keeps the size of scratch. -/
theorem step_mem_size (p : Program) (d : Device σ) (m : Machine σ) :
    (Sim.step p d m).machine.mem.size = m.mem.size := by
  unfold Sim.step
  split
  · unfold exec
    dsimp only
    generalize (p.words[m.pc]).op &&& 0xFF = k
    split
    all_goals (try simp only [Machine.setReg])
    all_goals (repeat' split)
    all_goals (try simp only [Sim.Step.machine, memStore_size])
    all_goals (try rfl)
    all_goals (try (rw [fifo_size]))
  · rfl

/-- Runs keep `Inv` when the bus address of scratch is fixed. -/
theorem step_inv (p : Program) (d : Device σ) (m : Machine σ) (base : UInt32)
    (hphys : ∀ s, (d.phys s 0).1 = base) (hI : Inv p d m) :
    Inv p d (Sim.step p d m).machine := by
  refine ⟨by rw [step_mem_size, hI.1], fun π hpol => ?_⟩
  rw [hphys]
  have h0 := hI.2 π hpol
  rw [hphys] at h0
  unfold Sim.step
  split
  · exact DeviceProgramConfinement.exec_descOk π d p hpol base hphys _ _ h0
  · exact h0

/-- The generated executor's loop (`wifi_gen_resume`): the generated step
until it stops, at most `fuel` times. -/
def loop (p : Program) (d : Device σ) : Nat → Machine σ → Status × Machine σ
  | 0, m => (.stepLimit, m)
  | fuel + 1, m =>
    match decode (Exec.step (St.ofMachine p d m)) with
    | .next m' => loop p d fuel m'
    | .stop s m' => (s, m')

/-- The generated run: a fresh machine (zeroed registers and scratch). -/
def run (p : Program) (d : Device σ) (s0 : σ) (maxSteps : Nat) : Status × Machine σ :=
  loop p d maxSteps { dev := s0 }

theorem loop_eq (p : Program) (d : Device σ) (base : UInt32) (hphys : ∀ s, (d.phys s 0).1 = base)
    (hW : WF p) : ∀ (fuel : Nat) (m : Machine σ), Inv p d m → loop p d fuel m = Sim.loop p d fuel m
  | 0, _, _ => rfl
  | fuel + 1, m, hI => by
    have hs := step_inv p d m base hphys hI
    simp only [loop, Sim.loop, step_eq p d m hW hI]
    rcases hst : Sim.step p d m with m' | ⟨st', m'⟩
    · rw [hst] at hs
      exact loop_eq p d base hphys hW fuel m' hs
    · rfl

theorem inv_fresh (p : Program) (d : Device σ) (s0 : σ) : Inv p d ({ dev := s0 } : Machine σ) := by
  refine ⟨by simp [scratchBytes, ByteArray.size], fun π _ => DeviceProgramConfinement.descOk_zero π _⟩

/-- **The generated run is the simulator run.** -/
theorem run_eq (p : Program) (d : Device σ) (base : UInt32) (hphys : ∀ s, (d.phys s 0).1 = base)
    (hW : WF p) (s0 : σ) (fuel : Nat) : run p d s0 fuel = Sim.run p d s0 fuel :=
  loop_eq p d base hphys hW fuel _ (inv_fresh p d s0)

/-- **Static confinement of the generated executor.** An admissible program,
run by the generated step on any device model whose bus address of scratch is
fixed, never requests a device effect outside its policy
(`DeviceProgramConfinement.run_confined` for the code that runs). -/
theorem run_confined_generated (π : Policy) (p : Program)
    (hp : DeviceProgramConfinement.admissible p π = true) (hW : WF p)
    (d : Device σ) (base : UInt32) (hphys : ∀ s, (d.phys s 0).1 = base) (s0 : σ) (fuel : Nat) :
    (run p (DeviceProgramConfinement.guard π d) (s0, false) fuel).2.dev.2 = false := by
  rw [run_eq p _ base (fun s => hphys s.1) hW]
  exact DeviceProgramConfinement.run_confined π p hp d s0 fuel id (fun _ => rfl)

/-- **Dynamic confinement of the generated executor**: any program whose
image declares `π` is confined to it by the generated step's own checks. -/
theorem run_declared_confined_generated (π : Policy) (p : Program) (hpol : p.policy = some π)
    (hwin : p.effTarget.windowBytes.toNat ≤ π.window.toNat) (hW : WF p)
    (d : Device σ) (base : UInt32) (hphys : ∀ s, (d.phys s 0).1 = base) (s0 : σ) (fuel : Nat) :
    (run p (DeviceProgramConfinement.guard π d) (s0, false) fuel).2.dev.2 = false := by
  rw [run_eq p _ base (fun s => hphys s.1) hW]
  exact DeviceProgramConfinement.run_declared_confined π p hpol hwin d s0 fuel id (fun _ => rfl)

/-- **Descriptor pointers under the generated executor** (#495). -/
theorem run_declared_descriptors_generated (π : Policy) (p : Program) (hpol : p.policy = some π)
    (hW : WF p) (d : Device σ) (base : UInt32) (hphys : ∀ s, (d.phys s 0).1 = base) (s0 : σ)
    (fuel : Nat) : descOk π base (run p d s0 fuel).2.mem = true := by
  rw [run_eq p d base hphys hW]
  exact DeviceProgramConfinement.run_declared_descriptors π p hpol d base hphys s0 fuel

end LeanOS.Wifi.ExecRefinement
