import Lean
import LeanOS.Refinement.CSubset

/-!
# Symbolic evaluation of the C subset (issue #570)

A proof tool, not a trusted component: it is proved sound against the
`LeanOS.Refinement.CSubset` semantics.

`srun` runs a statement list of the subset on *symbolic* words — expressions
over the function's arguments (`SExpr`) — and returns every way the run can
end as a tree of branches (`STree`). It is a closed computation on the AST:
`csym_tree` computes a function's tree and the kernel re-checks it by
evaluation. A whole function's tree holds no statements, only the conditions
the C tests and the words it returns.

`srun_sound` proves that whatever the tree answers on concrete arguments, the
C semantics answers too, and `callWith_of_tree` lifts it to a call. A
refinement proof then compares the tree, a small `if`-tree over the
arguments, with the Lean definition. Soundness goes in one direction only:
the tree may get stuck where the C does not (a call nested inside an
operator, for example), which only makes a proof fail.
-/
namespace LeanOS.Refinement.CSymbolic

open LeanOS.Refinement.CSubset

/-- A symbolic word: an expression over the function's argument words. -/
inductive SExpr where
  | arg (index : Nat)
  | lit (value : UInt64)
  | bin (op : BinOp) (left right : SExpr)
  /-- Conversion to `uint8_t`. -/
  | u8 (value : SExpr)
  /-- A call: the callee's word for the argument words. -/
  | call (fn : String) (args : List SExpr)
  deriving Repr, Inhabited

mutual
/-- The word an expression denotes for the argument words `args`; a call the
environment does not answer denotes 0 (`ok` records whether it answers). -/
def SExpr.val (ext : Ext) (args : List UInt64) : SExpr → UInt64
  | .arg index => args.getD index 0
  | .lit value => value
  | .bin op left right => op.eval (left.val ext args) (right.val ext args)
  | .u8 value => truncate .u8 (value.val ext args)
  | .call fn callArgs => (ext fn (SExpr.vals ext args callArgs)).getD 0

def SExpr.vals (ext : Ext) (args : List UInt64) : List SExpr → List UInt64
  | [] => []
  | e :: es => e.val ext args :: SExpr.vals ext args es
end

/-- A call at the top of an expression answers; every other expression does. -/
def SExpr.ok (ext : Ext) (args : List UInt64) : SExpr → Bool
  | .call fn callArgs => (ext fn (SExpr.vals ext args callArgs)).isSome
  | _ => true

/-- The value a conversion to `ty` stores. -/
def wrap : Ty → SExpr → SExpr
  | .u8, e => .u8 e
  | .u64, e => e

/-- A symbolic environment: the declared types and a symbolic word per name. -/
structure SEnv where
  types : List (String × Ty)
  values : List (String × SExpr)

def SEnv.ty? (s : SEnv) (name : String) : Option Ty :=
  (s.types.find? (·.1 == name)).map (·.2)

def SEnv.get? (s : SEnv) (name : String) : Option SExpr :=
  (s.values.find? (·.1 == name)).map (·.2)

/-- The concrete environment a symbolic one denotes. -/
def SEnv.toEnv (ext : Ext) (args : List UInt64) (s : SEnv) : Env :=
  { types := s.types, values := s.values.map fun p => (p.1, p.2.val ext args) }

/-- Translate an expression; `top` allows a call (only at the top). -/
def sexpr (s : SEnv) (top : Bool) : Expr → Option SExpr
  | .var name => s.get? name
  | .lit value => some (.lit value)
  | .bin op left right =>
      match sexpr s false left, sexpr s false right with
      | some a, some b => some (.bin op a b)
      | _, _ => none
  | .call fn callArgs =>
      if top then (callArgs.mapM s.get?).map (.call fn) else none

/-- Every way a symbolic run can end. -/
inductive STree where
  | stuck
  | ret (value : SExpr)
  | normal (env : SEnv)
  | jump (label : String) (env : SEnv)
  /-- `if (c == 0) { zero } else { nonzero }`. -/
  | ite (c : SExpr) (zero nonzero : STree)
  /-- Stuck unless the call `e` answers. -/
  | check (e : SExpr) (k : STree)

/-- The concrete outcome a tree denotes for argument words `args`. -/
def STree.den (ext : Ext) (args : List UInt64) : STree → Option Signal
  | .stuck => none
  | .ret value => some (.returned (value.val ext args))
  | .normal env => some (.normal (env.toEnv ext args))
  | .jump label env => some (.jump label (env.toEnv ext args))
  | .ite c zero nonzero =>
      if c.val ext args = 0 then zero.den ext args else nonzero.den ext args
  | .check e k => if e.ok ext args then k.den ext args else none

/-- A `check` for an expression that may be stuck: a call. -/
def guardCall (e : SExpr) (k : STree) : STree :=
  match e with
  | .call .. => .check e k
  | _ => k

/-- Graft continuations onto the normal and jump ends of a tree. -/
def sseq (next : SEnv → STree) (jump : String → SEnv → STree) : STree → STree
  | .normal env => next env
  | .jump label env => jump label env
  | .ite c zero nonzero => .ite c (sseq next jump zero) (sseq next jump nonzero)
  | .check e k => .check e (sseq next jump k)
  | .stuck => .stuck
  | .ret value => .ret value

def sresolve (label : String) (s : SEnv) (stmts : List Stmt)
    (continue_ : SEnv → List Stmt → STree) : STree :=
  match findLabel label stmts with
  | some target => continue_ s target
  | none => .jump label s

/-- The symbolic run, statement for statement the `CSubset.run` it mirrors. -/
def srun : Nat → SEnv → List Stmt → List Stmt → STree
  | 0, _, _, _ => .stuck
  | _ + 1, s, _, [] => .normal s
  | fuel + 1, s, stmts, stmt :: rest =>
      match stmt with
      | .decl ty name => srun fuel { s with types := (name, ty) :: s.types } stmts rest
      | .assign name value =>
          match s.ty? name, sexpr s true value with
          | some ty, some e =>
              guardCall e (srun fuel { s with values := (name, wrap ty e) :: s.values } stmts rest)
          | _, _ => .stuck
      | .ifZero name thenBranch elseBranch =>
          match s.get? name with
          | none => .stuck
          | some c =>
              .ite c
                (sseq (srun fuel · stmts rest)
                  (fun label s' => sresolve label s' stmts (srun fuel · stmts ·))
                  (srun fuel s thenBranch thenBranch))
                (sseq (srun fuel · stmts rest)
                  (fun label s' => sresolve label s' stmts (srun fuel · stmts ·))
                  (srun fuel s elseBranch elseBranch))
      | .goto label => sresolve label s stmts (srun fuel · stmts ·)
      | .block _ body =>
          sseq (srun fuel · stmts rest)
            (fun label s' => sresolve label s' stmts (srun fuel · stmts ·))
            (srun fuel s body body)
      | .ret value =>
          match sexpr s true value with
          | some e => guardCall e (.ret e)
          | none => .stuck

/-- The symbolic parameters `index, index + 1, …`, converted to their types. -/
def sparams : List (String × Ty) → Nat → List (String × SExpr)
  | [], _ => []
  | (name, ty) :: rest, index => (name, wrap ty (.arg index)) :: sparams rest (index + 1)

/-- The tree of a function's body. -/
def treeOf (func : Func) : STree :=
  srun 256 { types := func.params, values := sparams func.params 0 } func.body func.body

/-! ## Soundness -/

section Soundness

variable (ext : Ext) (args : List UInt64)

theorem toEnv_get (s : SEnv) (name : String) :
    (s.toEnv ext args).get? name = (s.get? name).map (·.val ext args) := by
  simp only [SEnv.toEnv, Env.get?, SEnv.get?, List.find?_map, Option.map_map]
  rfl

theorem toEnv_ty (s : SEnv) (name : String) : (s.toEnv ext args).ty? name = s.ty? name := rfl

theorem val_wrap (ty : Ty) (e : SExpr) :
    (wrap ty e).val ext args = truncate ty (e.val ext args) := by
  cases ty <;> rfl

theorem guardCall_den (e : SExpr) (k : STree) :
    (guardCall e k).den ext args = if e.ok ext args then k.den ext args else none := by
  cases e <;> simp [guardCall, STree.den, SExpr.ok]

theorem mapM_get (s : SEnv) :
    ∀ (names : List String) (es : List SExpr), names.mapM s.get? = some es →
      names.mapM (s.toEnv ext args).get? = some (SExpr.vals ext args es)
  | [], es, h => by
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
      subst h; rfl
  | name :: names, es, h => by
      simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind] at h
      cases hn : s.get? name with
      | none => simp [hn] at h
      | some e =>
          cases hns : names.mapM s.get? with
          | none => simp [hn, hns] at h
          | some es' =>
              simp only [hn, hns, Option.bind_some, Option.some.injEq] at h
              subst h
              simp [List.mapM_cons, toEnv_get, hn, mapM_get s names es' hns, SExpr.vals]

theorem sexpr_sound_inner (s : SEnv) :
    ∀ (value : Expr) (e : SExpr), sexpr s false value = some e →
      evalExpr ext (s.toEnv ext args) value = some (e.val ext args)
  | .var name, e, h => by
      simp only [sexpr] at h
      simp [evalExpr, toEnv_get, h]
  | .lit value, e, h => by
      simp only [sexpr, Option.some.injEq] at h
      subst h; rfl
  | .bin op left right, e, h => by
      simp only [sexpr] at h
      cases ha : sexpr s false left with
      | none => simp [ha] at h
      | some a =>
          cases hb : sexpr s false right with
          | none => simp [ha, hb] at h
          | some b =>
              simp only [ha, hb, Option.some.injEq] at h
              subst h
              simp [evalExpr, sexpr_sound_inner s left a ha, sexpr_sound_inner s right b hb,
                SExpr.val]
  | .call fn callArgs, e, h => by
      simp [sexpr] at h

theorem sexpr_sound (s : SEnv) (top : Bool) (value : Expr) (e : SExpr)
    (h : sexpr s top value = some e) (hok : e.ok ext args = true) :
    evalExpr ext (s.toEnv ext args) value = some (e.val ext args) := by
  cases value with
  | call fn callArgs =>
      cases top with
      | false => simp [sexpr] at h
      | true =>
          simp only [sexpr, ite_true] at h
          cases hm : callArgs.mapM s.get? with
          | none => simp [hm] at h
          | some es =>
              simp only [hm, Option.map_some, Option.some.injEq] at h
              subst h
              simp only [SExpr.ok] at hok
              simp only [evalExpr, mapM_get ext args s callArgs es hm, Option.bind_eq_bind,
                Option.bind_some, SExpr.val]
              cases hx : ext fn (SExpr.vals ext args es) <;> simp_all
  | var name => exact sexpr_sound_inner ext args s _ e (by simpa [sexpr] using h)
  | lit value => exact sexpr_sound_inner ext args s _ e (by simpa [sexpr] using h)
  | bin op left right => exact sexpr_sound_inner ext args s _ e (by simpa [sexpr] using h)

/-- Grafting continuations: what the grafted tree answers, the nested run
followed by the concrete continuations answers. -/
theorem sseq_sound (next : SEnv → STree) (jump : String → SEnv → STree)
    (nextC : Env → Option Signal) (jumpC : String → Env → Option Signal)
    (hnext : ∀ s r, (next s).den ext args = some r → nextC (s.toEnv ext args) = some r)
    (hjump : ∀ label s r, (jump label s).den ext args = some r →
      jumpC label (s.toEnv ext args) = some r) :
    ∀ (t : STree) (r : Signal), (sseq next jump t).den ext args = some r →
      ∃ r', t.den ext args = some r' ∧ seq (some r') nextC jumpC = some r
  | .stuck, r, h => by simp [sseq, STree.den] at h
  | .ret value, r, h => ⟨_, rfl, by simpa [sseq, STree.den, seq] using h⟩
  | .normal env, r, h => ⟨_, rfl, by simpa [seq] using hnext env r h⟩
  | .jump label env, r, h => ⟨_, rfl, by simpa [seq] using hjump label env r h⟩
  | .ite c zero nonzero, r, h => by
      simp only [sseq, STree.den] at h ⊢
      split at h
      · simpa [*] using sseq_sound next jump nextC jumpC hnext hjump zero r h
      · simpa [*] using sseq_sound next jump nextC jumpC hnext hjump nonzero r h
  | .check e k, r, h => by
      simp only [sseq, STree.den] at h ⊢
      split at h
      · simpa [*] using sseq_sound next jump nextC jumpC hnext hjump k r h
      · simp at h

theorem sresolve_sound (label : String) (s : SEnv) (stmts : List Stmt)
    (k : SEnv → List Stmt → STree) (kC : Env → List Stmt → Option Signal)
    (hk : ∀ s target r, (k s target).den ext args = some r → kC (s.toEnv ext args) target = some r)
    (r : Signal) (h : (sresolve label s stmts k).den ext args = some r) :
    resolve label (s.toEnv ext args) stmts kC = some r := by
  simp only [sresolve, resolve] at h ⊢
  split at h
  · rename_i target htarget
    simp only [htarget]
    exact hk s target r h
  · rename_i htarget
    simp only [htarget]
    simpa [STree.den] using h

/-- **Soundness of the symbolic run.** -/
theorem srun_sound : ∀ (fuel : Nat) (s : SEnv) (stmts from_ : List Stmt) (r : Signal),
    (srun fuel s stmts from_).den ext args = some r →
      run ext fuel (s.toEnv ext args) stmts from_ = some r
  | 0, s, stmts, from_, r, h => by simp [srun, STree.den] at h
  | fuel + 1, s, stmts, [], r, h => by simpa [srun, STree.den, run] using h
  | fuel + 1, s, stmts, stmt :: rest, r, h => by
      have ih := srun_sound fuel
      have resolveK : ∀ label s' r, (sresolve label s' stmts (srun fuel · stmts ·)).den ext args =
          some r → resolve label (s'.toEnv ext args) stmts (run ext fuel · stmts ·) = some r :=
        fun label s' r h => sresolve_sound ext args label s' stmts _ _
          (fun s target r h => ih s stmts target r h) r h
      cases stmt with
      | decl ty name =>
          simp only [srun] at h
          exact ih _ stmts rest r h
      | assign name value =>
          simp only [srun] at h
          cases hty : s.ty? name with
          | none => simp [hty, STree.den] at h
          | some ty =>
              cases he : sexpr s true value with
              | none => simp [hty, he, STree.den] at h
              | some e =>
                  simp only [hty, he, guardCall_den] at h
                  split at h
                  · rename_i hok
                    have hv := sexpr_sound ext args s true value e he hok
                    have := ih _ stmts rest r h
                    simp only [run, toEnv_ty, hty, hv]
                    simpa [SEnv.toEnv, val_wrap] using this
                  · simp at h
      | ifZero name thenBranch elseBranch =>
          simp only [srun] at h
          cases hc : s.get? name with
          | none => simp [hc, STree.den] at h
          | some c =>
              simp only [hc, STree.den] at h
              simp only [run, toEnv_get, hc, Option.map_some]
              split at h
              · rename_i hz
                obtain ⟨r', hr', hseq⟩ := sseq_sound ext args _ _ (run ext fuel · stmts rest)
                  (fun label env' => resolve label env' stmts (run ext fuel · stmts ·))
                  (fun s' r h => ih s' stmts rest r h) resolveK _ r h
                simp [hz, ih s thenBranch thenBranch r' hr', hseq]
              · rename_i hz
                obtain ⟨r', hr', hseq⟩ := sseq_sound ext args _ _ (run ext fuel · stmts rest)
                  (fun label env' => resolve label env' stmts (run ext fuel · stmts ·))
                  (fun s' r h => ih s' stmts rest r h) resolveK _ r h
                simp [hz, ih s elseBranch elseBranch r' hr', hseq]
      | goto label =>
          simp only [srun] at h
          simp only [run]
          exact resolveK label s r h
      | block label body =>
          simp only [srun] at h
          obtain ⟨r', hr', hseq⟩ := sseq_sound ext args _ _ (run ext fuel · stmts rest)
            (fun label env' => resolve label env' stmts (run ext fuel · stmts ·))
            (fun s' r h => ih s' stmts rest r h) resolveK _ r h
          simp only [run, ih s body body r' hr']
          exact hseq
      | ret value =>
          simp only [srun] at h
          cases he : sexpr s true value with
          | none => simp [he, STree.den] at h
          | some e =>
              simp only [he, guardCall_den] at h
              split at h
              · rename_i hok
                simp only [STree.den, Option.some.injEq] at h
                subst h
                simp [run, sexpr_sound ext args s true value e he hok]
              · simp at h

theorem sparams_toEnv : ∀ (params : List (String × Ty)) (index : Nat),
    index + params.length = args.length →
      (sparams params index).map (fun p => (p.1, p.2.val ext args)) =
        (params.zip (args.drop index)).map fun (p, a) => (p.1, truncate p.2 a)
  | [], _, _ => by simp [sparams]
  | (name, ty) :: rest, index, hlen => by
      have hi : index < args.length := by simp at hlen; omega
      rw [List.drop_eq_getElem_cons hi]
      simp only [sparams, List.map_cons, List.zip_cons_cons, val_wrap, SExpr.val,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      rw [sparams_toEnv rest (index + 1) (by simp at hlen; omega)]

/-- **A call answers what its tree answers.** -/
theorem callWith_of_tree (func : Func) (hlen : func.params.length = args.length) (v : UInt64)
    (h : (treeOf func).den ext args = some (.returned v)) :
    callWith ext func args = some (truncate func.result v) := by
  have env : ({ types := func.params, values := sparams func.params 0 } : SEnv).toEnv ext args =
      { types := func.params
        values := (func.params.zip args).map fun (p, a) => (p.1, truncate p.2 a) } := by
    simp only [SEnv.toEnv]
    rw [sparams_toEnv ext args func.params 0 (by omega)]
    simp
  have run := srun_sound ext args 256 _ func.body func.body _ h
  rw [env] at run
  simp [callWith, hlen, run, finish]

end Soundness

/-! ## Reading a tree

`csym_norm` turns the denotation of a concrete tree, and the Lean definition
it is compared with, into `if`-trees over the same atomic conditions;
`csym_close` then splits on the first condition, rewrites with the case, and
recurses until both sides are the same word. A wrong tree or definition
leaves two different leaves and fails. -/

theorem flag_u8 (c : Prop) [Decidable c] :
    (if c then (1 : UInt64) else 0).toUInt8.toUInt64 = if c then 1 else 0 := by
  split <;> rfl

theorem flag_eq_zero (c : Prop) [Decidable c] :
    ((if c then (1 : UInt64) else 0) = 0) ↔ ¬ c := by
  split <;> simp_all

theorem ite_and' {α : Type} (p q : Prop) [Decidable p] [Decidable q] (a b : α) :
    (if p ∧ q then a else b) = if p then (if q then a else b) else b := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem ite_or' {α : Type} (p q : Prop) [Decidable p] [Decidable q] (a b : α) :
    (if p ∨ q then a else b) = if p then a else (if q then a else b) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-- Lean's `>>>` and `<<<` on `UInt64` already take the shift modulo 64, as
`lean.h` does explicitly. -/
theorem shr_mod (a b : UInt64) : a >>> (b % 64) = a >>> b := by
  apply UInt64.toBitVec_inj.mp
  simp [UInt64.toBitVec_shiftRight, UInt64.toBitVec_mod]

theorem shl_mod (a b : UInt64) : a <<< (b % 64) = a <<< b := by
  apply UInt64.toBitVec_inj.mp
  simp [UInt64.toBitVec_shiftLeft, UInt64.toBitVec_mod]

theorem ite_cond_ite {α : Type} (c p q : Prop) [Decidable c] [Decidable p] [Decidable q]
    [Decidable (if c then p else q)] (a b : α) :
    (if (if c then p else q) then a else b) =
      if c then (if p then a else b) else (if q then a else b) := by
  by_cases hc : c <;> simp [hc]

/-- A function with a `uint8_t` result answers the word of a Lean `Bool`. -/
theorem callWith_of_tree_bool (ext : Ext) (args : List UInt64) (func : Func)
    (hlen : func.params.length = args.length) (hres : func.result = .u8) (b : Bool)
    (h : (treeOf func).den ext args = some (.returned (if b = true then 1 else 0))) :
    callWith ext func args = some (boolWord b) := by
  rw [callWith_of_tree ext args func hlen _ h, hres]
  cases b <;> rfl

/-- Unfold a tree's denotation to an `if`-tree. -/
macro "csym_den" : tactic => `(tactic|
  simp +decide only [↓reduceIte, STree.den, SExpr.val, SExpr.vals, SExpr.ok, BinOp.eval, truncate,
    List.getD_cons_zero, List.getD_cons_succ, boolWord, flag_u8, flag_eq_zero, ite_not,
    beq_iff_eq, Option.getD_some, Option.isSome_some, shr_mod, shl_mod])

/-- Normalize a tree's denotation and a Lean definition to `if`-trees over
atomic conditions (in separate passes: together the lemmas loop). -/
macro "csym_norm" : tactic => `(tactic| (
  try csym_den
  try simp only [↓reduceIte, beq_iff_eq, bne_iff_ne, ne_eq, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_true_eq, gt_iff_lt, Bool.ite_eq_true_distrib, Bool.false_eq_true,
    Bool.true_eq_false]
  try simp only [Bool.eq_false_iff, ne_eq]
  try simp only [ite_cond_ite]
  try simp only [ite_and']
  try simp only [ite_or']
  try simp only [↓reduceIte, beq_iff_eq, bne_iff_ne, ne_eq, Bool.not_eq_true', decide_eq_true_eq,
    Bool.false_eq_true, Bool.true_eq_false, not_false_eq_true, not_true_eq_false]
  try simp only [Bool.eq_false_iff, ne_eq]
  try simp only [ite_not]))

open Lean Meta in
/-- The normal form of a closed tree, computed with the elaborator's `whnf`
(which caches closed terms): constructors of the tree's own types are reduced
throughout, leaf words and names are left as the AST wrote them (only
projections and matches around them are reduced), and argument indices become
literals. Nothing here is trusted: `csym_tree` uses the result as a
definitional change, which the kernel re-checks. -/
partial def normalTree (e : Lean.Expr) : MetaM Lean.Expr := do
  let reduced ← whnfD e
  let fn := reduced.getAppFn
  let .const name _ := fn | return reduced
  let some (.ctorInfo info) := (← getEnv).find? name | return reduced
  let args ← reduced.getAppArgs.mapIdxM fun index arg => do
    if index < info.numParams then return arg
    let type ← whnfR (← inferType arg)
    if type.isConstOf ``Nat then
      return mkNatLit (← evalNat arg |>.run).get!
    if type.isConstOf ``UInt64 || type.isConstOf ``String then
      whnfCore arg
    else
      normalTree arg
  return mkAppN fn args

open Lean Meta Elab Tactic in
/-- Replace `treeOf f` in the goal by the tree the kernel computes for it.
The replacement is a definitional change that the kernel re-checks when the
theorem is added. -/
elab "csym_tree" : tactic => liftMetaTactic1 fun goal => goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let some app := target.find? (fun e => e.isAppOfArity ``treeOf 1)
    | throwError "csym_tree: no `treeOf` in the goal"
  let tree ← normalTree app
  goal.replaceTargetDefEq (target.replace fun e => if e == app then some tree else none)

open Lean Meta Elab Tactic in
/-- Case on the condition of the first `if` in the goal. -/
elab "csym_case" : tactic => withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let some ite := target.find? (fun e => e.isAppOfArity ``ite 5 && !e.hasLooseBVars)
    | throwError "csym_case: no `if` in the goal"
  let cond ← Term.exprToSyntax (ite.getArg! 1)
  evalTactic (← `(tactic| by_cases h : $cond))

/-- Close an equation between two `if`-trees over the same conditions: case
on the first condition, rewrite every occurrence with the case, and recurse.
A case on a `Bool` atom `b = true` may rewrite `b` itself to `false`, so
`false = true` is reduced too. Two different leaves under one set of cases
fail. -/
syntax "csym_close" : tactic
macro_rules
  | `(tactic| csym_close) => `(tactic|
      first
        | rfl
        | (csym_case <;> simp only [*, ↓reduceIte, Bool.false_eq_true] <;> csym_close))

/-- Like `csym_close`, but leaves each pair of unequal leaves as a goal (for
diagnosing a proof that fails). -/
syntax "csym_debug" : tactic
macro_rules
  | `(tactic| csym_debug) => `(tactic|
      first
        | rfl
        | (csym_case <;> simp only [*, ↓reduceIte, Bool.false_eq_true] <;> csym_debug)
        | skip)

/-- Prove `callWith ext f args = some w` from `f`'s tree: compute the tree,
normalize both sides and compare them case by case. Callees in the tree are
resolved by the extra simp lemmas, applied after the tree is unfolded. -/
syntax "csym_refine" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| csym_refine) => `(tactic| (csym_tree; csym_norm; all_goals csym_close))
  | `(tactic| csym_refine [$lemmas,*]) => `(tactic|
      (csym_tree; csym_den; (try simp +decide only [↓reduceIte, $lemmas,*]); csym_norm;
        all_goals csym_close))

end LeanOS.Refinement.CSymbolic
