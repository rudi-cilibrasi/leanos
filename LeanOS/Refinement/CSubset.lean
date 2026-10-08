/-!
# A C subset for generated scalar exports (issue #470, ADR 0023)

A deep embedding of exactly the C constructs the pinned Lean toolchain emits for
a scalar `uint64_t` export with no allocation. It is checked in as an AST and
compared byte-for-byte against `scripts/extract-generated-c.py`'s extraction of
the generated `.c` file, so the build fails when the emitted C drifts.

The subset:

* parameters and locals declared as `uint64_t` or `uint8_t`; an assignment
  truncates to the declared width, as C conversion to an unsigned type does;
* literals `NULL`-free unsigned constants (`0ULL`, `1ULL`);
* the inline `lean.h` helper `lean_uint64_dec_eq(a, b)`, whose definition is
  `return a1 == a2;` (C equality yields 0 or 1);
* `if (x == 0) { … } else { … }` on a local;
* labelled blocks (`label: { … }`) reached by `goto label;`;
* `return e;`.

Anything else is rejected by the extractor, so a proof about this AST says
nothing about C outside the subset. The meaning of each construct is the
reviewed reading of C11 written here; it is a TCB row (`docs/tcb.md`), not a
mechanized C standard. The calling convention that delivers the two
`uint64_t` arguments and returns the result stays a named assumption.
-/
namespace LeanOS.Refinement.CSubset

inductive Ty where
  | u8
  | u64
  deriving Repr, DecidableEq

inductive Expr where
  | var (name : String)
  | lit (value : UInt64)
  /-- `lean_uint64_dec_eq(a, b)`: 1 when equal, else 0. -/
  | decEq (left right : Expr)
  deriving Repr, DecidableEq

inductive Stmt where
  /-- `ty name;` a block-scoped local declaration. -/
  | decl (ty : Ty) (name : String)
  /-- `name = value;` converted to the declared width. -/
  | assign (name : String) (value : Expr)
  /-- `if (name == 0) { thenBranch } else { elseBranch }`. -/
  | ifZero (name : String) (thenBranch elseBranch : List Stmt)
  /-- `goto label;` -/
  | goto (label : String)
  /-- `label: { body }` — a join point; falling into it runs the body. -/
  | block (label : String) (body : List Stmt)
  /-- `return value;` -/
  | ret (value : Expr)
  deriving Repr

/-- A function: its `uint64_t` parameters and its body after `_start:`. -/
structure Func where
  params : List String
  body : List Stmt
  deriving Repr

structure Env where
  types : List (String × Ty) := []
  values : List (String × UInt64) := []

def Env.ty? (env : Env) (name : String) : Option Ty :=
  (env.types.find? (·.1 == name)).map (·.2)

def Env.get? (env : Env) (name : String) : Option UInt64 :=
  (env.values.find? (·.1 == name)).map (·.2)

def truncate : Ty → UInt64 → UInt64
  | .u8, value => value.toUInt8.toUInt64
  | .u64, value => value

def evalExpr (env : Env) : Expr → Option UInt64
  | .var name => env.get? name
  | .lit value => some value
  | .decEq left right => do
      let a ← evalExpr env left
      let b ← evalExpr env right
      pure (if a == b then 1 else 0)

/-- How a statement list ended. -/
inductive Signal where
  | normal (env : Env)
  | jump (label : String) (env : Env)
  | returned (value : UInt64)

/-- Run a statement list; `none` is stuck (unbound name, bad label, no fuel). -/
def execList (fuel : Nat) (env : Env) : List Stmt → Option Signal
  | [] => some (.normal env)
  | stmt :: rest =>
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match stmt with
      | .decl ty name =>
          execList fuel { env with types := (name, ty) :: env.types } rest
      | .assign name value => do
          let ty ← env.ty? name
          let v ← evalExpr env value
          execList fuel { env with values := (name, truncate ty v) :: env.values } rest
      | .ifZero name thenBranch elseBranch => do
          let v ← env.get? name
          match ← execList fuel env (if v == 0 then thenBranch else elseBranch) with
          | .normal env' => execList fuel env' rest
          | other => pure other
      | .goto label => some (.jump label env)
      | .block _ body => do
          match ← execList fuel env body with
          | .normal env' => execList fuel env' rest
          | other => pure other
      | .ret value => do
          let v ← evalExpr env value
          some (.returned v)

/-- The labelled block `label` among the top-level statements, with the
statements after it (C `goto` continues from the label). -/
def findLabel (label : String) : List Stmt → Option (List Stmt)
  | [] => none
  | .block l body :: rest => if l == label then some (.block l body :: rest) else findLabel label rest
  | _ :: rest => findLabel label rest

/-- Run a top-level body, following `goto`s to top-level labels (at most
`jumps` of them). -/
def runBody (fuel jumps : Nat) (body : List Stmt) (env : Env) (from_ : List Stmt) :
    Option UInt64 :=
  match execList fuel env from_ with
  | some (.returned v) => some v
  | some (.jump label env') =>
      match jumps with
      | 0 => none
      | jumps + 1 => do
          let target ← findLabel label body
          runBody fuel jumps body env' target
  | _ => none

/-- Call `func` on `uint64_t` arguments. -/
def call (func : Func) (args : List UInt64) : Option UInt64 :=
  if func.params.length != args.length then none
  else
    let env : Env :=
      { types := func.params.map (·, Ty.u64), values := func.params.zip args }
    runBody 64 8 func.body env func.body

end LeanOS.Refinement.CSubset
