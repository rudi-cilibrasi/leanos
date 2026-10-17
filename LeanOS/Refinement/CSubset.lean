/-!
# A C subset for generated scalar exports (issues #470, #570; ADR 0023, ADR 0029)

A deep embedding of exactly the C constructs the pinned Lean toolchain emits for
a scalar export with no allocation. Each proved function is checked in as an
AST and compared byte-for-byte against `scripts/extract-generated-c.py`'s
extraction of the generated `.c` file, so the build fails when the emitted C
drifts.

The subset:

* parameters, results and locals declared as `uint64_t` or `uint8_t`; an
  assignment, a parameter binding and a `return` convert to the declared
  width, as C conversion to an unsigned type does;
* unsigned literals (`0ULL`, `1ULL`, and the `uint8_t` literals `0`, `1`);
* these inline `lean.h` helpers, each given its `lean.h` body:
  `lean_uint64_dec_eq(a, b)` is `a == b`, `lean_uint64_dec_lt` is `a < b`,
  `lean_uint64_dec_le` is `a <= b` (C comparisons yield 0 or 1);
  `lean_uint64_add`, `lean_uint64_sub` are `a + b`, `a - b` modulo 2^64;
  `lean_uint64_land`, `lean_uint64_lor`, `lean_uint64_xor` are `&`, `|`, `^`;
  `lean_uint64_shift_left`, `lean_uint64_shift_right` are `a << (b % 64)`,
  `a >> (b % 64)`; `lean_uint64_mod` is `b == 0 ? a : a % b`;
* a call `f(x, y, …)` of another function on variables, given meaning by an
  explicit environment `Ext` (see `callWith`): either another extracted and
  proved function, or a callee whose C behavior is a stated hypothesis;
* `if (x == 0) { … } else { … }` on a local;
* labelled blocks (`label: { … }`) reached by `goto label;` from inside the
  block list that contains the label, or from a block nested in it;
* `return e;`.

Anything else is rejected by the extractor, so a proof about this AST says
nothing about C outside the subset. The meaning of each construct is the
reviewed reading of C11 written here; it is a trusted row of ADR 0023 and
ADR 0029, not a mechanized C standard. The calling convention that delivers
the arguments and returns the result stays a named assumption.
-/
namespace LeanOS.Refinement.CSubset

inductive Ty where
  | u8
  | u64
  deriving Repr, DecidableEq

/-- The binary `lean.h` helpers of the subset. -/
inductive BinOp where
  | decEq
  | decLt
  | decLe
  | add
  | sub
  | land
  | lor
  | xor
  | shiftLeft
  | shiftRight
  | mod
  deriving Repr, DecidableEq

/-- The `lean.h` body of each helper, on `uint64_t` operands. -/
def BinOp.eval : BinOp → UInt64 → UInt64 → UInt64
  | .decEq, a, b => if a == b then 1 else 0
  | .decLt, a, b => if a < b then 1 else 0
  | .decLe, a, b => if a ≤ b then 1 else 0
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .land, a, b => a &&& b
  | .lor, a, b => a ||| b
  | .xor, a, b => a ^^^ b
  | .shiftLeft, a, b => a <<< (b % 64)
  | .shiftRight, a, b => a >>> (b % 64)
  | .mod, a, b => if b == 0 then a else a % b

inductive Expr where
  | var (name : String)
  | lit (value : UInt64)
  /-- A `lean.h` helper applied to two operands. -/
  | bin (op : BinOp) (left right : Expr)
  /-- `fn(args…)`: a call of another function on variables. -/
  | call (fn : String) (args : List String)
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

/-- A function: its typed parameters, its result type and its body after
`_start:`. -/
structure Func where
  params : List (String × Ty)
  result : Ty := .u64
  body : List Stmt
  deriving Repr

/-- The meaning of the functions a body may call: a callee name and its
argument words to its result word, `none` when the callee is unknown. -/
abbrev Ext := String → List UInt64 → Option UInt64

/-- No callee is known. -/
def noCalls : Ext := fun _ _ => none

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

def evalExpr (ext : Ext) (env : Env) : Expr → Option UInt64
  | .var name => env.get? name
  | .lit value => some value
  | .bin op left right => do
      let a ← evalExpr ext env left
      let b ← evalExpr ext env right
      pure (op.eval a b)
  | .call fn args => do
      let values ← args.mapM env.get?
      ext fn values

/-- How a statement list ended. -/
inductive Signal where
  | normal (env : Env)
  | jump (label : String) (env : Env)
  | returned (value : UInt64)

/-- The labelled block `label` among the statements of one block list, with
the statements after it (C `goto` continues from the label). -/
def findLabel (label : String) : List Stmt → Option (List Stmt)
  | [] => none
  | .block l body :: rest => if l == label then some (.block l body :: rest) else findLabel label rest
  | _ :: rest => findLabel label rest

/-- Resolve a jump to `label` within the block list `stmts`: continue from
the label when the list has it, otherwise leave the block with the jump. -/
def resolve (label : String) (env : Env) (stmts : List Stmt)
    (continue_ : Env → List Stmt → Option Signal) : Option Signal :=
  match findLabel label stmts with
  | some target => continue_ env target
  | none => some (.jump label env)

/-- Continue after a nested block: run `next` after a normal end, `jump`
after a jump signal, and pass a return or a stuck state through. -/
def seq : Option Signal → (Env → Option Signal) → (String → Env → Option Signal) →
    Option Signal
  | some (.normal env), next, _ => next env
  | some (.jump label env), _, jump => jump label env
  | some (.returned v), _, _ => some (.returned v)
  | none, _, _ => none

/-- `run ext fuel env stmts from_` runs `from_`, a suffix of the block list
`stmts`; `none` is stuck (unbound name, unknown callee, no fuel). A `goto`
to a label of `stmts` continues from that label; a `goto` to any other label
leaves the block with a jump signal that an enclosing block resolves. -/
def run (ext : Ext) : Nat → Env → List Stmt → List Stmt → Option Signal
  | 0, _, _, _ => none
  | _ + 1, env, _, [] => some (.normal env)
  | fuel + 1, env, stmts, stmt :: rest =>
      match stmt with
      | .decl ty name =>
          run ext fuel { env with types := (name, ty) :: env.types } stmts rest
      | .assign name value =>
          match env.ty? name, evalExpr ext env value with
          | some ty, some v =>
              run ext fuel { env with values := (name, truncate ty v) :: env.values } stmts rest
          | _, _ => none
      | .ifZero name thenBranch elseBranch =>
          match env.get? name with
          | none => none
          | some v =>
              if v = 0 then
                seq (run ext fuel env thenBranch thenBranch) (run ext fuel · stmts rest)
                  (fun label env' => resolve label env' stmts (run ext fuel · stmts ·))
              else
                seq (run ext fuel env elseBranch elseBranch) (run ext fuel · stmts rest)
                  (fun label env' => resolve label env' stmts (run ext fuel · stmts ·))
      | .goto label => resolve label env stmts (run ext fuel · stmts ·)
      | .block _ body =>
          seq (run ext fuel env body body) (run ext fuel · stmts rest)
            (fun label env' => resolve label env' stmts (run ext fuel · stmts ·))
      | .ret value => (evalExpr ext env value).map .returned

/-- The result word of a function body's run, converted to the result type. -/
def finish (ty : Ty) : Option Signal → Option UInt64
  | some (.returned v) => some (truncate ty v)
  | some (.normal _) => none
  | some (.jump _ _) => none
  | none => none

/-- Call `func` on argument words, with `ext` giving the meaning of the
functions it calls. Each argument converts to its parameter's type. -/
def callWith (ext : Ext) (func : Func) (args : List UInt64) : Option UInt64 :=
  if func.params.length != args.length then none
  else
    let env : Env :=
      { types := func.params
        values := (func.params.zip args).map fun (p, a) => (p.1, truncate p.2 a) }
    finish func.result (run ext 256 env func.body func.body)

/-- Call a function that calls nothing. -/
def call (func : Func) (args : List UInt64) : Option UInt64 :=
  callWith noCalls func args

/-- Add the extracted function `func` under the C name `name` to an
environment: calls of `name` run `func` with the callees of `ext`. -/
def Ext.add (ext : Ext) (name : String) (func : Func) : Ext :=
  fun fn args => if fn == name then callWith ext func args else ext fn args

/-- The word a C `uint8_t` holds for a Lean `Bool`. -/
def boolWord (b : Bool) : UInt64 := if b then 1 else 0

end LeanOS.Refinement.CSubset
