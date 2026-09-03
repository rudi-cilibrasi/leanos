import Lean

/-!
# Exported boundary inventory generator

This host-only executable loads the compiled `LeanOS` environment and lists
every declaration carrying an `@[export leanos_…]` attribute together with the
shape of its type.  The build renders the scalar rows into the generated
`boundary-abi.h` prototype header that the kernel and the hosted harnesses
include, so a C caller can only declare an exported entry point with the arity
the Lean definition actually has.  The attribute is the single source of
truth; nothing here is transcribed from C.  The generator, the C compiler, and
the consumers remain trusted integration steps rather than proved refinement.
-/
namespace LeanOS.BoundaryABIGenerator

open Lean

/-- The binder domains and the result of an exported type, in order, as
`u64` for `UInt64` or the printed Lean type otherwise. -/
partial def shape : Expr → List String
  | .forallE _ domain body _ =>
    (if domain.isConstOf ``UInt64 then "u64" else toString domain) :: shape body
  | result => [if result.isConstOf ``UInt64 then "u64" else toString result]

structure Row where
  symbol : String
  declaration : String
  module : String
  shape : List String

def Row.isScalar (row : Row) : Bool := row.shape.all (· == "u64")

def Row.arity (row : Row) : Nat := row.shape.length - 1

def collect (env : Environment) (prefix_ : String) : Array Row := Id.run do
  let mut rows : Array Row := #[]
  for (declaration, info) in env.constants.toList do
    match getExportNameFor? env declaration with
    | none => pure ()
    | some symbol =>
      if (toString symbol).startsWith prefix_ then
        let module := ((env.getModuleIdxFor? declaration).bind
          (fun index => env.header.moduleNames[index.toNat]?)).map toString
          |>.getD "?"
        rows := rows.push
          { symbol := toString symbol, declaration := toString declaration
            module, shape := shape info.type }
  return rows.qsort (fun a b => a.symbol < b.symbol)

def emit (rows : Array Row) (revision : String) : IO Unit := do
  IO.println "leanos-abi\t1"
  IO.println s!"source-revision\t{revision}"
  for row in rows do
    if row.isScalar then
      IO.println s!"export\t{row.symbol}\t{row.arity}\t{row.declaration}\t{row.module}"
    else
      IO.println
        s!"object-export\t{row.symbol}\t{String.intercalate "," row.shape}\t{row.declaration}\t{row.module}"

def run (args : List String) : IO Unit := do
  let root := match args with
    | [] => `LeanOS
    | [name] => name.toName
    | _ => panic! "usage: leanos-abi [root-module]"
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := root }] {} 0
  let revision := (← IO.getEnv "LEANOS_SOURCE_REVISION").getD "unknown"
  emit (collect env "leanos_") revision

end LeanOS.BoundaryABIGenerator

def main (args : List String) : IO Unit := LeanOS.BoundaryABIGenerator.run args
