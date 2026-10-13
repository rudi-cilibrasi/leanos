/-!
# Oracle vector record

One row of the bounded scalar boundary oracle (`LeanOS.Oracle`): the row's
stable identifier, the adapter it exercises, its input words, and the expected
control and value words evaluated from the Lean adapter definitions.  The
corpus is split by adapter family into the `LeanOS.Oracle.*` modules (issue
#558) so the families elaborate in parallel; `LeanOS.Oracle` concatenates them
in the stable schema order.
-/
namespace LeanOS.Oracle

structure Vector where
  id : String
  adapter : String
  words : List UInt64
  expected : UInt64
  expectedValue : UInt64 := 0
  deriving Repr

end LeanOS.Oracle
