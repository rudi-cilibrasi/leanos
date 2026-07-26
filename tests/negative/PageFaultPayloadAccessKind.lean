import LeanOS.InterruptEntry
import LeanOS.X86PageTable

open LeanOS InterruptEntry

/-- A caller-selected execute tag cannot relabel a raw user-read error word. -/
example :
    (DecodedPageFaultError.mk false false true false).accessKind =
        X86PageTable.AccessKind.execute := by
  native_decide
