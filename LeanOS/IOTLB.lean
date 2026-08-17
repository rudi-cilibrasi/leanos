import LeanOS.IOMMU

/-!
# Finite IOMMU translation-cache vocabulary

This module starts the stale-IOMMU-translation model with a bounded cache whose
keys retain every software lifetime needed to distinguish source, assignment,
domain, mapping, and access direction.  It deliberately does not claim VT-d or
QEMU correspondence yet.  Later transition work can require these exact keys
in invalidation tickets before publishing IOMMU mutations or frame reuse.
-/

namespace LeanOS.IOMMU.IOTLB

structure Key where
  source : SourceId
  assignment : AssignmentHandle
  domain : DomainHandle
  mapping : MappingHandle
  iova : IOVA
  direction : Direction
  deriving BEq, DecidableEq, Repr

structure Entry where
  key : Key
  frame : FrameHandle
  permission : Permission
  deriving BEq, DecidableEq, Repr

def capacity : Nat := maxMappings

def lookup (entries : List Entry) (key : Key) : Option Entry :=
  entries.find? fun entry => decide (entry.key = key)

def eraseKey (entries : List Entry) (key : Key) : List Entry :=
  entries.filter fun entry => decide (entry.key ≠ key)

def eraseMapping (entries : List Entry) (mapping : MappingHandle) : List Entry :=
  entries.filter fun entry => decide (entry.key.mapping ≠ mapping)

def eraseAssignment (entries : List Entry)
    (assignment : AssignmentHandle) : List Entry :=
  entries.filter fun entry => decide (entry.key.assignment ≠ assignment)

def insert (entries : List Entry) (entry : Entry) : List Entry :=
  (entry :: eraseKey entries entry.key).take capacity

def Coherent (entries : List Entry) : Prop := entries.length ≤ capacity

theorem erase_mapping_length entries mapping :
    (eraseMapping entries mapping).length ≤ entries.length := by
  exact List.length_filter_le _ _

theorem erase_assignment_length entries assignment :
    (eraseAssignment entries assignment).length ≤ entries.length := by
  exact List.length_filter_le _ _

theorem insert_coherent entries entry : Coherent (insert entries entry) := by
  simp [Coherent, insert, Nat.min_le_left]

theorem erase_mapping_absent entries mapping key
    (hkey : key.mapping = mapping) :
    lookup (eraseMapping entries mapping) key = none := by
  simp only [lookup, List.find?_eq_none, eraseMapping, List.mem_filter]
  intro entry hentry hfound
  have hne := of_decide_eq_true hentry.2
  have heq := of_decide_eq_true hfound
  exact hne (congrArg Key.mapping heq |>.trans hkey)

theorem erase_assignment_absent entries assignment key
    (hkey : key.assignment = assignment) :
    lookup (eraseAssignment entries assignment) key = none := by
  simp only [lookup, List.find?_eq_none, eraseAssignment, List.mem_filter]
  intro entry hentry hfound
  have hne := of_decide_eq_true hentry.2
  have heq := of_decide_eq_true hfound
  exact hne (congrArg Key.assignment heq |>.trans hkey)

theorem erase_mapping_preserves_coherent entries mapping
    (hcoherent : Coherent entries) : Coherent (eraseMapping entries mapping) := by
  exact Nat.le_trans (erase_mapping_length entries mapping) hcoherent

theorem erase_assignment_preserves_coherent entries assignment
    (hcoherent : Coherent entries) : Coherent (eraseAssignment entries assignment) := by
  exact Nat.le_trans (erase_assignment_length entries assignment) hcoherent

end LeanOS.IOMMU.IOTLB
