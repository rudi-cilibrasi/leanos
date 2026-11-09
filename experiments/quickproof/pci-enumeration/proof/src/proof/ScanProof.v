(* The body proofs of the unit patch/enum_unit.c (boot/pci-enumeration.h and its wrapper), for every device
   predicate Dev: pci_enumeration_finish, pci_enumerate_segment (the scan, against the model `scan` of Defs.v, proved
   in ScanSegment.v) and enum_scan (one call). *)
Require Import VST.floyd.proofauto.
Require Import LeanosEnum.enum.code.
Require Import LeanosEnum.proof.Defs.
Require Import LeanosEnum.proof.EnumSpecs.
Require LeanosEnum.proof.ScanSegment.
#[local] Existing Instance EnumSpecs.CS.
Local Open Scope Z_scope.

Lemma body_pci_enumeration_finish (Dev: val -> list answer -> mpred) :
  semax_body Vprog (Gprog Dev) f_pci_enumeration_finish finish_spec.
Proof.
  start_function.
  unfold maybe_at.
  destruct (Val.eq result nullval).
  - subst. forward_if (PROP () LOCAL (temp _status (Vint (Int.repr st))) SEP ()).
    + contradiction.
    + forward. entailer!.
    + forward.
  - forward_if (PROP () LOCAL (temp _status (Vint (Int.repr st)))
                SEP (data_at Tsh t_result (result_val st b d f off) result)).
    + forward. forward. forward. forward. forward. unfold result_val. entailer!. apply derives_refl.
    + contradiction.
    + forward. unfold maybe_at. destruct (Val.eq result nullval); [ contradiction | apply derives_refl ].
Qed.

Lemma body_pci_enumerate_segment (Dev: val -> list answer -> mpred) :
  semax_body Vprog (Gprog Dev) f_pci_enumerate_segment (enum_spec Dev).
Proof. exact (ScanSegment.body_segment Dev). Qed.

Lemma body_enum_scan (Dev: val -> list answer -> mpred) :
  semax_body Vprog (Gprog Dev) f_enum_scan (enum_scan_spec Dev).
Proof.
  start_function.
  forward_call (read, ctx, snapshot, sold, result, rold).
  Intros vret. destruct vret as [[[[[h st] i] off] pub] rest]. cbn [fst snd] in *.
  forward.
  Exists h st i off pub rest.
  entailer!.
Qed.
