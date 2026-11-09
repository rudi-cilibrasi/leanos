(* Law capabilities_adversarial: the harness's header tables (header_offsets, masks), and tactics for the loops of
   main's checks. *)
Require Import VST.floyd.proofauto.
Require Import LeanosCaps.proof.Defs.
Require LeanosCaps.proof.CapsSpecs.
Require Import LeanosCaps.proof.AdvProg LeanosCaps.proof.AdvWalk LeanosCaps.proof.AdvFacts LeanosCaps.proof.AdvSpecs
  LeanosCaps.proof.AdvLib.
Local Open Scope Z_scope.

(* header_offsets and masks, as main stores them. *)
Definition OL : list val := [Vint (Int.repr 0); Vint (Int.repr 4); Vint (Int.repr 12); Vint (Int.repr 52)].
Definition ML : list val :=
  [Vint (Int.repr 4294967295); Vint (Int.repr 1048576); Vint (Int.repr 16711680); Vint (Int.repr 255)].

Lemma repr_m1: Int.repr (-1) = Int.repr 4294967295.
Proof. apply Int.eqm_samerepr. exists (-1). reflexivity. Qed.

Lemma OL_eq: upd_Znth 3 (upd_Znth 2 (upd_Znth 1 (upd_Znth 0 (@default_val LCS (tarray tuchar 4))
    (Vint (Int.repr 0))) (Vint (Int.repr 4))) (Vint (Int.repr 12))) (Vint (Int.repr 52)) = OL.
Proof. reflexivity. Qed.

Lemma ML_eq: upd_Znth 3 (upd_Znth 2 (upd_Znth 1 (upd_Znth 0 (@default_val LCS (tarray tuint 4))
    (Vint (Int.repr 4294967295))) (Vint (Int.repr 1048576))) (Vint (Int.repr 16711680))) (Vint (Int.repr 255)) = ML.
Proof. reflexivity. Qed.

Lemma Znth_OL: forall k, 0 <= k < 4 -> Znth k OL = Vint (Int.repr (hc_off k)).
Proof.
  intros k Hk. assert (E: k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia.
  destruct E as [ -> | [ -> | [ -> | -> ] ] ]; reflexivity.
Qed.

Lemma Znth_ML: forall k, 0 <= k < 4 -> Znth k ML = Vint (Int.repr (hc_mask k)).
Proof.
  intros k Hk. assert (E: k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia.
  destruct E as [ -> | [ -> | [ -> | -> ] ] ]; reflexivity.
Qed.

Lemma hc_off_range: forall k, 0 <= k < 4 -> 0 <= hc_off k <= 52 /\ 0 <= hc_off k / 4 < 16.
Proof.
  intros k Hk. assert (E: k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia.
  destruct E as [ -> | [ -> | [ -> | -> ] ] ]; unfold hc_off; simpl; lia.
Qed.

Lemma hc_mask_range: forall k, 0 <= k < 4 -> 0 <= hc_mask k <= Int.max_unsigned.
Proof.
  intros k Hk. assert (E: k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia.
  destruct E as [ -> | [ -> | [ -> | -> ] ] ]; unfold hc_mask; simpl; rep_lia.
Qed.

Lemma divs4_repr: forall o, 0 <= o <= 255 -> Int.divs (Int.repr o) (Int.repr 4) = Int.repr (o / 4).
Proof.
  intros o Ho. unfold Int.divs. rewrite !Int.signed_repr by rep_lia. f_equal.
  rewrite Z.quot_div_nonneg by lia. reflexivity.
Qed.

(* A loop from k = 0 (the temp kid just set) while the state stays the same; n bounds k. *)
Ltac loop_from kid n :=
  match goal with |- semax _ (PROPx ?Ps (LOCALx (temp kid _ :: ?Q) (SEPx ?R))) _ _ =>
    forward_loop (EX k: Z, PROPx ((0 <= k <= n) :: Ps) (LOCALx (temp kid (Vint (Int.repr k)) :: Q) (SEPx R)))
      break: (PROPx Ps (LOCALx Q (SEPx R)))
  end.

(* A counting loop of n iterations whose body keeps the state. *)
Ltac for_same n :=
  match goal with |- semax _ (PROPx ?Ps (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_for_simple_bound n (EX i: Z, PROPx Ps (LOCALx Q (SEPx R)))
  end.

(* An if-then without else whose branch keeps the state: join at the current precondition. *)
Ltac if_same :=
  match goal with |- semax _ ?Pre _ _ => forward_if Pre end.

(* A load whose value is given by the equation E (on a Znth of the device's arrays). *)
Ltac ldv E :=
  forward;
  try solve [ entailer!; znth_val; rewrite E; simpl; first [ exact I | rewrite Int.unsigned_repr by rep_lia; rep_lia ] ];
  znth_val; try rewrite E;
  try solve [ entailer!; first [ exact I | rep_lia | rewrite Int.unsigned_repr by rep_lia; rep_lia
                                | simpl; first [ exact I | rep_lia | rewrite Int.unsigned_repr by rep_lia; rep_lia ] ] ].

(* The typecheck of a division by 4: no overflow. *)
Ltac div4_tc :=
  entailer!;
  match goal with E: _ /\ Int.repr 4 = Int.mone |- _ =>
    destruct E as [_ E]; apply (f_equal Int.unsigned) in E; vm_compute in E; discriminate end.
