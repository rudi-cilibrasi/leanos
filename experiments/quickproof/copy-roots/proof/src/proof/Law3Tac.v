(* Law window_scan_exact: tactics and lemmas for the proof of main (src/contracts/window_scan_exact.v). *)
Require Import VST.floyd.proofauto.
Require Import LeanosRoots.proof.Defs.
Require Import LeanosRoots.proof.Law3Facts.
Require LeanosRoots.proof.RootsSpecs.
Local Open Scope Z_scope.

(* The indices of the SEP items of R that mention neither p nor q (syntactically). *)
Ltac sep_idx_free R p q i :=
  lazymatch R with
  | nil => constr:(@nil Z)
  | ?x :: ?R' =>
      let rest := sep_idx_free R' p q (Z.succ i) in
      match x with
      | context [p] => rest
      | context [q] => rest
      | _ => constr:(i :: rest)
      end
  end.

(* Freeze every SEP item but those at p and q: VST's cancellation then never compares two big structs. *)
Ltac freeze_except p q F :=
  match goal with
  | |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
      let L := sep_idx_free R p q 0 in let L := eval cbn in L in freeze_tac L F
  | |- ENTAIL _, (PROPx _ (LOCALx _ (SEPx ?R))) |-- _ =>
      let L := sep_idx_free R p q 0 in let L := eval cbn in L in freeze_tac_entail L F
  end.


(* The SEP items that mention p or q (syntactically): their indices. *)
Ltac sep_idx_with R p q i :=
  lazymatch R with
  | nil => constr:(@nil Z)
  | ?x :: ?R' =>
      let rest := sep_idx_with R' p q (Z.succ i) in
      match x with
      | context [p] => constr:(i :: rest)
      | context [q] => constr:(i :: rest)
      | _ => rest
      end
  end.

Ltac freeze_only p q F :=
  match goal with
  | |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
      let L := sep_idx_with R p q 0 in let L := eval cbn in L in freeze_tac L F
  | |- ENTAIL _, (PROPx _ (LOCALx _ (SEPx ?R))) |-- _ =>
      let L := sep_idx_with R p q 0 in let L := eval cbn in L in freeze_tac_entail L F
  end.

Lemma assume_le16: forall n, 0 <= n <= Int64.max_unsigned ->
  Int.repr (Z.b2z (negb (Int64.ltu (Int64.repr 16) (Int64.repr n)))) <> Int.zero -> n <= 16.
Proof.
  intros n Hn H. unfold Int64.ltu in H. rewrite !Int64.unsigned_repr in H by rep_lia.
  destruct (zlt 16 n); [ simpl in H; exfalso; apply H; reflexivity | lia ].
Qed.

Lemma writable_repr: forall b, 0 <= b <= Byte.max_unsigned ->
  Int.and (Int.repr b) (Int.repr 1) = Int.repr (Z.land b 1) /\ 0 <= Z.land b 1 <= 1.
Proof.
  intros b Hb. change Byte.max_unsigned with 255 in Hb. split.
  - unfold Int.and. rewrite !Int.unsigned_repr by rep_lia. reflexivity.
  - assert (E: Z.land b 1 = b mod 2) by (change 1 with (Z.ones 1) at 1; rewrite Z.land_ones by lia; reflexivity).
    rewrite E. pose proof (Z.mod_pos_bound b 2 ltac:(lia)). lia.
Qed.

Lemma b2z_true: forall c, Int.repr (RootsSpecs.b2z c) <> Int.zero -> c = true.
Proof. intros c H. destruct c; [ reflexivity | exfalso; apply H; reflexivity ]. Qed.

Lemma b2z_false: forall c, Int.repr (RootsSpecs.b2z c) = Int.zero -> c = false.
Proof. intros c H. destruct c; [ exfalso; apply Int.one_not_zero; exact H | reflexivity ]. Qed.

(* The branches on a boolean of a temp. *)
Ltac b2z_hyps :=
  repeat match goal with
  | E: Int.repr (RootsSpecs.b2z _) <> Int.zero |- _ => apply b2z_true in E
  | E: Int.repr (RootsSpecs.b2z _) = Int.zero |- _ => apply b2z_false in E
  end.

(* The index of the first SEP item of R that mentions p. *)
Ltac sep_idx_of R p i :=
  lazymatch R with
  | ?x :: ?R' => match x with context [p] => eval cbn in i | _ => sep_idx_of R' p (Z.succ i) end
  end.

(* Bring the SEP items at p1, ..., pk to the front, in this order. *)
Ltac sep_front1 p1 :=
  match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
    let i := sep_idx_of R p1 0%Z in grab_indexes_SEP (i :: nil) end.
Ltac sep_front2 p1 p2 :=
  match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
    let i := sep_idx_of R p1 0%Z in let j := sep_idx_of R p2 0%Z in grab_indexes_SEP (i :: j :: nil) end.
Ltac sep_front4 p1 p2 p3 p4 :=
  match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
    let i := sep_idx_of R p1 0%Z in let j := sep_idx_of R p2 0%Z in
    let k := sep_idx_of R p3 0%Z in let l := sep_idx_of R p4 0%Z in grab_indexes_SEP (i :: j :: k :: l :: nil) end.

(* Before a call on the objects at p and q (in the order of the callee's precondition): freeze the rest and
   put them first, so that cancellation matches at the first try. *)
Ltac prep1 p F := freeze_except p p F; sep_front1 p.
Ltac prep2 p q F := freeze_except p q F; sep_front2 p q.

Lemma frames_len {cs: compspecs}: forall sh (fs: list Z) p, Zlength fs = 16 ->
  data_at sh (tarray tulong 16) (RootsSpecs.longs fs) p |-- data_at sh (tarray tulong (Zlength fs)) (RootsSpecs.longs fs) p.
Proof. intros sh fs p E. rewrite E. apply derives_refl. Qed.

Lemma Znth_longs': forall i l, 0 <= i < Zlength l -> Znth i (RootsSpecs.longs l) = Vlong (Int64.repr (Znth i l)).
Proof. intros. unfold RootsSpecs.longs. rewrite Znth_map by lia. reflexivity. Qed.

(* A load of a word of a root or an array of words. *)
Ltac ld :=
  forward;
  try (entailer!; unfold RootsSpecs.longs; rewrite Znth_map by (unfold LEAVES in *; lia); exact I);
  repeat rewrite Znth_longs' by (unfold LEAVES in *; lia).

Lemma odd_neq: forall c, 0 <= c <= Int64.max_unsigned ->
  Int64.and (Int64.repr c) (Int64.repr 1) <> Int64.repr 0 -> Z.odd c = true.
Proof.
  intros c Hc N. pose proof (present_repr c Hc) as P. destruct (Z.odd c); auto.
  exfalso. apply N. apply Int64.same_if_eq. rewrite P. reflexivity.
Qed.

Lemma odd_eq: forall c, 0 <= c <= Int64.max_unsigned ->
  Int64.and (Int64.repr c) (Int64.repr 1) = Int64.repr 0 -> Z.odd c = false.
Proof.
  intros c Hc E. pose proof (present_repr c Hc) as P. rewrite E in P. rewrite Int64.eq_true in P.
  destruct (Z.odd c); auto.
Qed.

Ltac odd_hyps :=
  change Int64.zero with (Int64.repr 0) in *;
  repeat match goal with
  | E: Int64.and (Int64.repr ?c) (Int64.repr 1) <> Int64.repr 0 |- _ => apply odd_neq in E; [ | rep_lia ]
  | E: Int64.and (Int64.repr ?c) (Int64.repr 1) = Int64.repr 0 |- _ => apply odd_eq in E; [ | rep_lia ]
  end.

(* Rewrite the goal with the boolean facts of the context. *)
Ltac bsubst :=
  repeat match goal with
  | E: Z.eqb ?a ?b = ?c |- context [Z.eqb ?a ?b] => rewrite E
  | E: ?f ?x = ?c |- context [?f ?x] => match type of c with bool => rewrite E end
  end.

Lemma frame_repr': forall c, 0 <= c <= Int64.max_unsigned ->
  Int64.shru (Int64.repr (Z.land c ADDRESS_MASK)) (Int64.repr 12) = Int64.repr (frame_of c).
Proof.
  intros c Hc. unfold Int64.shru. rewrite !Int64.unsigned_repr by (try apply land_range; rep_lia). reflexivity.
Qed.

Lemma in_slots_then: forall w i, 0 <= i <= Int64.max_unsigned -> 0 <= w_slot w <= Int64.max_unsigned ->
  w_slot w <= i ->
  Vint (Int.repr (RootsSpecs.b2z (in_slots w i))) =
  bool2val (Int64.cmpu Clt (Int64.repr i) (Int64.repr (w_slot w + pages_of w))).
Proof.
  intros w i Hi Hs Hle. unfold in_slots, Int64.cmpu, Int64.ltu.
  rewrite (Int64.unsigned_repr i) by lia. rewrite Int64.unsigned_repr_eq.
  destruct (Z.leb_spec (w_slot w) i); [ | lia ]. simpl andb.
  destruct (zlt i ((w_slot w + pages_of w) mod Int64.modulus));
  destruct (Z.ltb_spec i ((w_slot w + pages_of w) mod W)); unfold W in *; try lia; reflexivity.
Qed.

Lemma in_slots_else: forall w i, i < w_slot w -> Vint (Int.repr (RootsSpecs.b2z (in_slots w i))) = Vint (Int.repr 0).
Proof.
  intros w i Hlt. unfold in_slots. destruct (Z.leb_spec (w_slot w) i); [ lia | reflexivity ].
Qed.

Lemma wr_true: forall wr, Int.repr wr <> Int.zero -> (wr =? 0) = false.
Proof. intros wr N. apply Z.eqb_neq. intro E. subst. apply N. reflexivity. Qed.

Lemma wr_false: forall wr, 0 <= wr <= 1 -> Int.repr wr = Int.zero -> (wr =? 0) = true.
Proof.
  intros wr R E. apply Z.eqb_eq. apply (f_equal Int.unsigned) in E.
  rewrite Int.unsigned_repr in E by rep_lia. exact E.
Qed.

(* Unsigned comparisons as comparisons of Z (the pilot's to_z). *)
Ltac to_z :=
  repeat match goal with
  | H: context [Int.unsigned (Int.repr ?n)] |- _ => rewrite (Int.unsigned_repr n) in H by rep_lia
  | H: context [Int64.unsigned (Int64.repr ?n)] |- _ => rewrite (Int64.unsigned_repr n) in H by rep_lia
  | H: Int64.ltu ?a ?b = true |- _ =>
      unfold Int64.ltu in H; match type of H with context [zlt ?x ?y] => destruct (zlt x y); [ clear H | discriminate ] end
  | H: Int64.ltu ?a ?b = false |- _ =>
      unfold Int64.ltu in H; match type of H with context [zlt ?x ?y] => destruct (zlt x y); [ discriminate | clear H ] end
  | H: negb ?c = true |- _ => apply negb_true_iff in H
  | H: negb ?c = false |- _ => apply negb_false_iff in H
  end.

Lemma want_repr': forall base p slot (wr: bool),
  0 <= base <= Int64.max_unsigned -> 0 <= p <= Int64.max_unsigned -> 0 <= slot <= Int64.max_unsigned ->
  Int64.or (Int64.or (Int64.or
     (Int64.shl (Int64.add (Int64.shru (Int64.repr base) (Int64.repr 12)) (Int64.repr (p - slot)))
                (Int64.repr 12))
     (Int64.repr 1)) (Int64.shl (Int64.repr 1) (Int64.repr 63))) (Int64.repr (if wr then 2 else 0)) =
  Int64.repr (Z.lor (Z.lor (Z.lor (((Z.shiftr base 12 + (p - slot) mod W) mod W * 4096) mod W) 1) NX)
                    (if wr then 2 else 0)).
Proof.
  intros base p slot wr Hb Hp Hs.
  replace (Int64.repr (p - slot)) with (Int64.sub (Int64.repr p) (Int64.repr slot))
    by (unfold Int64.sub; rewrite !Int64.unsigned_repr by lia; reflexivity).
  apply want_repr; auto.
Qed.

(* The SEP items that mention none of p1 .. p4. *)
Ltac sep_idx_free4 R p1 p2 p3 p4 i :=
  lazymatch R with
  | nil => constr:(@nil Z)
  | ?x :: ?R' =>
      let rest := sep_idx_free4 R' p1 p2 p3 p4 (Z.succ i) in
      match x with
      | context [p1] => rest
      | context [p2] => rest
      | context [p3] => rest
      | context [p4] => rest
      | _ => constr:(i :: rest)
      end
  end.

Ltac prep4 p1 p2 p3 p4 F :=
  match goal with
  | |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
      let L := sep_idx_free4 R p1 p2 p3 p4 0 in let L := eval cbn in L in freeze_tac L F
  end;
  sep_front4 p1 p2 p3 p4.

(* The SEP items that are not objects at p or q: their indices. *)
Ltac sep_idx_not_at R p q i :=
  lazymatch R with
  | nil => constr:(@nil Z)
  | ?x :: ?R' =>
      let rest := sep_idx_not_at R' p q (Z.succ i) in
      match x with
      | data_at _ _ _ p => rest
      | data_at _ _ _ q => rest
      | data_at_ _ _ p => rest
      | data_at_ _ _ q => rest
      | _ => constr:(i :: rest)
      end
  end.

(* Freeze every SEP item but the objects at p and q, which come first. *)
Ltac prep_at p q F :=
  match goal with
  | |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
      let L := sep_idx_not_at R p q 0 in let L := eval cbn in L in freeze_tac L F
  end;
  sep_front2 p q.

(* Freeze every SEP item. *)
Ltac freeze_all F :=
  match goal with
  | |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
      let n := eval cbn in (Zlength R) in
      let L := eval cbn in (map Z.of_nat (seq 0 (Z.to_nat n))) in freeze_tac L F
  end.
