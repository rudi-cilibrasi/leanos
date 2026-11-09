(* Pure lemmas for the body proofs of include/boot_handoff_decode.h (Hd*.v): 32- and 64-bit words and their C
   comparisons, the arrays of 64-bit words as they fill, the two decoder states as two rows, and how the model's
   memory updates compose. *)
Require Import VST.floyd.proofauto.
Require Import LeanosHandoff.handoff.code.
Require Import LeanosHandoff.proof.Defs.
Require Import LeanosHandoff.proof.HandoffSpecs.
#[local] Existing Instance HandoffSpecs.CS.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* ---------- words ---------- *)

Lemma eq64_repr: forall a b, u64_ok a -> u64_ok b -> Int64.eq (Int64.repr a) (Int64.repr b) = (a =? b).
Proof.
  intros. unfold u64_ok in *. unfold Int64.eq. rewrite !Int64.unsigned_repr by auto.
  destruct (zeq a b); destruct (Z.eqb_spec a b); auto; lia.
Qed.

Lemma ltu64_repr: forall a b, u64_ok a -> u64_ok b -> Int64.ltu (Int64.repr a) (Int64.repr b) = (a <? b).
Proof.
  intros. unfold u64_ok in *. unfold Int64.ltu. rewrite !Int64.unsigned_repr by auto.
  destruct (zlt a b); destruct (Z.ltb_spec a b); auto; lia.
Qed.

Lemma repr64_inj: forall a b, u64_ok a -> u64_ok b -> Int64.repr a = Int64.repr b -> a = b.
Proof. intros. unfold u64_ok in *. apply repr_inj_unsigned64; auto. Qed.

Lemma repr32_inj: forall a b, u32_ok a -> u32_ok b -> Int.repr a = Int.repr b -> a = b.
Proof. intros. unfold u32_ok in *. apply repr_inj_unsigned; auto. Qed.

Lemma repr64_neq: forall a b, Int64.repr a <> Int64.repr b -> a <> b.
Proof. intros a b H E. subst. contradiction. Qed.

Lemma repr32_neq: forall a b, Int.repr a <> Int.repr b -> a <> b.
Proof. intros a b H E. subst. contradiction. Qed.

Lemma u32_u64: forall a, u32_ok a -> u64_ok a.
Proof. unfold u32_ok, u64_ok. intros. rep_lia. Qed.

Lemma repr_mod32: forall z, Int.repr (z mod 2 ^ 32) = Int.repr z.
Proof. intros. rewrite <- (Int.repr_unsigned (Int.repr z)), Int.unsigned_repr_eq. reflexivity. Qed.

Lemma and7_repr: forall a, 0 <= a <= Int.max_unsigned -> Int.and (Int.repr a) (Int.repr 7) = Int.repr (a mod 8).
Proof.
  intros. change (Int.repr 7) with (Int.repr (two_p 3 - 1)). rewrite <- Int.zero_ext_and by lia.
  rewrite <- (Int.repr_unsigned (Int.zero_ext 3 _)). rewrite Int.zero_ext_mod by (cbn; lia).
  rewrite Int.unsigned_repr by lia. reflexivity.
Qed.

Lemma and7_zero: forall a, 0 <= a <= Int.max_unsigned ->
  (Int.and (Int.repr a) (Int.repr 7) = Int.repr 0 <-> a mod 8 = 0).
Proof.
  intros. rewrite and7_repr by auto. split; intros E.
  - apply repr_inj_unsigned in E; [ auto | pose proof (Z.mod_pos_bound a 8); rep_lia | rep_lia ].
  - rewrite E. reflexivity.
Qed.

(* A 32-bit value passed to a 64-bit parameter. *)
Lemma i2l_repr: forall a, u32_ok a -> Int64.repr (Int.unsigned (Int.repr a)) = Int64.repr a.
Proof. intros. rewrite Int.unsigned_repr by (unfold u32_ok in *; auto). reflexivity. Qed.

Lemma vl_u32: forall a, u32_ok a -> Vlong (Int64.repr (Int.unsigned (Int.repr a))) = vl a.
Proof. intros. unfold vl. rewrite Int.unsigned_repr by (unfold u32_ok in *; auto). reflexivity. Qed.

(* The comparisons of a 64-bit word with another, or with a 32-bit one, as the C makes them. *)
Lemma ne64: forall a b, u64_ok a -> u64_ok b -> Int64.repr a <> Int64.repr b -> (a =? b) = false.
Proof. intros. apply Z.eqb_neq. intro E. subst. contradiction. Qed.

Lemma eq64: forall a b, u64_ok a -> u64_ok b -> Int64.repr a = Int64.repr b -> (a =? b) = true.
Proof. intros. apply Z.eqb_eq. apply repr64_inj; auto. Qed.

(* ---------- the arrays of 64-bit words as they fill ---------- *)

Lemma upd_fill: forall (a: list Z) (v: Z) n,
  Zlength a < n ->
  upd_Znth (Zlength a) (map vl a ++ Zrepeat Vundef (n - Zlength a)) (vl v) =
  map vl (a ++ [v]) ++ Zrepeat Vundef (n - (Zlength a + 1)).
Proof.
  intros. rewrite map_app.
  rewrite upd_Znth_app2 by (rewrite Zlength_map, Zlength_Zrepeat; lia).
  rewrite Zlength_map, Z.sub_diag.
  replace (n - Zlength a) with (1 + (n - (Zlength a + 1))) by lia.
  rewrite <- Zrepeat_app by lia. rewrite upd_Znth_app1 by (rewrite Zlength_Zrepeat; lia).
  rewrite <- app_assoc. f_equal.
Qed.

Lemma fill_full: forall (a: list Z) n, Zlength a = n -> map vl a ++ Zrepeat Vundef (n - Zlength a) = map vl a.
Proof. intros. rewrite H, Z.sub_diag. apply app_nil_r. Qed.

Lemma fill_empty: forall n, 0 <= n -> map vl [] ++ Zrepeat Vundef (n - Zlength (@nil Z)) = Zrepeat Vundef n.
Proof. intros. rewrite Zlength_nil, Z.sub_0_r. reflexivity. Qed.

(* ---------- the model's memory ---------- *)

Lemma with_copy_same: forall m, with_copy m (m_copy m) = m.
Proof. intros [] ; reflexivity. Qed.

Lemma with_bitmaps_same: forall m, with_bitmaps m (m_usable m) (m_blocked m) (m_reserved m) = m.
Proof. intros [] ; reflexivity. Qed.

Lemma with_states_same: forall m, with_states m (m_states m) (m_at m) = m.
Proof. intros [] ; reflexivity. Qed.

(* ---------- the run ---------- *)

Lemma run_one: forall x p h s m v,
  run x p h = Some (Go s m) -> run x p (h ++ [(expected x s m, v)]) = Some (step x s m v).
Proof. intros. apply run_snoc. auto. Qed.

(* A status constant is a status; two distinct ones differ. *)
Ltac sok := unfold status_ok; split; vm_compute; discriminate.
Ltac sne := let E := fresh in intro E; vm_compute in E; discriminate.

Lemma sub32: forall a b, 0 <= b <= a -> a <= Int.max_unsigned -> Int.sub (Int.repr a) (Int.repr b) = Int.repr (a - b).
Proof. intros. unfold Int.sub. rewrite !Int.unsigned_repr by lia. reflexivity. Qed.

(* Decide the comparisons of a check from the hypotheses, one at a time. *)
Ltac zb :=
  repeat (first [ rewrite (proj2 (Z.eqb_eq _ _)) by lia | rewrite (proj2 (Z.eqb_neq _ _)) by lia
                | rewrite (proj2 (Z.ltb_lt _ _)) by lia | rewrite (proj2 (Z.ltb_ge _ _)) by lia
                | rewrite (proj2 (Z.leb_le _ _)) by lia | rewrite (proj2 (Z.leb_gt _ _)) by lia ];
          cbn [negb]).

Lemma Forall_u64_Znth: forall a j, Forall u64_ok a -> 0 <= j < Zlength a -> u64_ok (Znth j a).
Proof. intros. apply (proj1 (Forall_Znth a u64_ok) H j H0). Qed.

Ltac u64 :=
  first [ assumption | apply Forall_u64_Znth; [ assumption | lia ] | apply u32_u64; assumption
        | unfold u64_ok; rep_lia ].

(* The C's comparisons of 64-bit words, as hypotheses about the words. *)
Ltac w64 :=
  repeat match goal with
  | H: context [Int64.zero] |- _ => change Int64.zero with (Int64.repr 0) in H
  | H: context [Int64.one] |- _ => change Int64.one with (Int64.repr 1) in H
  | H: Int64.repr ?a <> Int64.repr ?b |- _ => apply repr64_neq in H
  | H: Int64.repr ?a = Int64.repr ?b |- _ => apply repr64_inj in H; [ | u64 | u64 ]
  | H: Int64.eq (Int64.repr ?a) (Int64.repr ?b) = true |- _ =>
      rewrite eq64_repr in H by u64; apply Z.eqb_eq in H
  | H: Int64.eq (Int64.repr ?a) (Int64.repr ?b) = false |- _ =>
      rewrite eq64_repr in H by u64; apply Z.eqb_neq in H
  | H: Int64.ltu (Int64.repr ?a) (Int64.repr ?b) = true |- _ =>
      rewrite ltu64_repr in H by u64; apply Z.ltb_lt in H
  | H: Int64.ltu (Int64.repr ?a) (Int64.repr ?b) = false |- _ =>
      rewrite ltu64_repr in H by u64; apply Z.ltb_ge in H
  | H: context [Int64.unsigned (Int64.repr ?a)] |- _ =>
      rewrite (Int64.unsigned_repr a) in H by (let U := fresh in assert (U: u64_ok a) by u64; exact U)
  | H: context [Int.unsigned (Int.repr ?a)] |- _ => rewrite (Int.unsigned_repr a) in H by rep_lia
  | H: context [Int.signed (Int.repr 8)] |- _ => change (Int.signed (Int.repr 8)) with 8 in H
  | H: context [Int64.add (Int64.repr ?a) (Int64.repr ?b)] |- _ => rewrite add64_repr in H
  end.

Ltac post_split := repeat match goal with |- _ /\ _ => split end.

(* terminal = (offset + 8 == total), as the C computes it, offset = 8k. *)
Lemma terminal_val: forall T k, 0 <= 8 * k -> 8 * k + 8 <= Int64.max_unsigned -> u32_ok T ->
  Vlong (Int64.repr (Int.signed (Int.repr (Z.b2z (Int64.cmpu Ceq
    (Int64.add (Int64.repr (8 * k)) (Int64.repr (Int.signed (Int.repr 8))))
    (Int64.repr (Int.unsigned (Int.repr T)))))))) = vl (terminal T k).
Proof.
  intros. unfold u32_ok in *. change (Int.signed (Int.repr 8)) with 8.
  rewrite add64_repr, Int.unsigned_repr by lia. cbn [Int64.cmpu].
  rewrite eq64_repr by (unfold u64_ok; rep_lia). unfold terminal, vl.
  destruct (8 * k + 8 =? T); reflexivity.
Qed.

Lemma terminal_range: forall T k, 0 <= terminal T k <= 1.
Proof. intros. unfold terminal. destruct (_ =? _); lia. Qed.

(* The carried state as the C copies answer[0..6] over it, word w at a time. *)
Lemma carry_step: forall (a st: list Z) w, 7 <= Zlength a -> Zlength st = 7 -> 0 <= w < 7 ->
  upd_Znth w (map vl (sublist 0 w a ++ sublist w 7 st)) (vl (Znth w a)) =
  map vl (sublist 0 (w + 1) a ++ sublist (w + 1) 7 st).
Proof.
  intros. rewrite upd_Znth_map. f_equal.
  rewrite upd_Znth_app2 by (rewrite !Zlength_sublist by lia; lia).
  rewrite Zlength_sublist by lia. replace (w - (w - 0)) with 0 by lia.
  rewrite (sublist_split 0 w (w + 1) a) by lia. rewrite sublist_len_1 by lia.
  rewrite <- app_assoc. f_equal. cbn [app].
  rewrite (sublist_split w (w + 1) 7 st) by lia. rewrite sublist_len_1 by lia. cbn [app].
  rewrite upd_Znth0. reflexivity.
Qed.

Lemma carry_end: forall (a st: list Z), Zlength st = 7 -> sublist 0 7 a ++ sublist 7 7 st = sublist 0 7 a.
Proof. intros. rewrite sublist_nil. apply app_nil_r. Qed.

Lemma carry_start: forall (st: list Z), Zlength st = 7 -> sublist 0 0 (@nil Z) ++ sublist 0 7 st = st.
Proof. intros. rewrite sublist_nil. cbn [app]. rewrite sublist_same by lia. reflexivity. Qed.

Lemma next8: forall k T, 8 * k < T -> T mod 8 = 0 -> 8 * (k + 1) <= T.
Proof.
  intros. pose proof (Z.div_mod T 8 ltac:(lia)) as D. rewrite H0 in D.
  set (q := T / 8) in *. lia.
Qed.

Lemma last8: forall k T, ~ 8 * k < T -> 8 * k <= T -> 8 * k = T.
Proof. intros. lia. Qed.
