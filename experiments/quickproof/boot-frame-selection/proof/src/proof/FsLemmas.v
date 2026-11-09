(* Pure lemmas for the body proofs of include/boot_frame_selection.h (Fs*.v): 32- and 64-bit words and their C
   comparisons (project 8's HdLemmas.v, the part this header needs), the facts inputs_ok gives, and the rows of
   the two decoder states as states[k] evaluates them. *)
Require Import VST.floyd.proofauto.
Require Import LeanosFrameSelection.frame.code.
Require Import LeanosFrameSelection.proof.Defs.
Require Import LeanosFrameSelection.proof.FrameSpecs.
#[local] Existing Instance FrameSpecs.CS.
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

Lemma Forall_u64_Znth: forall a j, Forall u64_ok a -> 0 <= j < Zlength a -> u64_ok (Znth j a).
Proof. intros. apply (proj1 (Forall_Znth a u64_ok) H j H0). Qed.

(* S + 1 in uint64_t. *)
Lemma add64_one: forall a, Int64.add (Int64.repr a) (Int64.repr 1) = Int64.repr ((a + 1) mod 2 ^ 64).
Proof.
  intros. rewrite add64_repr. rewrite <- (Int64.repr_unsigned (Int64.repr (a + 1))), Int64.unsigned_repr_eq.
  reflexivity.
Qed.

Lemma u64_mod: forall a, u64_ok (a mod 2 ^ 64).
Proof. intros. unfold u64_ok. pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)). rep_lia. Qed.

Ltac u64 :=
  first [ assumption | apply u64_mod | apply Forall_u64_Znth; [ assumption | lia ] | apply u32_u64; assumption
        | unfold u64_ok; rep_lia ].

(* The C's comparisons of 64-bit words, as hypotheses about the words. *)
Ltac w64 :=
  repeat match goal with
  | H: context [Int64.zero] |- _ => change Int64.zero with (Int64.repr 0) in H
  | H: context [Int64.one] |- _ => change Int64.one with (Int64.repr 1) in H
  | H: context [Int.zero] |- _ => change Int.zero with (Int.repr 0) in H
  | H: context [Int.one] |- _ => change Int.one with (Int.repr 1) in H
  | H: context [Int64.add (Int64.repr ?a) (Int64.repr 1)] |- _ => rewrite add64_one in H
  | H: negb ?b = true |- _ => apply negb_true_iff in H
  | H: negb ?b = false |- _ => apply negb_false_iff in H
  | H: Int64.repr ?a <> Int64.repr ?b |- _ => apply repr64_neq in H
  | H: Int64.repr ?a = Int64.repr ?b |- _ => apply repr64_inj in H; [ | u64 | u64 ]
  | H: Int.repr ?a <> Int.repr ?b |- _ => apply repr32_neq in H
  | H: Int.repr ?a = Int.repr ?b |- _ => apply repr32_inj in H; [ | unfold u32_ok in *; rep_lia | unfold u32_ok in *; rep_lia ]
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
  | H: context [Int.unsigned (Int.repr ?a)] |- _ => rewrite (Int.unsigned_repr a) in H by (unfold u32_ok in *; rep_lia)
  end.

(* Decide the comparisons of a check from the hypotheses, one at a time (any occurrence lia decides). *)
Ltac zb1 :=
  match goal with
  | |- context [?a =? ?b] =>
      first [ rewrite (proj2 (Z.eqb_eq a b)) by lia | rewrite (proj2 (Z.eqb_neq a b)) by lia ]
  | |- context [?a <? ?b] =>
      first [ rewrite (proj2 (Z.ltb_lt a b)) by lia | rewrite (proj2 (Z.ltb_ge a b)) by lia ]
  | |- context [?a <=? ?b] =>
      first [ rewrite (proj2 (Z.leb_le a b)) by lia | rewrite (proj2 (Z.leb_gt a b)) by lia ]
  end.
Ltac zb := repeat (zb1; cbn [negb orb andb]).

Ltac zb1_in H :=
  match type of H with
  | context [?a =? ?b] =>
      first [ rewrite (proj2 (Z.eqb_eq a b)) in H by lia | rewrite (proj2 (Z.eqb_neq a b)) in H by lia ]
  | context [?a <? ?b] =>
      first [ rewrite (proj2 (Z.ltb_lt a b)) in H by lia | rewrite (proj2 (Z.ltb_ge a b)) in H by lia ]
  | context [?a <=? ?b] =>
      first [ rewrite (proj2 (Z.leb_le a b)) in H by lia | rewrite (proj2 (Z.leb_gt a b)) in H by lia ]
  end.
Ltac zb_in H := repeat (zb1_in H; cbn [negb orb andb] in H).

(* Two distinct status constants differ. *)
Ltac sne := let E := fresh in intro E; vm_compute in E; discriminate.

Ltac post_split := repeat match goal with |- _ /\ _ => split end.

(* ---------- the inputs ---------- *)

(* What inputs_ok gives the bodies: the read-only objects' and the memory's lengths and words. *)
Lemma inputs_facts (x: inputs) : inputs_ok x ->
  u32_ok (i_take_next x) /\ u64_ok (i_selected x) /\ u64_ok (i_selected_manifest x) /\
  u64_ok (i_published x) /\ u64_ok (i_next x) /\
  Zlength (i_manifest x) = MANIFEST_WORDS /\ Forall u64_ok (i_manifest x) /\
  Zlength (i_decoded x) = WORDS /\ Forall u64_ok (i_decoded x) /\
  Zlength (i_usable x) = BLOCKS /\ Forall u64_ok (i_usable x) /\
  Zlength (i_blocked x) = BLOCKS /\ Forall u64_ok (i_blocked x) /\ mem_ok (i_mem x).
Proof. intros I. exact I. Qed.

Lemma mem_state (m: mem) (k: Z) : mem_ok m -> 0 <= k < 2 ->
  Zlength (Znth k (m_states m)) = WORDS /\ Forall u64_ok (Znth k (m_states m)).
Proof.
  intros (_ & _ & _ & _ & L & F & _) K.
  apply (proj1 (Forall_Znth (m_states m) _) F k). lia.
Qed.

(* The returns of a step that makes no call. *)
Lemma returns_nil (x: inputs) (st: Z) (m: mem) : start x = Return st m -> returns x nil = Some (st, m).
Proof. intros E. unfold returns. cbn [run]. rewrite E. reflexivity. Qed.

(* ---------- the rows of the states ---------- *)

Lemma row_ptr0 (sp: val) : isptr sp -> row_ptr sp 0 = sp.
Proof. intros. unfold row_ptr. rewrite Z.mul_0_r. apply isptr_offset_val_zero; auto. Qed.

(* states[k], as the C computes it for a uint32_t k. *)
Lemma row_add (sp: val) (k: Z) : isptr sp -> 0 <= k <= 1 ->
  force_val (sem_add_ptr_int (tarray tulong 41) Unsigned sp (Vint (Int.repr k))) = row_ptr sp k.
Proof.
  intros. unfold row_ptr, STATE_BYTES.
  rewrite sem_add_pi_ptr_special; [ reflexivity | reflexivity | auto | rep_lia ].
Qed.

(* State k of the memory after the decoder wrote ws to it. *)
Lemma Znth_with_state (m: mem) (k: Z) (ws: list Z) :
  Zlength (m_states m) = 2 -> 0 <= k < 2 -> Znth k (m_states (with_state m k ws)) = ws.
Proof. intros. unfold with_state, with_states. cbn [m_states]. apply upd_Znth_same. lia. Qed.

Lemma Znth_with_state_other (m: mem) (k j: Z) (ws: list Z) :
  Zlength (m_states m) = 2 -> 0 <= k < 2 -> 0 <= j < 2 -> j <> k ->
  Znth j (m_states (with_state m k ws)) = Znth j (m_states m).
Proof. intros. unfold with_state, with_states. cbn [m_states]. apply upd_Znth_diff; lia. Qed.

Lemma Zlength_with_state (m: mem) (k: Z) (ws: list Z) :
  Zlength (m_states (with_state m k ws)) = Zlength (m_states m).
Proof. unfold with_state, with_states. cbn [m_states]. apply Zlength_upd_Znth'. Qed.

(* An array of five words, written word by word from the front. *)
Lemma upd_five (r: list val) (a b c d e: val) : Zlength r = 5 ->
  upd_Znth 4 (upd_Znth 3 (upd_Znth 2 (upd_Znth 1 (upd_Znth 0 r a) b) c) d) e = [a; b; c; d; e].
Proof.
  intros L. destruct r as [| r0 [| r1 [| r2 [| r3 [| r4 [| r5 rs]]]]]];
    try (rewrite ?Zlength_cons, ?Zlength_nil in L; rep_lia).
  reflexivity.
Qed.

Lemma with_publication_same (m: mem) : with_publication m (m_publication m) = m.
Proof. destruct m; reflexivity. Qed.
