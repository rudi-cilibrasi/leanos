(* Lemmas about the memory of the snapshot for ScanProof.v: its split at the header being written, the address of
   that header as the C computes it, and the dwords of a header being read. *)
Require Import VST.floyd.proofauto.
Require Import LeanosEnum.enum.code.
Require Import LeanosEnum.proof.Defs.
Require Import LeanosEnum.proof.EnumSpecs.
#[local] Existing Instance EnumSpecs.CS.
Local Open Scope Z_scope.

(* ---------- the snapshot ---------- *)

(* The address of headers[k] of the snapshot at p. *)
Definition hdr_ptr (p: val) (k: Z) : val :=
  field_address0 (tarray t_header 16) [ArraySubsc k] (field_address t_snapshot [StructField _headers] p).

Lemma snap_split: forall sh c (hs: list (reptype t_header)) p k, 0 <= k < 16 -> Zlength hs = 16 ->
  data_at sh t_snapshot (snapshot_val c hs) p =
  (field_at sh t_snapshot [StructField _count] (Vint (Int.repr c)) p *
   data_at sh (tarray t_header k) (sublist 0 k hs) (field_address t_snapshot [StructField _headers] p) *
   data_at sh t_header (Znth k hs) (hdr_ptr p k) *
   data_at sh (tarray t_header (16 - (k + 1))) (sublist (k + 1) 16 hs) (hdr_ptr p (k + 1)))%logic.
Proof.
  intros. unfold snapshot_val.
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at sh t_snapshot [StructField _headers]).
  change (nested_field_type t_snapshot [StructField _headers]) with (tarray t_header 16).
  unfold hdr_ptr, tarray.
  erewrite (split3_data_at_Tarray sh t_header 16 k (k + 1) hs hs); try reflexivity; try lia.
  2: { simpl. auto. }
  2: { rewrite sublist_same by lia. reflexivity. }
  replace (k + 1 - k) with 1 by lia.
  rewrite (data_at_singleton_array_eq sh t_header (Znth k hs)) by (rewrite sublist_len_1 by lia; reflexivity).
  rewrite !sepcon_assoc. reflexivity.
Qed.

Lemma snap_join: forall sh c (hs: list (reptype t_header)) p k (hv: reptype t_header),
  0 <= k < 16 -> Zlength hs = 16 ->
  (field_at sh t_snapshot [StructField _count] (Vint (Int.repr c)) p *
   data_at sh (tarray t_header k) (sublist 0 k hs) (field_address t_snapshot [StructField _headers] p) *
   data_at sh t_header hv (hdr_ptr p k) *
   data_at sh (tarray t_header (16 - (k + 1))) (sublist (k + 1) 16 hs) (hdr_ptr p (k + 1)))%logic
  = data_at sh t_snapshot (snapshot_val c (upd_Znth k hs hv)) p.
Proof.
  intros. rewrite (snap_split sh c (upd_Znth k hs hv) p k) by (try list_solve; lia).
  rewrite upd_Znth_same by lia.
  rewrite sublist_upd_Znth_l by lia. rewrite sublist_upd_Znth_r by lia. reflexivity.
Qed.

Lemma hdr_fc: forall p k, field_compatible t_snapshot [] p -> 0 <= k <= 16 ->
  field_compatible0 (tarray t_header 16) [ArraySubsc k] (field_address t_snapshot [StructField _headers] p).
Proof.
  intros.
  assert (F1: field_compatible t_snapshot [StructField _headers] p).
  { apply field_compatible_cons. simpl. split; [ unfold in_members; simpl; auto | auto ]. }
  pose proof (field_compatible_nested_field _ _ _ F1) as F2.
  rewrite field_address_offset by auto.
  change (nested_field_type t_snapshot [StructField _headers]) with (tarray t_header 16) in F2.
  apply field_compatible0_cons. split; [ simpl; lia | exact F2 ].
Qed.
Lemma header_addr: forall p k, field_compatible t_snapshot [] p -> 0 <= k < 16 ->
  force_val (sem_binary_operation' Oadd (tarray (Tstruct _pci_enumeration_header noattr) 16) tuint
    (eval_field (Tstruct _pci_enumeration_snapshot noattr) _headers p) (Vint (Int.repr k))) = hdr_ptr p k.
Proof.
  intros. unfold hdr_ptr. rewrite field_address0_offset by (apply hdr_fc; auto; lia).
  rewrite field_address_offset by (apply field_compatible_cons; simpl; split; [ unfold in_members; simpl; auto | auto ]).
  destruct H as [Hp _]. destruct p; try contradiction.
  unfold sem_binary_operation', eval_field. simpl.
  f_equal. f_equal. rewrite Z.add_0_l. unfold Ptrofs.of_intu, Ptrofs.of_int. rewrite Int.unsigned_repr by rep_lia.
  rewrite ptrofs_mul_repr. reflexivity.
Qed.

(* The words of a header being read: the dwords ws read so far, then the uninitialized rest. *)
Definition wvals (ws: list Z) : list val := map (fun x => Vint (Int.repr x)) ws ++ Zrepeat Vundef (WORDS - Zlength ws).

Lemma wvals_upd: forall ws x, Zlength ws < WORDS ->
  upd_Znth (Zlength ws) (wvals ws) (Vint (Int.repr x)) = wvals (ws ++ [x]).
Proof.
  intros. unfold wvals, WORDS in *. pose proof (Zlength_nonneg ws).
  rewrite upd_Znth_app2 by (rewrite Zlength_map, Zlength_Zrepeat by lia; lia).
  rewrite Zlength_map, Z.sub_diag. rewrite Zlength_app, Zlength_cons, Zlength_nil.
  replace (16 - Zlength ws) with (1 + (16 - (Zlength ws + 1))) by lia.
  rewrite <- Zrepeat_app by lia. rewrite upd_Znth_app1 by (rewrite Zlength_Zrepeat; lia).
  rewrite map_app, <- app_assoc. f_equal.
Qed.

Lemma wvals_full: forall ws, Zlength ws = WORDS -> wvals ws = map (fun x => Vint (Int.repr x)) ws.
Proof. intros. unfold wvals. rewrite H, Z.sub_diag. simpl. apply app_nil_r. Qed.


Lemma value_fits_snapshot: forall v, value_fits t_snapshot v -> Zlength (snd v) = 16.
Proof.
  intros v H. rewrite value_fits_eq in H. simpl in H. destruct H as [_ H].
  rewrite value_fits_eq in H. simpl in H. destruct H as [H _]. rewrite ?Z.max_r in H by lia. exact H.
Qed.

(* ---------- the headers of the snapshot ---------- *)

(* hs, the snapshot's 16 headers, publishes the headers found fs (latest first) in its first |fs| entries. *)
Definition pub_ok (fs: list found) (hs: list (reptype t_header)) : Prop :=
  Zlength hs = 16 /\ Zlength fs <= 16 /\ sublist 0 (Zlength fs) hs = map header_val (rev fs).

Lemma pub_ok_nil: forall hs, Zlength hs = 16 -> pub_ok nil hs.
Proof. intros. split; [ auto | split; [ rewrite Zlength_nil; lia | reflexivity ] ]. Qed.

Lemma pub_ok_cons: forall fs hs f, pub_ok fs hs -> Zlength fs < 16 ->
  pub_ok (f :: fs) (upd_Znth (Zlength fs) hs (header_val f)).
Proof.
  intros fs hs f [L [L2 E]] Lt. pose proof (Zlength_nonneg fs).
  split; [ rewrite Zlength_upd_Znth; auto | ].
  rewrite Zlength_cons. split; [ lia | ].
  rewrite (sublist_split 0 (Zlength fs) (Z.succ (Zlength fs))) by (try rewrite Zlength_upd_Znth; lia).
  rewrite sublist_upd_Znth_l by lia. rewrite E.
  rewrite (sublist_len_1 (Zlength fs)) by (rewrite Zlength_upd_Znth; lia).
  rewrite upd_Znth_same by lia. simpl rev. rewrite map_app. reflexivity.
Qed.

Lemma pub_ok_split: forall fs hs, pub_ok fs hs ->
  hs = map header_val (rev fs) ++ sublist (Zlength fs) 16 hs.
Proof.
  intros fs hs [L [L2 E]]. pose proof (Zlength_nonneg fs). rewrite <- E.
  rewrite <- sublist_split by lia. rewrite sublist_same by lia. reflexivity.
Qed.

(* The header of function n while its dwords are read: its location and the dwords ws read so far. *)
Definition stage (n: Z) (ws: list Z) : reptype t_header :=
  (Vint (Int.repr (bus_of n)), (Vint (Int.repr (dev_of n)), (Vint (Int.repr (fn_of n)), wvals ws))).

Lemma stage_full: forall n ws, Zlength ws = WORDS -> stage n ws = header_val (n, ws).
Proof. intros. unfold stage, header_val. rewrite wvals_full by auto. reflexivity. Qed.
