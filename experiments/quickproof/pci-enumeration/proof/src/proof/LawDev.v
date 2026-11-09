(* Law enumeration_exact: the law's device answer by answer (Dev_exact of h ++ [a] from the state after h), and
   seen[] as the device updates it. *)
Require Import VST.floyd.proofauto.
Require Import LeanosEnum.harness.enumeration_exact.code.
Require Import LeanosEnum.proof.Defs.
Require LeanosEnum.proof.EnumSpecs.
Require Import LeanosEnum.proof.LawProg LeanosEnum.proof.LawRun LeanosEnum.proof.LawSpecs.
Local Open Scope Z_scope.

Lemma Dev_go: forall ctx h next w fs, run start h = Some (Go (next, w, fs)) ->
  Dev_exact ctx h = dev_at ctx next w (Zlength fs) 0 0 (Zlength h) (last_loc h) fs.
Proof. intros. unfold Dev_exact. rewrite H. reflexivity. Qed.

Lemma last_loc_snoc: forall h i o ok v, last_loc (h ++ [(i, o, ok, v)]) = loc_of i o.
Proof. intros. unfold last_loc. rewrite rev_app_distr. reflexivity. Qed.

Lemma removelast_snoc {A: Type}: forall (h: list A) a, removelast (h ++ [a]) = h.
Proof. intros. rewrite removelast_app by discriminate. simpl. apply app_nil_r. Qed.

(* One more answer, after which the scan reads again (or has read every identity). *)
Lemma Dev_snoc_go: forall ctx h a s n' w' fs',
  run start h = Some (Go s) -> live s = true -> answers (request s) a = true -> step s a = Go (n', w', fs') ->
  Dev_exact ctx (h ++ [a]) = dev_at ctx n' w' (Zlength fs') 0 0 (Zlength h + 1) (last_loc (h ++ [a])) fs'.
Proof.
  intros ctx h a s n' w' fs' R L A S. unfold Dev_exact. rewrite run_snoc, R, L, A, S. simpl andb.
  rewrite Zlength_app, Zlength_cons, Zlength_nil. reflexivity.
Qed.

(* One more answer, at which the scan returns. *)
Lemma Dev_snoc_stop: forall ctx h a next w fs st i o,
  run start h = Some (Go (next, w, fs)) -> live (next, w, fs) = true -> answers (request (next, w, fs)) a = true ->
  step (next, w, fs) a = Stop st i o ->
  Dev_exact ctx (h ++ [a]) =
  if st =? S_READ_FAILED then dev_at ctx next w (Zlength fs) 1 1 (Zlength h + 1) (last_loc (h ++ [a])) fs
  else dev_at ctx (next + 1) 0 (CAPACITY + 1) 1 0 (Zlength h + 1) (last_loc (h ++ [a])) fs.
Proof.
  intros ctx h a next w fs st i o R L A S. unfold Dev_exact. rewrite run_snoc, R, L, A, S. simpl andb.
  rewrite removelast_snoc, R.
  rewrite Zlength_app, Zlength_cons, Zlength_nil. reflexivity.
Qed.

Lemma answers_req: forall s i o ok v, request s = (i, o) -> answers (request s) (i, o, ok, v) = true.
Proof. intros. rewrite H. unfold answers. simpl. rewrite !Z.eqb_refl. reflexivity. Qed.

(* The step of one answer, by case. *)
Lemma step_fail: forall s i o v, step s (i, o, false, v) = Stop S_READ_FAILED i o.
Proof. intros [[next w] fs] i o v. reflexivity. Qed.

Lemma step_none: forall next fs i o v, Z.land v 65535 = 65535 ->
  step (next, 0, fs) (i, o, true, v) = Go (next + 1, 0, fs).
Proof. intros. unfold step. simpl negb. cbv iota. rewrite H. reflexivity. Qed.

Lemma step_found: forall next (fs: list found) i o v, Z.land v 65535 <> 65535 -> Zlength fs <> CAPACITY ->
  step (next, 0, fs) (i, o, true, v) = Go (next + 1, 1, (i, [v]) :: fs).
Proof.
  intros. unfold step. simpl negb. cbv iota.
  rewrite (proj2 (Z.eqb_neq _ _) H), (proj2 (Z.eqb_neq _ _) H0). reflexivity.
Qed.

Lemma step_cap: forall next (fs: list found) i o v, Z.land v 65535 <> 65535 -> Zlength fs = CAPACITY ->
  step (next, 0, fs) (i, o, true, v) = Stop S_CAPACITY_EXCEEDED i 0.
Proof.
  intros. unfold step. simpl negb. cbv iota.
  rewrite (proj2 (Z.eqb_neq _ _) H), H0, Z.eqb_refl. reflexivity.
Qed.

Lemma step_word: forall next w fs i o v, w <> 0 ->
  step (next, w, fs) (i, o, true, v) = Go (next, if w =? 15 then 0 else w + 1, add_word v fs).
Proof. intros. unfold step. simpl negb. cbv iota. rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity. Qed.

Lemma vendor_iff: forall v, 0 <= v <= Int.max_unsigned ->
  (Int.and (Int.repr v) (Int.repr 65535) = Int.repr 65535 <-> Z.land v 65535 = 65535).
Proof.
  intros v Hv. rewrite and_repr.
  pose proof (land_ones_range v 16 ltac:(lia)) as R. change (Z.ones 16) with 65535 in R.
  change (2 ^ 16) with 65536 in R.
  split; intro E.
  - apply repr_inj_unsigned in E; rep_lia.
  - rewrite E. reflexivity.
Qed.

Lemma add_word_len: forall v (fs: list found), Zlength (add_word v fs) = Zlength fs.
Proof. intros v [ | [i ws] rest ]; [ reflexivity | simpl; rewrite !Zlength_cons; reflexivity ]. Qed.
