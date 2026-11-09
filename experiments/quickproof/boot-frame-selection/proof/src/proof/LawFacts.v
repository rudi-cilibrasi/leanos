(* Law frame_selection_exact: the model's run as the law's callees see it: which stage each call comes from (its
   arguments as the model's), what every point of a run gives (Defs.run_ok), and the arithmetic of the words. *)
Require Import VST.floyd.proofauto.
Require Import LeanosFrameSelection.proof.Defs.
Require Import LeanosFrameSelection.proof.FrameSpecs.
Require Import LeanosFrameSelection.proof.LawProg LeanosFrameSelection.proof.LawDefs.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Ltac split_and := repeat match goal with |- _ /\ _ => split end.

(* ---------------------------------------------------------------------- *)
(* The run                                                                 *)
(* ---------------------------------------------------------------------- *)

Lemma next_go: forall x h p c, run x (start x) h = Some p -> next_call x h = Some c ->
  exists g m, p = Go g m /\ c = expected x g m.
Proof.
  intros x h p c R N. destruct (next_call_run x h c N) as (g & m & R' & E).
  rewrite R in R'. inversion R'; subst. eauto.
Qed.

Lemma returns_eq: forall x h p st m, run x (start x) h = Some p -> returns x h = Some (st, m) -> p = Return st m.
Proof.
  intros x h p st m R E. apply returns_run in E. rewrite R in E. inversion E; reflexivity.
Qed.

Lemma progress_of_run: forall x h p, inputs_ok x -> answers_ok h -> run x (start x) h = Some p -> progress_ok x p.
Proof. intros x h p I A R. exact (run_ok x (start x) p h I (start_ok x I) A R). Qed.

Lemma answers_ok_snoc: forall h c r, answers_ok h -> reply_ok c r -> answers_ok (h ++ [(c, r)]).
Proof. intros. unfold answers_ok in *. apply Forall_app. split; auto. Qed.

Lemma run_word': forall x h g m v, run x (start x) h = Some (Go g m) ->
  (forall c k, expected x g m <> Decode c k) ->
  run x (start x) (h ++ [(expected x g m, Word v)]) = Some (step x g m (Word v)).
Proof. intros. apply run_word; auto. Qed.

Lemma mem_of_start: forall x, mem_of (start x) = i_mem x.
Proof.
  intros x. unfold start. destruct (i_step x); try reflexivity.
  destruct (rescan_order x =? S_OK); reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* The calls                                                               *)
(* ---------------------------------------------------------------------- *)

Lemma call_scrub: forall x g m f, expected x g m = Scrub f -> g = ExpectScrub /\ f = i_selected x.
Proof. intros x g m f E. destruct g; simpl in E; inversion E; subst; auto. Qed.

Lemma call_decode: forall x g m c k, expected x g m = Decode c k ->
  (exists f fm, g = ExpectDecode c k f fm) \/ (g = ExpectRescanDecode /\ c = i_next x /\ k = 1).
Proof. intros x g m c k E. destruct g; simpl in E; inversion E; subst; eauto. Qed.

Lemma call_manifest: forall x g m b ms q, expected x g m = Manifest b ms q ->
  exists ms' me fw a, g = ExpectManifest b ms' me fw a /\ ms = i_manifest x /\ q = Zlength a + 1.
Proof. intros x g m b ms q E. destruct g; simpl in E; inversion E; subst; eauto 8. Qed.

Lemma call_free: forall x g m u bl r, expected x g m = Free u bl r ->
  exists b ms me fw, g = ExpectFree b ms me fw /\ u = Znth b (i_usable x) /\ bl = Znth b (i_blocked x) /\
    r = Znth b (m_reserved m).
Proof. intros x g m u bl r E. destruct g; simpl in E; inversion E; subst; eauto 8. Qed.

Lemma call_finish: forall x g m ds de ms me cnt hi own q fw, expected x g m = Finish ds de ms me cnt hi own q fw ->
  g = ExpectFinish q ms me fw /\ ds = Znth 1 (i_decoded x) /\ de = Znth 2 (i_decoded x) /\
  cnt = Znth 11 (i_decoded x) /\ hi = Znth 17 (i_decoded x) /\ own = 1.
Proof. intros. destruct g; simpl in H; inversion H; subst; auto 8. Qed.

Lemma call_candidate: forall x g m f ms, expected x g m = Candidate f ms ->
  ((exists k f' fm, g = ExpectCandidate f k f' fm) \/ (g = ExpectRescanCandidate /\ f = i_next x)) /\
  ms = i_manifest x.
Proof. intros x g m f ms E. destruct g; simpl in E; inversion E; subst; eauto 8. Qed.

Lemma call_consume: forall x g m cur c ds u bl cm, expected x g m = Consume cur c ds u bl cm ->
  exists k f fm, g = ExpectConsume c k f fm cm /\ cur = FRAMES /\ ds = Znth 1 (Znth k (m_states m)) /\
    u = Znth 14 (Znth k (m_states m)) /\ bl = Znth 15 (Znth k (m_states m)).
Proof. intros. destruct g; simpl in H; inversion H; subst; eauto 10. Qed.

Lemma call_authority: forall x g m s t ds u bl sm sc q, expected x g m = Authority s t ds u bl sm sc q ->
  g = ExpectAuthority q /\ s = i_selected x /\ t = Znth 16 (Znth 0 (m_states m)) /\
  ds = Znth 1 (Znth 0 (m_states m)) /\ u = Znth 14 (Znth 0 (m_states m)) /\
  bl = Znth 15 (Znth 0 (m_states m)) /\ sm = i_selected_manifest x /\ sc = 1.
Proof. intros. destruct g; simpl in H; inversion H; subst; auto 10. Qed.

(* ---------------------------------------------------------------------- *)
(* Lists and ranges                                                        *)
(* ---------------------------------------------------------------------- *)

Lemma Forall_u64_Znth: forall l i, Forall u64_ok l -> 0 <= i < Zlength l -> u64_ok (Znth i l).
Proof. intros l i F I. exact (proj1 (Forall_Znth _ _) F i I). Qed.

Lemma Forall_upd: forall (P: Z -> Prop) l i x, Forall P l -> P x -> Forall P (upd_Znth i l x).
Proof.
  intros P l i x F Px. destruct (zlt i 0); [ rewrite upd_Znth_out_of_range by lia; auto | ].
  destruct (zlt i (Zlength l)); [ | rewrite upd_Znth_out_of_range by lia; auto ].
  apply Forall_Znth. intros j Hj. rewrite upd_Znth_Zlength in Hj by lia.
  destruct (Z.eq_dec j i) as [-> | N]; [ rewrite upd_Znth_same by lia; auto | ].
  rewrite upd_Znth_diff by lia. apply Forall_Znth; auto.
Qed.

Lemma Forall_u64_app1: forall l v, Forall u64_ok l -> u64_ok v -> Forall u64_ok (l ++ [v]).
Proof. intros. apply Forall_app; split; auto. Qed.

(* The memory of the model: its words. *)
Lemma mem_ok_states: forall m, mem_ok m -> Zlength (m_states m) = 2 /\
  Zlength (Znth 0 (m_states m)) = WORDS /\ Forall u64_ok (Znth 0 (m_states m)) /\
  Zlength (Znth 1 (m_states m)) = WORDS /\ Forall u64_ok (Znth 1 (m_states m)).
Proof.
  intros m (_ & _ & _ & _ & L & F & _).
  destruct (Forall_Znth' _ (m_states m) 0 F ltac:(lia)) as [L0 F0].
  destruct (Forall_Znth' _ (m_states m) 1 F ltac:(lia)) as [L1 F1].
  auto 6.
Qed.

(* ---------------------------------------------------------------------- *)
(* Words                                                                   *)
(* ---------------------------------------------------------------------- *)

Lemma Int64_eq_repr: forall a b, 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.eq (Int64.repr a) (Int64.repr b) = (a =? b).
Proof.
  intros a b Ha Hb. unfold Int64.eq. rewrite !Int64.unsigned_repr by auto.
  destruct (zeq a b); destruct (Z.eqb_spec a b); auto; lia.
Qed.

Lemma Int64_ltu_repr: forall a b, 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr a) (Int64.repr b) = (a <? b).
Proof.
  intros a b Ha Hb. unfold Int64.ltu. rewrite !Int64.unsigned_repr by auto.
  destruct (zlt a b); destruct (Z.ltb_spec a b); auto; lia.
Qed.

Lemma Int_eq_repr: forall a b, 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Int.eq (Int.repr a) (Int.repr b) = (a =? b).
Proof.
  intros a b Ha Hb. unfold Int.eq. rewrite !Int.unsigned_repr by auto.
  destruct (zeq a b); destruct (Z.eqb_spec a b); auto; lia.
Qed.

Lemma Int_ltu_repr: forall a b, 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Int.ltu (Int.repr a) (Int.repr b) = (a <? b).
Proof.
  intros a b Ha Hb. unfold Int.ltu. rewrite !Int.unsigned_repr by auto.
  destruct (zlt a b); destruct (Z.ltb_spec a b); auto; lia.
Qed.

Lemma add64_repr': forall a b, Int64.add (Int64.repr a) (Int64.repr b) = Int64.repr (a + b).
Proof.
  intros. unfold Int64.add. apply Int64.eqm_samerepr. apply Int64.eqm_add; apply Int64.eqm_sym, Int64.eqm_unsigned_repr.
Qed.

Lemma add_repr': forall a b, Int.add (Int.repr a) (Int.repr b) = Int.repr (a + b).
Proof.
  intros. unfold Int.add. apply Int.eqm_samerepr. apply Int.eqm_add; apply Int.eqm_sym, Int.eqm_unsigned_repr.
Qed.

Lemma repr64_inj: forall a b, 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.repr a = Int64.repr b -> a = b.
Proof.
  intros a b Ha Hb E. apply (f_equal Int64.unsigned) in E. rewrite !Int64.unsigned_repr in E by auto. exact E.
Qed.

Lemma repr64_neq: forall a b, Int64.repr a <> Int64.repr b -> a <> b.
Proof. intros a b N E. subst. apply N. reflexivity. Qed.

Lemma repr_neq_e: forall a b, Int.repr a <> Int.repr b -> a <> b.
Proof. intros a b N E. subst. apply N. reflexivity. Qed.

(* (uint32_t) of a 64-bit word: its low 32 bits. *)
Lemma low32_range: forall v, 0 <= v mod 2 ^ 32 <= Int.max_unsigned.
Proof. intros. pose proof (Z.mod_pos_bound v (2 ^ 32) ltac:(lia)). unfold Int.max_unsigned, Int.modulus; simpl. lia. Qed.

Lemma low32: forall v, Int.repr v = Int.repr (v mod 2 ^ 32).
Proof.
  intros. rewrite <- (Int.repr_unsigned (Int.repr v)). rewrite Int.unsigned_repr_eq. reflexivity.
Qed.

Lemma statuses_u32: forall st, status_ok st -> u32_ok st.
Proof. intros st H. unfold status_ok, S_RESCAN_MANIFEST in H. unfold u32_ok. rep_lia. Qed.
