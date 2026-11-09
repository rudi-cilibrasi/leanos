(* Law consumer_obligations: what main's proof needs besides the harness's functions: the consumer's argument
   types between the unit's compspecs and the law's, the arguments that may be NULL, the global oracle as main
   finds it (all zeros), and the law's oracle at the call. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosMadt.harness.consumer_obligations.code.
Require Import LeanosMadt.proof.Defs.
Require Import LeanosMadt.proof.MadtSpecs.
Require Import LeanosMadt.proof.LawProg LeanosMadt.proof.LawDefs LeanosMadt.proof.LawFacts LeanosMadt.proof.LawLib
  LeanosMadt.proof.LawSplit.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

(* ---------------------------------------------------------------------- *)
(* The consumer's argument types, at the unit's compspecs                  *)
(* ---------------------------------------------------------------------- *)

Lemma obs_cs: forall sh (v: val * (val * (val * (val * (val * val))))) p,
  @data_at LCS sh t_obs v p = @data_at MadtSpecs.CS sh t_obs v p.
Proof.
  intros. apply equal_f. symmetry.
  apply (@data_at_change_composite MadtSpecs.CS LCS LCR); [ apply JMeq_refl | reflexivity ].
Qed.

Lemma result_cs: forall sh (v: val * (val * (val * (val * (val * val))))) p,
  @data_at LCS sh t_result v p = @data_at MadtSpecs.CS sh t_result v p.
Proof.
  intros. apply equal_f. symmetry.
  apply (@data_at_change_composite MadtSpecs.CS LCS LCR); [ apply JMeq_refl | reflexivity ].
Qed.

Lemma result__cs: forall sh p, @data_at_ LCS sh t_result p = @data_at_ MadtSpecs.CS sh t_result p.
Proof.
  intros. apply equal_f. symmetry. apply (@data_at__change_composite MadtSpecs.CS LCS LCR). reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* The arguments that may be NULL                                          *)
(* ---------------------------------------------------------------------- *)

Definition sel (b: bool) (p: val) : val := if b then nullval else p.

Lemma sel_isnull: forall b p, isptr p -> isnull (sel b p) = b.
Proof.
  intros [ | ] p P; unfold sel, isnull; [ rewrite if_true by reflexivity; reflexivity | ].
  rewrite if_false; [ reflexivity | destruct p; try contradiction; discriminate ].
Qed.

Lemma sel_ptr: forall b p, isptr p -> is_pointer_or_null (sel b p).
Proof. intros [ | ] p P; unfold sel; [ simpl; auto | destruct p; try contradiction; exact I ]. Qed.

Lemma maybe_split: forall (b: bool) sh t (v: @reptype MadtSpecs.CS t) p, isptr p ->
  @data_at MadtSpecs.CS sh t v p |--
  (maybe_at sh t v (sel b p) * (if b then @data_at MadtSpecs.CS sh t v p else emp))%logic.
Proof.
  intros [ | ] sh t v p P; unfold maybe_at, sel.
  - rewrite if_true by reflexivity. cancel.
  - rewrite if_false by (destruct p; try contradiction; discriminate). cancel.
Qed.

Lemma maybe_join: forall (b: bool) sh t (v v': @reptype MadtSpecs.CS t) p, isptr p ->
  (maybe_at sh t v' (sel b p) * (if b then @data_at MadtSpecs.CS sh t v p else emp))%logic |--
  @data_at MadtSpecs.CS sh t (if b then v else v') p.
Proof.
  intros [ | ] sh t v v' p P; unfold maybe_at, sel.
  - rewrite if_true by reflexivity. cancel.
  - rewrite if_false by (destruct p; try contradiction; discriminate). cancel.
Qed.

(* The value of (bool)(arg != NULL) and of arg == NULL. *)
Lemma sel_cmp_ne: forall (b: bool) p, isptr p ->
  force_val (sem_cmp_pp Cne (sel b p) (Vlong (Int64.repr 0))) = Vint (if b then Int.zero else Int.one).
Proof. intros [ | ] p P; unfold sel; [ reflexivity | destruct p; try contradiction; reflexivity ]. Qed.

Lemma sel_cmp_eq: forall (b: bool) p, isptr p ->
  force_val (sem_cmp_pp Ceq (sel b p) (Vlong (Int64.repr 0))) = Vint (if b then Int.one else Int.zero).
Proof. intros [ | ] p P; unfold sel; [ reflexivity | destruct p; try contradiction; reflexivity ]. Qed.

Lemma sel_tc_test: forall (b: bool) p (P: mpred), (P |-- valid_pointer p) -> isptr p ->
  P |-- denote_tc_test_eq (sel b p) (Vlong (Int64.repr 0)).
Proof.
  intros b p P V I. apply denote_tc_test_eq_split; [ | apply valid_pointer_zero64; reflexivity ].
  destruct b; unfold sel; [ apply valid_pointer_zero64; reflexivity | exact V ].
Qed.

(* ---------------------------------------------------------------------- *)
(* The global oracle as main finds it                                      *)
(* ---------------------------------------------------------------------- *)

Definition ob0 : observation := mk_observation 0 0 0 0 0 0.
Definition s0 : ost := mk_ost 0 0 0 (Zrepeat 0 12) (Zrepeat 0 16) 0 (Zrepeat 0 4) (Zrepeat 0 5) (Zrepeat 0 6) 0.

Lemma zero_oracle: zero_val t_oracle = oval nullval 0 ob0 s0.
Proof.
  apply JMeq_eq. eapply JMeq_trans; [ apply JMeq_zero_val_zero_val' | ].
  Timeout 60 vm_compute. apply JMeq_refl.
Qed.

Lemma oracle_zero: forall gv, headptr (gv _oracle) ->
  globvars2pred gv [(_oracle, v_oracle)] |-- ofields (gv _oracle) nullval 0 ob0 s0.
Proof.
  intros gv H. rewrite <- oval_split, <- zero_oracle.
  unfold globvars2pred, globvar2pred. simpl. rewrite ?sepcon_emp.
  change 448 with (sizeof t_oracle).
  apply mapsto_zero_data_at_zero.
  - apply writable_readable, writable_Ews.
  - reflexivity.
  - reflexivity.
  - apply headptr_field_compatible; auto;
      first [ reflexivity | exact I | (vm_compute; reflexivity) | (apply la_env_cs_sound; reflexivity) ].
Qed.

(* ---------------------------------------------------------------------- *)
(* The law's oracle at the call                                            *)
(* ---------------------------------------------------------------------- *)

Lemma ora_intro: forall gv bs ob p sh s, readable_share sh -> length_ok (Zlength bs) = true ->
  Forall byte_ok bs -> obs_ok ob -> ost_ok s -> nmi_ok bs s ->
  os_phase s = 0 -> os_byte s = 0 -> os_word s = 0 -> os_state s = initial_state -> os_rejected s = 0 ->
  (ofields (gv _oracle) p (Zlength bs) ob s * data_at sh (tarray tuchar (Zlength bs)) (bytes_val bs) p)%logic
  |-- Ora_law gv (bs, ob) nil.
Proof.
  intros. unfold Ora_law. Exists p sh s. simpl fst; simpl snd. entailer!. apply J_start; auto.
Qed.

(* The span's two shares: the law's oracle reads one, the consumer the other. *)
Definition sh1 : share := fst (slice.cleave Ews).
Definition sh2 : share := snd (slice.cleave Ews).
Lemma sh1_readable: readable_share sh1.
Proof. apply slice.cleave_readable1. apply writable_readable. apply writable_Ews. Qed.
Lemma sh2_readable: readable_share sh2.
Proof. apply slice.cleave_readable2. apply writable_readable. apply writable_Ews. Qed.
Lemma span_split: forall n v p,
  data_at Ews (tarray tuchar n) v p = (data_at sh1 (tarray tuchar n) v p * data_at sh2 (tarray tuchar n) v p)%logic.
Proof. intros. symmetry. apply data_at_share_join. apply slice.cleave_join. Qed.

Lemma sel_eq_null: forall (b: bool) p, isptr p -> sel b p = nullval -> b = true.
Proof. intros [ | ] p P E; [ reflexivity | unfold sel in E; subst; contradiction ]. Qed.

Lemma sel_ne_null: forall (b: bool) p, sel b p <> nullval -> b = false.
Proof. intros [ | ] p N; [ exfalso; apply N; reflexivity | reflexivity ]. Qed.

(* Freeze the oracle's fields. *)
Ltac idx_oracle R i :=
  lazymatch R with
  | nil => constr:(@nil Z)
  | ?x :: ?R' =>
      let rest := idx_oracle R' (Z.succ i) in
      lazymatch x with
      | field_at _ t_oracle _ _ _ => let i' := eval cbn in i in constr:(i' :: rest)
      | _ => rest
      end
  end.
Ltac freeze_oracle F :=
  match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
    let I := idx_oracle R 0 in freeze_tac I F
  end.

Lemma fa_count: forall v q,
  field_at Ews t_oracle (DOT _nmi_count) v q = data_at Ews tulong v (field_address t_oracle (DOT _nmi_count) q).
Proof. intros. rewrite field_at_data_at. reflexivity. Qed.

Lemma fa_nmi: forall v q,
  field_at Ews t_oracle (DOT _nmi) v q = data_at Ews (tarray tulong 4) v (field_address t_oracle (DOT _nmi) q).
Proof. intros. rewrite field_at_data_at. reflexivity. Qed.

(* Freeze every SEP item that is not one of the oracle's fields nor a data_at of a type in T. *)
Ltac idx_other R T i :=
  lazymatch R with
  | nil => constr:(@nil Z)
  | ?x :: ?R' =>
      let rest := idx_other R' T (Z.succ i) in
      lazymatch x with
      | field_at _ t_oracle _ _ _ => rest
      | data_at _ ?t _ _ => lazymatch T with context [t] => rest | _ => let i' := eval cbn in i in constr:(i' :: rest) end
      | _ => let i' := eval cbn in i in constr:(i' :: rest)
      end
  end.
Ltac freeze_other T F :=
  match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
    let I := idx_other R T 0 in freeze_tac I F
  end.

Lemma fa_offset: forall q f, headptr q -> legal_nested_field t_oracle (DOT f) ->
  field_address t_oracle (DOT f) q = offset_val (nested_field_offset t_oracle (DOT f)) q.
Proof.
  intros q f H L. unfold field_address. rewrite if_true; [ reflexivity | ].
  apply headptr_field_compatible; auto;
    first [ reflexivity | (vm_compute; reflexivity) | (apply la_env_cs_sound; reflexivity) ].
Qed.

Ltac lnf := split; [ exact I | simpl; repeat (first [ left; reflexivity | right ]) ].
Lemma lnf_count: legal_nested_field t_oracle (DOT _nmi_count).
Proof. lnf. Qed.
Lemma lnf_nmi: legal_nested_field t_oracle (DOT _nmi).
Proof. lnf. Qed.

(* The consumer's oracle argument, handed over or not. *)
Lemma add_emp_if: forall (b: bool) (Q R: mpred), b = true -> R |-- ((if b then emp else Q) * R)%logic.
Proof. intros b Q R E. rewrite E. rewrite emp_sepcon. apply derives_refl. Qed.

Lemma to_if_false: forall (b: bool) (Q: mpred), b = false -> Q |-- if b then emp else Q.
Proof. intros b Q E. rewrite E. apply derives_refl. Qed.

Lemma invalid_sel: forall eb obb qb q v_obs v_out n, isptr q -> isptr v_obs -> isptr v_out ->
  invalid_call (sel eb q) (sel obb v_obs) (sel qb v_out) n = (qb || eb || obb || negb (length_ok n))%bool.
Proof. intros. unfold invalid_call. rewrite !sel_isnull by auto. reflexivity. Qed.

(* The oracle as main leaves it before the call. *)
Definition s_main (valid: bool) (c: Z) (m: list Z) : ost :=
  mk_ost (if valid then 0 else 3) 0 0 initial_state (Zrepeat 0 16) c m (Zrepeat 0 5) (Zrepeat 0 6) 0.

Lemma ost_ok_main: forall b c m, u64_ok c -> Zlength m = 4 -> Forall u64_ok m -> ost_ok (s_main b c m).
Proof.
  intros b c m Hc Lm Fm. unfold ost_ok, s_main, u64_ok in *; simpl.
  repeat split; auto; try (destruct b; rep_lia); try rep_lia;
    repeat (apply Forall_cons; [ unfold u64_ok; rep_lia | ]); apply Forall_nil.
Qed.

Lemma nmi_ok_main: forall bs b c m,
  match records bs with Some (c', m') => c = c' /\ m = m' | None => True end -> nmi_ok bs (s_main b c m).
Proof. intros bs b c m H c' m' E. rewrite E in H. simpl. destruct H; split; congruence. Qed.
