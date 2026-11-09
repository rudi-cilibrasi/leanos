(* Law admission_exact: main's setup of the law after the copy: the result's ten arguments, the prior value of the
   APIC ID record, the protocol's fields, then the stage the function starts at (EXPECT_RESULT, begin_entries,
   EXPECT_ENVELOPE or envelope_done at once for an empty copy), which is the model's start (J at no answers);
   then the call (LawMainDisp). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosMadtAdmission.harness.admission_exact.code.
Require Import LeanosMadtAdmission.proof.Defs.
Require Import LeanosMadtAdmission.proof.MgaSpecs.
Require Import LeanosMadtAdmission.proof.LawProg LeanosMadtAdmission.proof.LawDefs LeanosMadtAdmission.proof.LawFacts
  LeanosMadtAdmission.proof.LawLib LeanosMadtAdmission.proof.LawSplit LeanosMadtAdmission.proof.LawMainLib
  LeanosMadtAdmission.proof.LawMainDisp.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

(* The function is not the one whose code the C compared the call with. *)
Ltac ne_call c x :=
  let Ef := fresh "Ef" in
  intro Ef; change (i_call x) with (call_of (cc c)) in Ef; apply (f_equal call_code) in Ef; cbn [call_code] in Ef;
  lia.

Lemma tail_setup {Espec: OracleKind} gv madt cp vid c n e bs:
  0 <= c <= Byte.max_unsigned -> u32_ok n -> u32_ok e -> Zlength bs = n -> Forall byte_ok bs ->
  isptr madt -> isptr cp ->
  forall Delta R cmd, Delta = Delta0 -> R = Post0 -> cmd = s_setup ->
  semax Delta
    (PROP () LOCAL (temp _madt madt; temp _m (gv _law); lvar _id tuint vid; gvars gv)
     SEP (lraw (gv _law) (cc c) n e cp (Zrepeat 0 10) 0 0 0 0 (Zrepeat 0 12) (Zrepeat 0 16) 0;
          data_at Ews (tarray tuchar n) (bytes_val bs) madt; data_at Ews (tarray tuchar n) (bytes_val bs) cp;
          data_at_ Tsh tuint vid; TT))
    cmd R.
Proof.
  intros Hc Hn He Lbs Fbs Pm Pc Delta R cmd -> -> ->.
  unfold s_setup, Delta0, Post0. start_tail.
  unfold lraw. Intros. unfold u32_ok in Hn, He.
  (* the result's arguments *)
  freeze_but [_args] false F.
  forward_for_simple_bound 10
    (EX k: Z, EX al: list Z,
     PROP (Zlength al = k; Forall u64_ok al)
     LOCAL (temp _madt madt; temp _m (gv _law); lvar _id tuint vid; gvars gv)
     SEP (FRZL F; field_at Ews t_law (DOT _args) (map vl (al ++ Zrepeat 0 (10 - k))) (gv _law)))%assert.
  { Exists (@nil Z). entailer!. }
  { forward_call tt. Intros a. forward.
    Exists (al ++ [a]). entailer!.
    - split; [ list_solve | ]. apply Forall_app; split; [ auto | ]. apply Forall_cons; [ assumption | apply Forall_nil ].
    - rewrite upd_Znth_map_vl. apply derives_refl'. do 2 f_equal. list_solve. }
  Intros al. thaw F.
  replace (al ++ Zrepeat 0 (10 - 10)) with al by list_solve.
  (* the record's prior value *)
  forward_call. Intros pr. forward. forward.
  (* the law's protocol *)
  forward. forward. forward. forward.
  change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with (vl 0).
  change (Vint (Int.repr 0)) with (vi 0).
  freeze_but [_state] false F2.
  forward_for_simple_bound 12
    (EX k: Z, PROP ()
     LOCAL (temp _prior (vi pr); temp _madt madt; temp _m (gv _law); lvar _id tuint vid; gvars gv)
     SEP (FRZL F2; field_at Ews t_law (DOT _state) (map vl (Zrepeat 0 12)) (gv _law)))%assert.
  { entailer!. }
  { forward. change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with (vl 0).
    rewrite upd_Znth_map_vl. replace (upd_Znth i (Zrepeat 0 12) 0) with (Zrepeat 0 12) by list_solve. entailer!. }
  thaw F2.
  assert (Fal: Forall u64_ok al) by assumption.
  pose (x := mk_inputs (call_of (cc c)) bs n e al pr).
  assert (Hx: inputs_ok x) by (unfold x, inputs_ok, u32_ok; simpl; split_and; auto; lia).
  pose proof (cc_range c ltac:(lia)) as Rcc.
  rewrite <- (call_code_of c) by lia.
  change (call_of (cc c)) with (i_call x).
  pose proof (call_code_range (i_call x)) as Rcx. pose proof (call_code_range (call_of (cc c))) as Rcx'.
  forward.
  forward_if (EX s0: lst,
    PROP (lst_ok s0; J x nil s0; ls_args s0 = i_args x)
    LOCAL (temp _prior (vi pr); temp _madt madt; temp _m (gv _law); lvar _id tuint vid; gvars gv)
    SEP (lfields (gv _law) cp x s0; data_at Ews (tarray tuchar n) (bytes_val bs) madt;
         data_at Ews (tarray tuchar n) (bytes_val bs) cp; data_at Tsh tuint (vi pr) vid; TT)).
  - (* the result: EXPECT_RESULT *)
    u64c. forward.
    Exists (s_init al E_RESULT). unfold lfields, s_init; lst_cbn. entailer!.
    split; [ apply lst_ok_init; auto; unfold E_RESULT; lia | ].
    apply J_start_result; auto. apply call_code_2; auto.
  - u64c. forward. forward_if.
    + (* the entries: begin_entries *)
      u64c.
      sep_apply (lfields_fold (gv _law) cp x al 0 0 0 0 (Zrepeat 0 12) (Zrepeat 0 16) 0).
      fold (s_init al 0).
      forward_call (gv _law, cp, x, s_init al 0).
      { split_and; auto; apply lst_ok_init; auto; lia. }
      Intros s'. Exists s'. entailer!.
      apply J_start_entries; auto. apply call_code_1; auto.
    + (* the envelope or the admission: EXPECT_ENVELOPE *)
      u64c. forward. forward. forward_if.
      * (* an empty copy: envelope_done at once *)
        u64c.
        sep_apply (lfields_fold (gv _law) cp x al 0 0 0 0 (Zrepeat 0 12) (Zrepeat 0 16) 0).
        fold (s_init al 0).
        forward_call (gv _law, cp, x, s_init al 0).
        { split_and; auto; apply lst_ok_init; auto; lia. }
        Intros s'. Exists s'. entailer!.
        apply J_start_env0; auto; ne_call c x.
      * u64c. assert (Ln0: 0 < i_length x) by (change (i_length x) with n; lia).
        forward.
        Exists (s_init al E_ENVELOPE). unfold lfields, s_init; lst_cbn. entailer!.
        split; [ apply lst_ok_init; auto; unfold E_ENVELOPE; lia | ].
        apply J_start_env; auto; try lia; ne_call c x.
  - Intros s0.
    eapply semax_pre; [ | apply (tail_disp gv madt cp vid x s0); first [ reflexivity | assumption | auto ] ].
    entailer!.
Qed.
