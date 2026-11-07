(* Law admission_exact: the body of the harness's main, up to the copy of the MADT into the law's own: the call it
   chooses, the length and the executing ID, the two objects (main returns 0 when either is NULL; malloc(0) may give
   a block), the copy's bytes; the rest is LawMainSetup. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosMadtAdmission.harness.admission_exact.code.
Require Import LeanosMadtAdmission.proof.Defs.
Require Import LeanosMadtAdmission.proof.MgaSpecs.
Require Import LeanosMadtAdmission.proof.LawProg LeanosMadtAdmission.proof.LawDefs LeanosMadtAdmission.proof.LawFacts
  LeanosMadtAdmission.proof.LawLib LeanosMadtAdmission.proof.LawSplit LeanosMadtAdmission.proof.LawMainLib
  LeanosMadtAdmission.proof.LawMainSetup.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

Lemma body_main: forall p, QPprog_vars p = [(_law, v_law)] ->
  semax_body Vlaw Gmain f_main (_main, main_spec_std p).
Proof.
  intros pp Hp. start_function. rewrite Hp.
  assert_PROP (headptr (gv _law)) as HO by entailer!.
  sep_apply (law_zero gv HO).
  sep_apply (create_mem_mgr gv).
  unfold lraw. Intros.
  forward.
  forward_call. Intros c.
  forward_if (temp _t'2 (vi (cc c))).
  { forward. entailer!. unfold cc. destruct (Z.ltb_spec c 3); [ reflexivity | lia ]. }
  { forward. entailer!. unfold cc. destruct (Z.ltb_spec c 3); [ lia | reflexivity ]. }
  forward.
  forward_call. Intros n. forward.
  forward_call. Intros e. forward.
  forward.
  forward_call (tarray tuchar n, gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros madt. forward.
  forward.
  forward_call (tarray tuchar n, gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros cp. forward.
  pose proof (eq_dec madt nullval) as [Em | Nm].
  { (* the MADT's object is NULL *)
    forward_if (temp _t'7 (Vint Int.one)).
    { forward. entailer!. }
    { exfalso. subst madt. auto. }
    forward_if. { forward. Exists (Int.repr 0). entailer!. } { else_false. } }
  rewrite (if_false (madt = nullval) (eq_dec madt nullval)) by exact Nm. Intros.
  pose proof (eq_dec cp nullval) as [Ec | Nc].
  { (* the law's copy is NULL *)
    forward_if (temp _t'7 (Vint Int.one)).
    { exfalso. auto. }
    { forward. forward. entailer!. }
    forward_if. { forward. Exists (Int.repr 0). entailer!. } { else_false. } }
  rewrite (if_false (cp = nullval) (eq_dec cp nullval)) by exact Nc. Intros.
  forward_if (temp _t'7 (Vint Int.zero)).
  { exfalso. auto. }
  { forward. forward. entailer!. destruct cp; try contradiction; reflexivity. }
  forward_if. { else_false. }
  forward.
  forward_call (madt, n, Ews).
  { rewrite (if_false (madt = nullval) (eq_dec madt nullval)) by exact Nm. cancel. }
  Intros bs. rewrite (if_false (madt = nullval) (eq_dec madt nullval)) by exact Nm.
  assert (Lbs: Zlength bs = n) by assumption. assert (Fbs: Forall byte_ok bs) by assumption.
  change (map (fun b => Vint (Int.repr b)) bs) with (bytes_val bs).
  assert (Fbv: Zlength (bytes_val bs) = n) by (unfold bytes_val; rewrite Zlength_map; auto).
  (* the law's copy *)
  rewrite data_at__eq. change (default_val (tarray tuchar n)) with (Zrepeat Vundef n).
  deadvars!.
  forward.
  freeze_but [_length; _copy] true F.
  forward_loop
    (EX i: Z, PROP (0 <= i <= n)
     LOCAL (temp _i (vi i); temp _madt madt; temp _m (gv _law); lvar _id tuint v_id; gvars gv)
     SEP (FRZL F; field_at Ews t_law (DOT _length) (vi n) (gv _law); field_at Ews t_law (DOT _copy) cp (gv _law);
          data_at Ews (tarray tuchar n) (bytes_val bs) madt;
          data_at Ews (tarray tuchar n) (sublist 0 i (bytes_val bs) ++ Zrepeat Vundef (n - i)) cp))%assert
  continue:
    (EX i: Z, PROP (0 <= i < n)
     LOCAL (temp _i (vi i); temp _madt madt; temp _m (gv _law); lvar _id tuint v_id; gvars gv)
     SEP (FRZL F; field_at Ews t_law (DOT _length) (vi n) (gv _law); field_at Ews t_law (DOT _copy) cp (gv _law);
          data_at Ews (tarray tuchar n) (bytes_val bs) madt;
          data_at Ews (tarray tuchar n) (sublist 0 (i + 1) (bytes_val bs) ++ Zrepeat Vundef (n - (i + 1))) cp))%assert
  break:
    (PROP ()
     LOCAL (temp _madt madt; temp _m (gv _law); lvar _id tuint v_id; gvars gv)
     SEP (FRZL F; field_at Ews t_law (DOT _length) (vi n) (gv _law); field_at Ews t_law (DOT _copy) cp (gv _law);
          data_at Ews (tarray tuchar n) (bytes_val bs) madt; data_at Ews (tarray tuchar n) (bytes_val bs) cp))%assert.
  { Exists 0. entailer!. apply derives_refl'. f_equal; try list_solve. }
  { Intros i. forward.
    forward_if.
    { forward.
      assert (Ri: 0 <= Znth i bs <= Byte.max_unsigned) by (apply Forall_byte_Znth; auto; lia).
      forward.
      { entailer!. rewrite Znth_bytes_val by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
      rewrite Znth_bytes_val by lia.
      forward.
      Exists i. entailer!. apply derives_refl'. f_equal.
      rewrite <- Znth_bytes_val by lia. list_solve. }
    { forward. entailer!. apply derives_refl'. f_equal.
      replace i with (Zlength bs) by lia. list_solve. } }
  { Intros i. forward. Exists (i + 1). entailer!. }
  thaw F.
  assert_PROP (isptr madt /\ isptr cp) as PP by entailer!. destruct PP as [Pm Pc].
  eapply semax_pre;
    [ | apply (tail_setup gv madt cp v_id c n e bs); first [ reflexivity | assumption | auto ] ].
  unfold lraw. entailer!.
Qed.
