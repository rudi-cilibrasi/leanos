(* Law admission_exact: main after the function returned: its checks (the protocol ended with the status, the
   copy unchanged, the APIC ID record holding the APIC ID on OK but for the envelope and the prior value
   otherwise), from what the function's specification gives (returns, rec_ok) and the law's oracle (ret_inv). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosMadtAdmission.harness.admission_exact.code.
Require Import LeanosMadtAdmission.proof.Defs.
Require Import LeanosMadtAdmission.proof.MgaSpecs.
Require Import LeanosMadtAdmission.proof.LawProg LeanosMadtAdmission.proof.LawDefs LeanosMadtAdmission.proof.LawFacts
  LeanosMadtAdmission.proof.LawLib LeanosMadtAdmission.proof.LawMainLib.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[local] Existing Instance LawProg.LCS.

Lemma tail_check {Espec: OracleKind} gv madt vid x h st w rec:
  inputs_ok x -> returns x h = Some (st, w) -> rec_ok x st w rec -> u32_ok rec -> isptr madt ->
  forall Delta R cmd, Delta = Delta0 -> R = Post0 -> cmd = s_check ->
  semax Delta
    (PROP ()
     LOCAL (temp _status (vi st); temp _prior (vi (i_prior x)); temp _madt madt; temp _m (gv _law);
            lvar _id tuint vid; gvars gv)
     SEP (Ora_law gv x h; data_at Ews (tarray tuchar (i_length x)) (bytes_val (i_bytes x)) madt;
          data_at Tsh tuint (vi rec) vid; TT))
    cmd R.
Proof.
  intros Hx Hr Hrec Hu Pm Delta R cmd -> -> ->.
  unfold s_check, Delta0, Post0. start_tail.
  unfold Ora_law. Intros p s.
  match goal with H: lst_ok s |- _ => rename H into Hs end.
  match goal with H: J x h s |- _ => rename H into HJ end.
  pose proof (J_returns _ _ _ _ Hr HJ) as (E & V & Wd). simpl fst in V; simpl snd in Wd. unfold E_NOTHING in E.
  pose proof Hx as Hx''. inputs_facts Hx''. pose proof Hs as Hs'. lst_facts Hs'.
  assert (Rst: 0 <= st <= Int.max_unsigned) by (rewrite <- V; auto).
  pose proof (call_code_range (i_call x)) as Rc.
  unfold u32_ok in Hu.
  unfold lfields. Intros.
  (* the protocol ended with the function's status *)
  if1. gp.
  (* the copy unchanged *)
  deadvars!.
  forward.
  freeze_but [_length; _copy] true F.
  forward_loop
    (EX i: Z, PROP (0 <= i <= i_length x)
     LOCAL (temp _i__1 (vi i); temp _status (vi st); temp _prior (vi (i_prior x)); temp _madt madt;
            temp _m (gv _law); lvar _id tuint vid; gvars gv)
     SEP (FRZL F; field_at Ews t_law (DOT _length) (vi (i_length x)) (gv _law);
          field_at Ews t_law (DOT _copy) p (gv _law);
          data_at Ews (tarray tuchar (i_length x)) (bytes_val (i_bytes x)) p;
          data_at Ews (tarray tuchar (i_length x)) (bytes_val (i_bytes x)) madt))%assert
  continue:
    (EX i: Z, PROP (0 <= i < i_length x)
     LOCAL (temp _i__1 (vi i); temp _status (vi st); temp _prior (vi (i_prior x)); temp _madt madt;
            temp _m (gv _law); lvar _id tuint vid; gvars gv)
     SEP (FRZL F; field_at Ews t_law (DOT _length) (vi (i_length x)) (gv _law);
          field_at Ews t_law (DOT _copy) p (gv _law);
          data_at Ews (tarray tuchar (i_length x)) (bytes_val (i_bytes x)) p;
          data_at Ews (tarray tuchar (i_length x)) (bytes_val (i_bytes x)) madt))%assert
  break:
    (PROP ()
     LOCAL (temp _status (vi st); temp _prior (vi (i_prior x)); temp _madt madt;
            temp _m (gv _law); lvar _id tuint vid; gvars gv)
     SEP (FRZL F; field_at Ews t_law (DOT _length) (vi (i_length x)) (gv _law);
          field_at Ews t_law (DOT _copy) p (gv _law);
          data_at Ews (tarray tuchar (i_length x)) (bytes_val (i_bytes x)) p;
          data_at Ews (tarray tuchar (i_length x)) (bytes_val (i_bytes x)) madt))%assert.
  { Exists 0. entailer!. }
  { Intros i. forward.
    forward_if.
    { assert (Ri: 0 <= Znth i (i_bytes x) <= Byte.max_unsigned) by (apply Forall_byte_Znth; auto; lia).
      forward.
      { entailer!. rewrite Znth_bytes_val by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
      forward. forward.
      rewrite Znth_bytes_val by lia.
      forward_call Int.one.
      { entailer!. simpl. rewrite Int.eq_true. reflexivity. }
      Exists i. entailer!. }
    { forward. entailer!. } }
  { Intros i. forward. Exists (i + 1). entailer!. }
  thaw F.
  (* the APIC ID record *)
  forward_if (temp _t'15 (Vint (Int.repr (Z.b2z ((st =? S_OK) && negb (call_code (i_call x) =? 0)))))).
  { forward. forward. entailer!. unfold S_OK. bool_fin. }
  { forward. entailer!. unfold S_OK. bool_fin. }
  forward_if (PROP ()
    LOCAL (temp _status (vi st); temp _prior (vi (i_prior x)); temp _madt madt; temp _m (gv _law);
           lvar _id tuint vid; gvars gv)
    SEP (data_at Tsh tuint (vi rec) vid; TT)).
  { (* OK, but the envelope: the record holds the APIC ID *)
    assert (Wr: w = Some rec) by (unfold rec_ok in Hrec; match goal with E: _ = true |- _ => rewrite E in Hrec end; exact Hrec).
    rewrite Wr in Wd.
    forward. forward.
    forward_call Int.one.
    { entailer!. rewrite Int64.eq_true. reflexivity. }
    entailer!. }
  { (* else: the prior value *)
    assert (Wr: rec = i_prior x) by (unfold rec_ok in Hrec; match goal with E: _ = false |- _ => rewrite E in Hrec end; exact Hrec).
    forward.
    forward_call Int.one.
    { entailer!. rewrite Int.eq_true. reflexivity. }
    entailer!. }
  forward. Exists (Int.repr 0). entailer!.
Qed.
