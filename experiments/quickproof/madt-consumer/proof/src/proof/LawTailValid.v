(* Law consumer_obligations: main's checks after a call of madt_bind with valid arguments: the consumer's outcome
   against the law's oracle (main_ok). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosMadt.harness.consumer_obligations.code.
Require Import LeanosMadt.proof.Defs.
Require Import LeanosMadt.proof.MadtSpecs.
Require Import LeanosMadt.proof.LawProg LeanosMadt.proof.LawDefs LeanosMadt.proof.LawFacts LeanosMadt.proof.LawLib
  LeanosMadt.proof.LawSplit LeanosMadt.proof.LawMainLib LeanosMadt.proof.LawMainDefs.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.
Require Import LeanosMadt.proof.LawTailValid2 LeanosMadt.proof.LawTailValid1.

Ltac ptr_tc := entailer!; apply sel_tc_test; [ entailer! | auto ].
Ltac free_locals := sep_apply (data_at_data_at_ Tsh t_result); sep_apply (data_at_data_at_ Tsh t_obs).
(* bool_fin with the conditions of main's checks. *)
Ltac bool_fin' := bool_fin_loc ltac:(unfold two_b).

Lemma span_valid_ptr: forall sh k (vs: list val) q, readable_share sh -> 0 < k ->
  @data_at MadtSpecs.CS sh (tarray tuchar k) vs q |-- valid_pointer q.
Proof. intros. apply data_at_valid_ptr; [ apply readable_nonidentity; auto | simpl; lia ]. Qed.

Lemma tail_valid {Espec: OracleKind} gv q v_out v_observation n bs ob h o:
  isptr q -> isptr v_out -> isptr v_observation -> length_ok n = true -> Zlength bs = n ->
  consume (bs, ob) h = Some o ->
  forall Delta R c, Delta = Delta0 -> R = Post0 -> c = s_after_call ->
  semax Delta
    (PROP ()
     LOCAL (temp _status (vl (status_of o)); temp _walk (Vint (Int.repr (if walk_b bs then 1 else 0)));
            temp _out_arg v_out; temp _observation_arg v_observation; temp _entries_arg q;
            temp _valid_length (Vint (Int.repr 1)); temp _length (Vlong (Int64.repr n)); temp _o (gv _oracle);
            lvar _out t_result v_out; lvar _observation t_obs v_observation; gvars gv)
     SEP (Ora_law gv (bs, ob) h; @data_at LCS Tsh t_result (result_val o) v_out;
          @data_at LCS Tsh t_obs (obs_val ob) v_observation;
          @data_at MadtSpecs.CS sh2 (tarray tuchar (Zlength bs)) (bytes_val bs) q; TT))
    c R.
Proof.
  intros Pq Po Pob L Zbn C Delta R c -> -> ->.
  unfold s_after_call. start_tail.
  unfold Ora_law. Intros p sh s. simpl fst in *; simpl snd in *.
  rename H into Hsh, H0 into Hlen, H1 into Hby, H2 into Hob, H3 into Hok, H4 into Hnmi, H5 into HJ.
  pose proof (J_consume _ _ _ _ C HJ) as M.
  destruct o as [[[[[stt d] off] a] cc] bb].
  pose proof M as Mall.
  unfold main_ok in M. destruct M as (Mst & Mz & Mrej & Mok).
  unfold result_val, status_of in *. cbv beta iota.
  pose proof Hok as (Rph & Rby & Rwo & Rco & Rre & Lst & Lan & Lnm & Lpo & Lbo & Fst & Fan & Fnm & Fpo & Fbo).
  unfold u64_ok in Rph, Rby, Rwo, Rco, Rre.
  assert (Lb0: 0 < Zlength bs) by (unfold length_ok in L; apply andb_true_iff in L as [L1 _]; apply Z.ltb_lt in L1; lia).
  unfold ofields. Intros.
  (* out_arg is not NULL *)
  match goal with |- semax _ ?Pre _ _ => forward_if Pre end.
  { exfalso. subst v_out. contradiction. }
  { forward. entailer!. }
  (* the status *)
  forward. if1. gp.
  (* the arguments are valid *)
  forward_if (temp _t'35 (Vint Int.zero)).
  { apply denote_tc_test_eq_split; [ | apply valid_pointer_zero64; reflexivity ].
    sep_apply (span_valid_ptr sh2 (Zlength bs) (bytes_val bs) q sh2_readable Lb0). entailer!. }
  { exfalso. subst q. contradiction. }
  { forward. entailer!. destruct v_observation; try contradiction. reflexivity. }
  forward_if (temp _t'36 (Vint Int.zero)).
  { else_false. }
  { forward. entailer!. }
  match goal with |- semax _ ?Pre _ _ => forward_if Pre end.
  { else_false. }
  { forward. entailer!. }
  deadvars!.
  (* no APIC on a rejection *)
  match goal with |- semax _ ?Pre _ _ => forward_if Pre end.
  { assert (Hs: stt <> 0) by (u64c; auto). destruct (Mz Hs) as (Ea & Ec & Eb). subst a cc bb.
    if1. if1. gp. entailer!. }
  { forward. entailer!. }
  (* a rejected stream *)
  forward.
  destruct (Z.eq_dec (os_rejected s) 0) as [R0 | R1].
  - match goal with |- semax _ ?Pre _ _ => forward_if Pre end.
    { exfalso. rewrite R0 in *. change Int64.zero with (Int64.repr 0) in *. auto. }
    { forward. entailer!. }
    eapply semax_pre; [ | apply (tail_v1 gv v_out v_observation n bs ob s p stt d off a cc bb); auto ].
    unfold ofields. entailer!.
  - destruct (Mrej R1) as (Es & Ed & Eo). clear Mok Mrej Mz Mall. subst off.
    rng_list (os_answer s) 3.
    freeze_res [_answer; _byte] F1.
    forward_if (PROP (False) LOCAL () SEP ()).
    { forward.
      forward_if (temp _t'39 (Vint (Int.repr (Z.b2z (two_b (os_answer s)))))).
      { forward. forward. entailer!. bool_fin'. }
      { forward. entailer!. bool_fin'. }
      forward.
      forward_if (temp _t'40 (Vint (Int.repr (if two_b (os_answer s) then 2 else 3)))).
      { forward. entailer!. if_b (two_b (os_answer s)). }
      { forward. entailer!. if_b (two_b (os_answer s)). }
      forward_if (temp _t'41 (Vint Int.one)).
      { forward_if (temp _t'42 (vl (if two_b (os_answer s) then Znth 2 (os_answer s) else 0))).
        { forward. forward. entailer!. if_b (two_b (os_answer s)). }
        { forward. entailer!. if_b (two_b (os_answer s)). }
        forward. forward. entailer!. try subst d. destruct (two_b (os_answer s)); cmp_close. }
      { exfalso. match goal with E: _ <> _ |- _ => apply E end. try subst stt.
        destruct (two_b (os_answer s)); reflexivity. }
      gp.
      forward. forward.
      to_branch; forward_call Int.one; [ entailer!; simpl; rewrite ?add64_repr'; cmp_close | ].
      thaw F1. free_locals. forward. Exists (Int.repr 0). entailer!. }
    { else_false'. }
Qed.
