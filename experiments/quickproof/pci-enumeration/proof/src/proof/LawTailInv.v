(* Law enumeration_exact: main after the scan, when it returned INVALID_ARGUMENT (the callback or the snapshot
   is NULL): no read, the snapshot untouched or with count 0, the result at location 0. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosEnum.harness.enumeration_exact.code.
Require Import LeanosEnum.proof.Defs.
Require LeanosEnum.proof.EnumSpecs.
Require Import LeanosEnum.proof.LawProg LeanosEnum.proof.LawRun LeanosEnum.proof.LawSpecs LeanosEnum.proof.LawSplit
  LeanosEnum.proof.LawLib LeanosEnum.proof.LawOut LeanosEnum.proof.LawMainDefs.
Local Open Scope Z_scope.

Lemma tail_inv {Espec: OracleKind} gv v_d v_snapshot v_result (rbq sb qb: bool) cnt rb rd rf ro seen
    (rest: list (reptype EnumSpecs.t_header)):
  isptr v_d -> isptr v_snapshot -> isptr v_result -> isptr (gv _device_read) ->
  0 <= cnt <= Int.max_unsigned -> 0 <= rb <= Byte.max_unsigned -> 0 <= rd <= Byte.max_unsigned ->
  0 <= rf <= Byte.max_unsigned -> 0 <= ro <= Byte.max_unsigned ->
  (rbq || sb)%bool = true ->
  forall Delta R c, Delta = Delta0 -> R = Post0 -> c = s_after_call ->
  semax Delta
    (PROP ()
     LOCAL (temp _status (Vint (Int.repr 3)); temp _result_arg (if qb then nullval else v_result);
            temp _snapshot_arg (if sb then nullval else v_snapshot);
            temp _read_arg (if rbq then nullval else gv _device_read);
            temp _prior_offset (Vint (Int.repr ro)); temp _prior_function (Vint (Int.repr rf));
            temp _prior_device (Vint (Int.repr rd)); temp _prior_bus (Vint (Int.repr rb));
            temp _prior_count (Vint (Int.repr cnt));
            lvar _result EnumSpecs.t_result v_result; lvar _snapshot EnumSpecs.t_snapshot v_snapshot;
            lvar _d t_device v_d; gvars gv)
     SEP (data_at Tsh EnumSpecs.t_result
            (Vint (Int.repr (if qb then 0 else 3)),
             (Vint (Int.repr (if qb then rb else 0)), (Vint (Int.repr (if qb then rd else 0)),
              (Vint (Int.repr (if qb then rf else 0)), Vint (Int.repr (if qb then ro else 0)))))) v_result;
          data_at Tsh EnumSpecs.t_snapshot
            (Vint (Int.repr (if sb then cnt else 0)),
             if sb then Zrepeat (Vundef, (Vundef, (Vundef, Zrepeat Vundef 16))) 16 else rest) v_snapshot;
          TT; func_ptr' (EnumSpecs.read_spec Dev_exact) (gv _device_read); has_ext tt;
          field_at Tsh t_device (DOT _next) (Vint (Int.repr 0)) v_d;
          field_at Tsh t_device (DOT _word) (Vint (Int.repr 0)) v_d;
          field_at Tsh t_device (DOT _found) (Vint (Int.repr 0)) v_d;
          field_at Tsh t_device (DOT _stopped) (Vint (Int.repr 0)) v_d;
          field_at Tsh t_device (DOT _failed) (Vint (Int.repr 0)) v_d;
          field_at Tsh t_device (DOT _reads) (Vint (Int.repr 0)) v_d;
          field_at Tsh t_device (DOT _last_bus) Vundef v_d;
          field_at Tsh t_device (DOT _last_device) Vundef v_d;
          field_at Tsh t_device (DOT _last_function) Vundef v_d;
          field_at Tsh t_device (DOT _last_offset) Vundef v_d;
          field_at Tsh t_device (DOT _seen) seen v_d))
    c R.
Proof.
  intros until c. intros -> -> ->.
  unfold s_after_call.
  start_tail.
  rename H8 into Inv.
  freeze [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15] F1.
  (* status in range *)
  forward_if (temp _t'13 (Vint Int.one)).
  { forward. entailer!. }
  { exfalso. match goal with N: _ |- _ => solve [ apply N; reflexivity | inv N ] end. }
  gp_call.
  (* the result record: the status, or untouched *)
  forward_if True.
  { tc_sel. }
  { match goal with E: (if _ then nullval else _) <> nullval |- _ => apply sel_ne_null in E end. subst qb.
    forward. gp_call. all: try entailer!. }
  { match goal with E: (if _ then nullval else _) = nullval |- _ => apply sel_eq_null in E; [ | auto ] end. subst qb.
    forward.
    forward_if (temp _t'14 (Vint Int.one)).
    { forward. forward. entailer!; rewrite ?Int.eq_true; reflexivity. }
    { exfalso. match goal with N: _ |- _ => solve [ apply N; reflexivity ] end. }
    forward_if (temp _t'15 (Vint Int.one)).
    { forward. forward. entailer!; rewrite ?Int.eq_true; reflexivity. }
    { discriminate. }
    forward_if (temp _t'16 (Vint Int.one)).
    { forward. forward. entailer!; rewrite ?Int.eq_true; reflexivity. }
    { discriminate. }
    forward_if (temp _t'17 (Vint Int.one)).
    { forward. forward. entailer!; rewrite ?Int.eq_true; reflexivity. }
    { discriminate. }
    gp_call. all: try entailer!. }
  Intros.
  (* located *)
  forward; try tc_sel.
  rewrite (sel_ne_val qb v_result) by auto.
  thaw F1.
  (* INVALID_ARGUMENT exactly when the callback or the snapshot is NULL *)
  forward_if (temp _t'18 (Vint (Int.repr (b2z (rbq || sb))))).
  { tc_sel. }
  { match goal with E: (if _ then nullval else _) = nullval |- _ => apply sel_eq_null in E; [ | auto ] end.
    subst rbq. forward. entailer!. }
  { match goal with E: (if _ then nullval else _) <> nullval |- _ => apply sel_ne_null in E end.
    subst rbq. forward. { tc_sel. }
    entailer!. destruct sb; [ reflexivity | destruct v_snapshot; try contradiction; reflexivity ]. }
  gp_call.
  { entailer!. rewrite Inv. reflexivity. }
  (* the snapshot's count: untouched, or 0 *)
  forward_if (temp _t'19 (Vint (Int.repr (if sb then cnt else 0)))).
  { tc_sel. }
  { match goal with E: (if _ then nullval else _) = nullval |- _ => apply sel_eq_null in E; [ | auto ] end.
    subst sb. forward. entailer!. }
  { match goal with E: (if _ then nullval else _) <> nullval |- _ => apply sel_ne_null in E end.
    subst sb.
    forward_if (temp _t'19 (Vint (Int.repr 0))).
    { exfalso. match goal with N: _ |- _ => solve [ inv N ] end. }
    { forward. forward. entailer!. } }
  forward.
  gp_call.
  (* INVALID_ARGUMENT: no read, location 0 *)
  forward_if.
  { forward. gp_call.
    forward_if (temp _t'20 (Vint Int.one)).
    { forward. entailer!. }
    { b2z_hyps. match goal with E: negb qb = true |- _ => apply negb_true_iff in E end. subst qb.
      forward.
      forward_if (temp _t'21 (Vint Int.one)).
      { forward. forward. entailer!. }
      { exfalso. match goal with N: _ |- _ => solve [ apply N; reflexivity ] end. }
      forward_if (temp _t'22 (Vint Int.one)).
      { forward. forward. entailer!. }
      { discriminate. }
      forward_if (temp _t'20 (Vint Int.one)).
      { forward. forward. forward. entailer!. }
      { discriminate. }
      entailer!. }
    gp_call.
    pose proof (dev_free 0 0 0 0 0 0 loc_undef seen v_d) as DF.
    unfold dev_fields, loc_undef in DF. simpl fst in DF; simpl snd in DF.
    sep_apply DF.
    free1 EnumSpecs.t_snapshot v_snapshot. free1 EnumSpecs.t_result v_result.
    forward.
    Exists (Int.repr 0). entailer!. }
  { exfalso. match goal with N: _ |- _ => solve [ apply N; reflexivity ] end. }
Qed.
