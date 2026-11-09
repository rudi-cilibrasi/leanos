(* Law enumeration_exact: main after the scan, when it returned READ_FAILED or CAPACITY_EXCEEDED: the device
   stopped after at least one read, failed exactly on READ_FAILED, found 17 functions exactly on
   CAPACITY_EXCEEDED, and the result names its last read; the snapshot has count 0. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosEnum.harness.enumeration_exact.code.
Require Import LeanosEnum.proof.Defs.
Require LeanosEnum.proof.EnumSpecs.
Require Import LeanosEnum.proof.LawProg LeanosEnum.proof.LawRun LeanosEnum.proof.LawSpecs LeanosEnum.proof.LawSplit
  LeanosEnum.proof.LawLib LeanosEnum.proof.LawOut LeanosEnum.proof.LawMainDefs.
Local Open Scope Z_scope.

(* A comparison of the harness on words in range, as the boolean of Z. *)
Ltac null_contra :=
  exfalso;
  match goal with
  | E: (if ?b then nullval else ?p) = nullval |- _ => apply sel_eq_null in E; [ congruence | auto ]
  | E: ?p = nullval, P: isptr ?p |- _ => rewrite E in P; exact P
  | E: nullval = ?p, P: isptr ?p |- _ => rewrite <- E in P; exact P
  end.

Ltac zb :=
  repeat match goal with
  | |- context [Z.b2z true] => change (Z.b2z true) with 1
  | |- context [Z.b2z false] => change (Z.b2z false) with 0
  | |- context [Int.eq ?x ?x] => rewrite (Int.eq_true x)
  | |- context [Int.eq (Int.repr ?a) (Int.repr ?b)] => rewrite (Int_eq_repr a b) by rep_lia
  | |- context [Int.lt (Int.repr ?a) (Int.repr ?b)] => rewrite (Int_lt_repr a b) by rep_lia
  | |- context [Int.ltu (Int.repr ?a) (Int.repr ?b)] => rewrite (Int_ltu_repr a b) by rep_lia
  | |- context [?a <? ?b] => destruct (Z.ltb_spec a b)
  | |- context [?a =? ?b] => destruct (Z.eqb_spec a b)
  | |- context [zlt ?a ?b] => destruct (zlt a b)
  | |- context [zeq ?a ?b] => destruct (zeq a b)
  end; try lia; try reflexivity.

(* A test of the status that cannot hold. *)
Ltac stc :=
  first [ lia
        | match goal with N: Int.repr _ = Int.repr _ |- _ => apply repr_inj_signed in N; rep_lia end
        | discriminate ].

Ltac gp_by tac := forward_call (Int.one); try solve [ entailer!; tac ].

Lemma tail_stop {Espec: OracleKind} gv v_d v_snapshot v_result (rbq sb qb: bool) cnt rb rd rf ro
    st i off nx wx fx n seen (rest: list (reptype EnumSpecs.t_header)):
  isptr v_d -> isptr v_snapshot -> isptr v_result -> isptr (gv _device_read) ->
  0 <= cnt <= Int.max_unsigned -> 0 <= rb <= Byte.max_unsigned -> 0 <= rd <= Byte.max_unsigned ->
  0 <= rf <= Byte.max_unsigned -> 0 <= ro <= Byte.max_unsigned ->
  (rbq || sb)%bool = false ->
  (st = S_READ_FAILED /\ 0 <= fx <= CAPACITY \/ st = S_CAPACITY_EXCEEDED /\ fx = CAPACITY + 1) ->
  1 <= n <= FUNCTIONS + WORDS * CAPACITY + 1 -> 0 <= i < FUNCTIONS -> 0 <= off <= 60 ->
  forall Delta R c, Delta = Delta0 -> R = Post0 -> c = s_after_call ->
  semax Delta
    (PROP ()
     LOCAL (temp _status (Vint (Int.repr st)); temp _result_arg (if qb then nullval else v_result);
            temp _snapshot_arg (if sb then nullval else v_snapshot);
            temp _read_arg (if rbq then nullval else gv _device_read);
            temp _prior_offset (Vint (Int.repr ro)); temp _prior_function (Vint (Int.repr rf));
            temp _prior_device (Vint (Int.repr rd)); temp _prior_bus (Vint (Int.repr rb));
            temp _prior_count (Vint (Int.repr cnt));
            lvar _result EnumSpecs.t_result v_result; lvar _snapshot EnumSpecs.t_snapshot v_snapshot;
            lvar _d t_device v_d; gvars gv)
     SEP (data_at Tsh EnumSpecs.t_result
            (Vint (Int.repr (if qb then 0 else st)),
             (Vint (Int.repr (if qb then rb else bus_of i)), (Vint (Int.repr (if qb then rd else dev_of i)),
              (Vint (Int.repr (if qb then rf else fn_of i)), Vint (Int.repr (if qb then ro else off)))))) v_result;
          data_at Tsh EnumSpecs.t_snapshot
            (Vint (Int.repr (if sb then cnt else 0)),
             if sb then Zrepeat (Vundef, (Vundef, (Vundef, Zrepeat Vundef 16))) 16 else rest) v_snapshot;
          TT; func_ptr' (EnumSpecs.read_spec Dev_exact) (gv _device_read); has_ext tt;
          field_at Tsh t_device (DOT _next) (Vint (Int.repr nx)) v_d;
          field_at Tsh t_device (DOT _word) (Vint (Int.repr wx)) v_d;
          field_at Tsh t_device (DOT _found) (Vint (Int.repr fx)) v_d;
          field_at Tsh t_device (DOT _stopped) (Vint (Int.repr 1)) v_d;
          field_at Tsh t_device (DOT _failed) (Vint (Int.repr (b2z (st =? S_READ_FAILED)))) v_d;
          field_at Tsh t_device (DOT _reads) (Vint (Int.repr n)) v_d;
          field_at Tsh t_device (DOT _last_bus) (Vint (Int.repr (bus_of i))) v_d;
          field_at Tsh t_device (DOT _last_device) (Vint (Int.repr (dev_of i))) v_d;
          field_at Tsh t_device (DOT _last_function) (Vint (Int.repr (fn_of i))) v_d;
          field_at Tsh t_device (DOT _last_offset) (Vint (Int.repr off)) v_d;
          field_at Tsh t_device (DOT _seen) seen v_d))
    c R.
Proof.
  intros Pd Ps Pq Pr Rc Rrb Rrd Rrf Rro Inv Hst Hn Hi Ho Delta R c -> -> ->.
  unfold s_after_call.
  start_tail.
  apply orb_false_iff in Inv. destruct Inv as [Erb Esb].
  pose proof (bus_range i Hi) as Rb. pose proof (dev_range i) as Rd. pose proof (fn_range i) as Rfn.
  unfold S_READ_FAILED, S_CAPACITY_EXCEEDED, FUNCTIONS, WORDS, CAPACITY in *.
  assert (Rst: 1 <= st <= 2) by lia.
  freeze [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15] F1.
  (* status in range *)
  forward_if (temp _t'13 (Vint Int.one)).
  { forward. entailer!. zb. }
  { exfalso. lia. }
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
  (* not INVALID_ARGUMENT: the callback and the snapshot are there *)
  forward_if (temp _t'18 (Vint (Int.repr 0))).
  all: try tc_sel.
  1: null_contra.
  1: { forward; try tc_sel. entailer!.
       try subst sb; simpl; destruct v_snapshot; try contradiction; reflexivity. }
  gp_by zb.
  (* the snapshot's count: 0 *)
  forward_if (temp _t'19 (Vint (Int.repr 0))).
  all: try tc_sel.
  1: null_contra.
  1: { forward_if (temp _t'19 (Vint (Int.repr 0))).
    { exfalso. stc. }
    { forward. forward. entailer!. } }
  try subst sb.
  forward.
  gp_call.
  (* not INVALID_ARGUMENT *)
  forward_if.
  { exfalso. stc. }
  (* READ_FAILED exactly when a read failed *)
  forward.
  gp_by ltac:(destruct Hst as [ (-> & _) | (-> & _) ]; reflexivity).
  (* CAPACITY_EXCEEDED exactly when the 17th function was found *)
  forward.
  gp_by ltac:(destruct Hst as [ (-> & Hf) | (-> & ->) ]; zb).
  (* stopped after at least one read; the result names the last read *)
  forward_if.
  { forward.
    forward_if (temp _t'23 (Vint Int.one)).
    { forward. forward. entailer!. zb. }
    { exfalso. match goal with N: _ |- _ => solve [ apply N; reflexivity ] end. }
    gp_call.
    forward_if (temp _t'24 (Vint Int.one)).
    { forward. entailer!. }
    { b2z_hyps. match goal with E: negb qb = true |- _ => apply negb_true_iff in E end. subst qb.
      repeat match goal with |- context [if false then ?a else ?b] => change (if false then a else b) with b end.
      fw. fw.
      forward_if (temp _t'25 (Vint Int.one)).
      { fw. fw. fw. all: try (entailer!; rewrite ?Int.eq_true; reflexivity). }
      { exfalso. match goal with N: _ |- _ => solve [ apply N; reflexivity ] end. }
      forward_if (temp _t'26 (Vint Int.one)).
      { fw. fw. fw. all: try (entailer!; rewrite ?Int.eq_true; reflexivity). }
      { discriminate. }
      forward_if (temp _t'24 (Vint Int.one)).
      { fw. fw. fw. fw. all: try (entailer!; rewrite ?Int.eq_true; reflexivity). }
      { discriminate. }
      entailer!. }
    gp_call.
    pose proof (dev_free nx wx fx 1 (b2z (st =? 1)) n (loc_of i off) seen v_d) as DF.
    unfold dev_fields, loc_of in DF. simpl fst in DF; simpl snd in DF.
    sep_apply DF.
    free1 EnumSpecs.t_snapshot v_snapshot. free1 EnumSpecs.t_result v_result.
    forward.
    Exists (Int.repr 0). entailer!. }
  { exfalso. stc. }
Qed.
