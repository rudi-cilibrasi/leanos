(* Law enumeration_exact: main after the scan, when it returned OK: every identity read, no failure, at most 16
   functions found, location 0, and the snapshot publishes exactly the headers the device answered, in the order
   found. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosEnum.harness.enumeration_exact.code.
Require Import LeanosEnum.proof.Defs.
Require LeanosEnum.proof.EnumSpecs.
Require Import LeanosEnum.proof.LawProg LeanosEnum.proof.LawRun LeanosEnum.proof.LawSpecs LeanosEnum.proof.LawSplit
  LeanosEnum.proof.LawLib LeanosEnum.proof.LawOut LeanosEnum.proof.LawMainDefs
  LeanosEnum.proof.LawSeen LeanosEnum.proof.LawPub LeanosEnum.proof.LawAddr.
Local Open Scope Z_scope.

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

Ltac gp_by tac := forward_call (Int.one); try solve [ entailer!; tac ].

(* Entry k of the snapshot and of seen[], as the header found. *)
Ltac hrw fs rest seen k :=
  repeat match goal with
  | |- context [@Znth ?A ?d k (map EnumSpecs.header_val (rev fs) ++ rest)] =>
      replace (@Znth A d k (map EnumSpecs.header_val (rev fs) ++ rest))
        with (hdr_v (fst (Znth k (rev fs))) (words_v (snd (Znth k (rev fs)))) : A)
        by (symmetry; apply (@pub_full d); unfold found in *; lia)
  | |- context [@Znth ?A ?d k seen] =>
      replace (@Znth A d k seen)
        with (hdr_v (fst (Znth k (rev fs))) (words_v (snd (Znth k (rev fs)))) : A)
        by (symmetry; apply (@seen_full d); [ assumption | assumption | unfold found in *; lia | unfold found in *; lia ])
  end;
  unfold hdr_v; simpl fst; simpl snd.

Lemma tail_ok {Espec: OracleKind} gv v_d v_snapshot v_result (rbq sb qb: bool) cnt rb rd rf ro
    (fs: list found) n (l: loc) seen (rest: list (reptype EnumSpecs.t_header)):
  isptr v_d -> isptr v_snapshot -> isptr v_result -> isptr (gv _device_read) ->
  0 <= cnt <= Int.max_unsigned -> 0 <= rb <= Byte.max_unsigned -> 0 <= rd <= Byte.max_unsigned ->
  0 <= rf <= Byte.max_unsigned -> 0 <= ro <= Byte.max_unsigned ->
  (rbq || sb)%bool = false ->
  seen_ok fs seen -> Zlength fs <= CAPACITY -> Forall complete fs -> Forall (fun f => 0 <= fst f < FUNCTIONS) fs ->
  0 <= n <= FUNCTIONS + WORDS * CAPACITY ->
  forall Delta R c, Delta = Delta0 -> R = Post0 -> c = s_after_call ->
  semax Delta
    (PROP ()
     LOCAL (temp _status (Vint (Int.repr 0)); temp _result_arg (if qb then nullval else v_result);
            temp _snapshot_arg (if sb then nullval else v_snapshot);
            temp _read_arg (if rbq then nullval else gv _device_read);
            temp _prior_offset (Vint (Int.repr ro)); temp _prior_function (Vint (Int.repr rf));
            temp _prior_device (Vint (Int.repr rd)); temp _prior_bus (Vint (Int.repr rb));
            temp _prior_count (Vint (Int.repr cnt));
            lvar _result EnumSpecs.t_result v_result; lvar _snapshot EnumSpecs.t_snapshot v_snapshot;
            lvar _d t_device v_d; gvars gv)
     SEP (data_at Tsh EnumSpecs.t_result
            (Vint (Int.repr (if qb then 0 else 0)),
             (Vint (Int.repr (if qb then rb else 0)), (Vint (Int.repr (if qb then rd else 0)),
              (Vint (Int.repr (if qb then rf else 0)), Vint (Int.repr (if qb then ro else 0)))))) v_result;
          data_at Tsh EnumSpecs.t_snapshot
            (Vint (Int.repr (if sb then cnt else Zlength (rev fs))),
             if sb then Zrepeat (Vundef, (Vundef, (Vundef, Zrepeat Vundef 16))) 16
             else map EnumSpecs.header_val (rev fs) ++ rest) v_snapshot;
          TT; func_ptr' (EnumSpecs.read_spec Dev_exact) (gv _device_read); has_ext tt;
          field_at Tsh t_device (DOT _next) (Vint (Int.repr 65536)) v_d;
          field_at Tsh t_device (DOT _word) (Vint (Int.repr 0)) v_d;
          field_at Tsh t_device (DOT _found) (Vint (Int.repr (Zlength fs))) v_d;
          field_at Tsh t_device (DOT _stopped) (Vint (Int.repr 0)) v_d;
          field_at Tsh t_device (DOT _failed) (Vint (Int.repr 0)) v_d;
          field_at Tsh t_device (DOT _reads) (Vint (Int.repr n)) v_d;
          field_at Tsh t_device (DOT _last_bus) (fst l) v_d;
          field_at Tsh t_device (DOT _last_device) (fst (snd l)) v_d;
          field_at Tsh t_device (DOT _last_function) (fst (snd (snd l))) v_d;
          field_at Tsh t_device (DOT _last_offset) (snd (snd (snd l))) v_d;
          field_at Tsh t_device (DOT _seen) seen v_d))
    c R.
Proof.
  intros Pd Ps Pq Pr Rc Rrb Rrd Rrf Rro Inv So Lf Cf Fi Hn Delta R c -> -> ->.
  unfold s_after_call.
  start_tail.
  apply orb_false_iff in Inv. destruct Inv as [Erb Esb].
  unfold FUNCTIONS, WORDS, CAPACITY in *.
  pose proof (Zlength_nonneg fs) as F0.
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
  (* not INVALID_ARGUMENT: the callback and the snapshot are there *)
  forward_if (temp _t'18 (Vint (Int.repr 0))).
  all: try tc_sel.
  1: null_contra.
  1: { forward; try tc_sel. entailer!.
       try subst sb; simpl; destruct v_snapshot; try contradiction; reflexivity. }
  gp_by zb.
  (* the snapshot's count: the functions found *)
  forward_if (temp _t'19 (Vint (Int.repr (Zlength fs)))).
  all: try tc_sel.
  1: null_contra.
  1: { forward_if (temp _t'19 (Vint (Int.repr (Zlength fs)))).
    { forward. forward. forward. entailer!. }
    { exfalso. match goal with N: _ |- _ => solve [ apply N; reflexivity ] end. } }
  try subst sb.
  forward.
  gp_by ltac:(rewrite Zlength_rev, Int.eq_true; reflexivity).
  (* not INVALID_ARGUMENT *)
  forward_if.
  { exfalso. match goal with N: _ |- _ => solve [ inv N ] end. }
  (* no failure, at most 16 found *)
  forward. gp_by zb.
  forward. gp_by zb.
  forward_if.
  { exfalso. discriminate. }
  (* every identity read *)
  forward.
  forward_if (temp _t'27 (Vint Int.one)).
  { forward. forward. entailer!. }
  { exfalso. match goal with N: _ |- _ => solve [ apply N; reflexivity ] end. }
  forward_if (temp _t'28 (Vint Int.one)).
  { forward. forward. entailer!. }
  { discriminate. }
  forward_if (temp _t'29 (Vint Int.one)).
  { forward. forward. entailer!. zb. }
  { discriminate. }
  gp_call.
  (* location 0 *)
  forward_if (temp _t'30 (Vint Int.one)).
  { forward. entailer!. }
  { b2z_hyps. match goal with E: negb qb = true |- _ => apply negb_true_iff in E end. subst qb.
    forward.
    forward_if (temp _t'31 (Vint Int.one)).
    { forward. forward. entailer!. }
    { exfalso. match goal with N: _ |- _ => solve [ apply N; reflexivity ] end. }
    forward_if (temp _t'32 (Vint Int.one)).
    { forward. forward. entailer!. }
    { discriminate. }
    forward_if (temp _t'30 (Vint Int.one)).
    { forward. forward. forward. entailer!. }
    { discriminate. }
    entailer!. }
  gp_call.
  (* the published headers: exactly those the device answered *)
  forward.
  deadvars!.
  match goal with |- semax _ (PROPx ?Ps (LOCALx (temp _i _ :: ?Q) (SEPx ?R))) _ _ =>
    forward_loop
      (EX k: Z, PROPx ((0 <= k <= Zlength fs) :: Ps) (LOCALx (temp _i (Vint (Int.repr k)) :: Q) (SEPx R)))
      continue: (EX k: Z, PROPx ((0 <= k < Zlength fs) :: Ps) (LOCALx (temp _i (Vint (Int.repr k)) :: Q) (SEPx R)))
      break: (PROPx Ps (LOCALx Q (SEPx R)))
  end.
  { Exists 0. entailer!. }
  { Intros k.
    forward.
    forward_if.
    { (* header k *)
      assert (Hk: k < Zlength fs).
      { rewrite ?Zlength_rev in *.
        match goal with
        | E: Int.ltu _ _ = true |- _ => rewrite Int_ltu_repr in E by rep_lia; apply Z.ltb_lt in E
        | _ => idtac
        end.
        match goal with E: k < Int.unsigned (Int.repr _) |- _ => rewrite Int.unsigned_repr in E by rep_lia | _ => idtac end.
        rewrite ?Zlength_rev in *. lia. }
      assert (Hk16: 0 <= k < 16) by lia.
      assert (RF: 0 <= fst (Znth k (rev fs)) < 65536)
        by (apply found_index; [ assumption | unfold found in *; lia ]).
      assert (WF: Zlength (snd (Znth k (rev fs))) = 16)
        by (apply found_words; [ assumption | unfold found in *; lia ]).
      pose proof (bus_range _ RF) as Rb.
      pose proof (dev_range (fst (Znth k (rev fs)))) as Rd.
      pose proof (fn_range (fst (Znth k (rev fs)))) as Rfn.
      forward.
      assert_PROP (field_compatible EnumSpecs.t_snapshot (DOT _headers) v_snapshot) as FCh by entailer!.
      rewrite (headers_addr v_snapshot k FCh Hk16).
      forward; hrw fs rest seen k; try solve [ entailer!; rep_lia ].
      forward; hrw fs rest seen k; try solve [ entailer!; rep_lia ].
      forward_if (temp _t'33 (Vint Int.one)).
      { forward; hrw fs rest seen k; try solve [ entailer!; rep_lia ].
        forward; hrw fs rest seen k; try solve [ entailer!; rep_lia ].
        forward. entailer!. }
      { exfalso. match goal with N: _ |- _ => solve [ apply N; reflexivity ] end. }
      forward_if (temp _t'34 (Vint Int.one)).
      { forward; hrw fs rest seen k; try solve [ entailer!; rep_lia ].
        forward; hrw fs rest seen k; try solve [ entailer!; rep_lia ].
        forward. entailer!. }
      { discriminate. }
      gp_call.
      (* its 16 dwords *)
      match goal with |- semax _ (PROPx ?Ps (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_for_simple_bound 16 (EX w: Z, PROPx Ps (LOCALx Q (SEPx R))) end.
      { entailer!. }
      { forward; hrw fs rest seen k; rewrite ?words_Znth by lia; try solve [ entailer!; rep_lia ].
        forward; hrw fs rest seen k; rewrite ?words_Znth by lia; try solve [ entailer!; rep_lia ].
        gp_call. }
      Exists k. entailer!. }
    { (* the end of the list *)
      forward. entailer!. } }
  { Intros k. forward. Exists (k + 1). entailer!. }
  (* return *)
  pose proof (dev_free 65536 0 (Zlength fs) 0 0 n l seen v_d) as DF. unfold dev_fields in DF.
  sep_apply DF.
  free1 EnumSpecs.t_snapshot v_snapshot. free1 EnumSpecs.t_result v_result.
  forward.
  Exists (Int.repr 0). entailer!.
Qed.
