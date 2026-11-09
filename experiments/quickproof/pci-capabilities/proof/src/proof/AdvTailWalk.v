(* Law capabilities_adversarial: main after the call, when the walker walked (any status but ARGUMENT). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosCaps.harness.capabilities_adversarial.code.
Require Import LeanosCaps.proof.Defs.
Require LeanosCaps.proof.CapsSpecs.
Require Import LeanosCaps.proof.AdvProg LeanosCaps.proof.AdvWalk LeanosCaps.proof.AdvFacts LeanosCaps.proof.AdvSpecs
  LeanosCaps.proof.AdvLib LeanosCaps.proof.AdvMainDefs LeanosCaps.proof.AdvFacts2 LeanosCaps.proof.AdvTables
  LeanosCaps.proof.AdvTailRF.
Local Open Scope Z_scope.

Lemma tail_walk {Espec: OracleKind} gv v_initial v_d v_snapshot v_result v_header_offsets v_masks
    bus dev fn ws cnt ro (qb: bool) h st off caps (rest: list (reptype CapsSpecs.t_cap)):
  isptr v_snapshot -> isptr v_result -> isptr v_d -> isptr v_initial ->
  Zlength ws = 16 -> Forall CapsSpecs.u32_ok ws ->
  0 <= ro <= Byte.max_unsigned -> 0 <= cnt <= Int.max_unsigned ->
  Zlength caps + Zlength rest = 48 ->
  walk ws h = Some (st, off, caps) ->
  forall Delta R c, Delta = Delta0 -> R = Post0 -> c = s_after_call ->
  semax Delta
    (PROP ()
     LOCAL (temp _status (Vint (Int.repr st)); temp _invalid (Vint (Int.repr 0));
            temp _prior_count (Vint (Int.repr cnt));
            temp _result_arg (if qb then nullval else v_result);
            temp _snapshot_arg v_snapshot;
            temp _result_offset (Vint (Int.repr ro));
            lvar _masks (tarray tuint 4) v_masks; lvar _header_offsets (tarray tuchar 4) v_header_offsets;
            lvar _result t_res v_result; lvar _snapshot t_snap v_snapshot; lvar _d t_device v_d;
            lvar _initial t_header v_initial; gvars gv)
     SEP (data_at Tsh t_header (hdr_val bus dev fn ws) v_initial;
          Dev_adv v_d (bus, dev, fn) h;
          data_at Tsh CapsSpecs.t_snapshot (Vint (Int.repr (Zlength caps)), map CapsSpecs.cap_val caps ++ rest)
            v_snapshot;
          data_at Tsh CapsSpecs.t_result
            (Vint (Int.repr (if qb then 0 else st)), Vint (Int.repr (if qb then ro else off))) v_result;
          TT; data_at_ Tsh (tarray tuint 4) v_masks; data_at_ Tsh (tarray tuchar 4) v_header_offsets; has_ext tt))
    c R.
Proof.
  intros until c. intros -> -> ->.
  unfold s_after_call.
  start_tail.
  rename H8 into W.

  pose proof (f_st_range ws h st off caps W) as [Rst Nst]. unfold S_ARGUMENT in Nst.
  pose proof (f_off_range ws h st off caps W) as Roff.
  (* status in range *)
  forward_if (temp _t'22 (Vint Int.one)).
  { forward. entailer!. destruct (zlt 6 st); [ lia | reflexivity ]. }
  { exfalso. lia. }
  gp_call.
  (* the result record *)
  forward.
  forward_if (temp _offset (Vint (Int.repr (if qb then ro else off)))).
  { tc_sel. }
  { match goal with E: (if _ then nullval else _) <> nullval |- _ => apply sel_ne_null in E end. subst qb.
    fw. gp_call. fw. all: try entailer!. }
  { match goal with E: (if _ then nullval else _) = nullval |- _ => apply sel_eq_null in E; [ | auto ] end. subst qb.
    fw. forward_if (temp _t'23 (Vint Int.one)).
    { fw. fw. all: try (entailer!; rewrite Int.eq_true; reflexivity). }
    { exfalso. match goal with N: _ |- _ => solve [ apply N; reflexivity ] end. }
    gp_call. all: try entailer!. }
  forward_call (Int.one).
  { assert (E1: (st =? 1) = false) by (apply Z.eqb_neq; exact Nst).
    entailer!. simpl. rewrite (Int_eq_repr st 1) by rep_lia. rewrite E1. reflexivity. }
  (* the snapshot's count *)
  pose proof (f_caps ws h st off caps W) as Ecaps.
  forward_if (temp _t'24 (Vint (Int.repr (Zlength caps)))).
  { exfalso. match goal with E: v_snapshot = nullval, P: isptr v_snapshot |- _ => rewrite E in P; exact P end. }
  { forward_if (temp _t'24 (Vint (Int.repr (Zlength caps)))).
    { fw. fw. fw. all: try entailer!. }
    { fw. fw. all: try entailer!. rewrite Ecaps by (unfold S_OK; lia). reflexivity. }
    all: try entailer!. }
  fw.
  gp_call.
  (* not ARGUMENT *)
  forward_if.
  { exfalso. lia. }
  (* the tables of the header reads *)
  do 8 fw.
  unfold Dev_adv. Intros offs oks vals.
  match goal with L: log_at _ _ _ _ |- _ => pose proof L as (L1 & L2 & L3 & F) end.
  unfold dev_val, CapsSpecs.bus_of, CapsSpecs.dev_of, CapsSpecs.fn_of. simpl fst; simpl snd.
  pose proof (f_len ws h st off caps W) as Lh1.
  fw.
  forward_call (Int.one).
  { entailer!. simpl. rewrite Int_ltu_repr by rep_lia. destruct (Z.ltb_spec (Zlength h) 1); [ lia | reflexivity ]. }
  fw. fw.
  deadvars!.
  rewrite sub_repr.
  match goal with |- context [data_at Tsh (tarray tuchar 4) ?l v_header_offsets] =>
    replace l with OL by (unfold OL; reflexivity) end.
  match goal with |- context [data_at Tsh (tarray tuint 4) ?l v_masks] =>
    replace l with ML by (unfold ML; rewrite <- repr_m1; reflexivity) end.
  assert (Ans: answers_ok h) by assumption.
  (* the header reads asked for the header offsets *)
  forward.
  loop_from _k (Z.min (Zlength h) 4).
  { Exists 0. entailer!. }
  { Intros k.
    fw.
    forward_if (temp _t'26 (Vint (Int.repr (CapsSpecs.b2z ((k <? Zlength h) && (k <? 4))%bool)))).
    { fw. entailer!. bool_fin. }
    { fw. entailer!. bool_fin. }
    forward_if.
    { match goal with E: ((_ <? _) && (_ <? _))%bool = true |- _ =>
        apply andb_prop in E; destruct E as [Hk1 Hk2]; apply Z.ltb_lt in Hk1; apply Z.ltb_lt in Hk2 end.
      destruct (F k ltac:(lia)) as (Fo & Fok & Fv).
      pose proof (answers_ok_Znth h k Ans ltac:(lia)) as [Ra Rv].
      pose proof (hc_off_range k ltac:(lia)) as [Rh Rh4].
      ldv Fo.
      ldv (Znth_OL k ltac:(lia)).
      rewrite (f_hoff ws h st off caps W k) by lia.
      gp_call.
      forward.
      Exists (k + 1). entailer!. }
    { forward. entailer!. }
    }
  (* every read before the last succeeded, the header ones matching *)
  for_same (Zlength h - 1).
  { entailer!. }
  { destruct (F i ltac:(lia)) as (Fo & Fok & Fv).
    pose proof (f_ok ws h st off caps W i ltac:(lia)) as Oki.
    rewrite Oki in Fok. simpl CapsSpecs.b2z in Fok.
    ldv Fok.
    gp_call.
    if_same.
    { pose proof (answers_ok_Znth h i Ans ltac:(lia)) as [Ra Rv].
      pose proof (hc_off_range i ltac:(lia)) as [Rh Rh4].
      pose proof (hc_mask_range i ltac:(lia)) as Rm.
      ldv (Fv Oki).
      ldv (Znth_ML i ltac:(lia)).
      ldv (Znth_OL i ltac:(lia)).
      pose proof (f_hm ws h st off caps W i ltac:(lia) ltac:(lia)) as Hm. unfold hmatch in Hm.
      unfold hdr_val.
      assert (Bw: 0 <= Int.signed (Int.divs (Int.repr (hc_off i)) (Int.repr 4)) < Zlength ws)
        by (rewrite divs4_repr by lia; rewrite Int.signed_repr by rep_lia; lia).
      forward;
        try rewrite divs4_repr by lia; try rewrite Int.signed_repr by rep_lia; try rewrite Znth_words by lia;
        try solve [ entailer! ].
      { div4_tc. }
      ldv (Znth_ML i ltac:(lia)).
      forward_call (Int.one).
      { entailer!. simpl. rewrite ?and_repr. rewrite Hm. rewrite Int.eq_true. reflexivity. }
      fold (hdr_val bus dev fn ws). entailer!. }
    { forward. all: try entailer!. }
    entailer!.
    }
  deadvars!.
  eapply semax_pre;
    [ | apply (tail_rf gv v_initial v_d v_snapshot v_result v_header_offsets v_masks bus dev fn ws ro qb h st off
                 caps rest offs oks vals); first [ reflexivity | assumption ] ].
  entailer!.
Qed.
