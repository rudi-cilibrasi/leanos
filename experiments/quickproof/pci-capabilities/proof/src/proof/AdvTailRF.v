(* Law capabilities_adversarial: main from the check of READ_FAILED on (the walker walked; the header reads and the
   successful reads before the last are checked). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosCaps.harness.capabilities_adversarial.code.
Require Import LeanosCaps.proof.Defs.
Require LeanosCaps.proof.CapsSpecs.
Require Import LeanosCaps.proof.AdvProg LeanosCaps.proof.AdvWalk LeanosCaps.proof.AdvFacts LeanosCaps.proof.AdvSpecs
  LeanosCaps.proof.AdvLib LeanosCaps.proof.AdvMainDefs LeanosCaps.proof.AdvFacts2 LeanosCaps.proof.AdvTables
  LeanosCaps.proof.AdvTailPC.
Local Open Scope Z_scope.

(* The statement of main from `if (status == PCI_CAPABILITY_READ_FAILED)` on. *)
Definition s_rf : statement := ltac:(
  let b := eval cbv delta [f_main] beta iota zeta in (fn_body f_main) in
  match b with
  | context [Ssequence (Sifthenelse (Ebinop Oeq (Etempvar _status tint) (Econst_int (Int.repr 2) tint) tint) ?a Sskip) ?rest] =>
      exact (Ssequence (Ssequence (Sifthenelse (Ebinop Oeq (Etempvar _status tint) (Econst_int (Int.repr 2) tint) tint)
                                    a Sskip) rest)
               (Sreturn (Some (Econst_int (Int.repr 0) tint))))
  end).

Lemma tail_rf {Espec: OracleKind} gv v_initial v_d v_snapshot v_result v_header_offsets v_masks
    bus dev fn ws ro (qb: bool) h st off caps (rest: list (reptype CapsSpecs.t_cap)) offs oks vals:
  isptr v_result -> Zlength ws = 16 -> Forall CapsSpecs.u32_ok ws -> 0 <= ro <= Byte.max_unsigned ->
  Zlength caps + Zlength rest = 48 ->
  walk ws h = Some (st, off, caps) -> st <> 1 ->
  Zlength h <= 52 -> answers_ok h -> log_at h offs oks vals ->
  forall Delta R c, Delta = Delta0 -> R = Post0 -> c = s_rf ->
  semax Delta
    (PROP ()
     LOCAL (temp _last (Vint (Int.repr (Zlength h - 1)));
            temp _offset (Vint (Int.repr (if qb then ro else off)));
            temp _status (Vint (Int.repr st));
            temp _result_arg (if qb then nullval else v_result);
            lvar _masks (tarray tuint 4) v_masks; lvar _header_offsets (tarray tuchar 4) v_header_offsets;
            lvar _result t_res v_result; lvar _snapshot t_snap v_snapshot; lvar _d t_device v_d;
            lvar _initial t_header v_initial; gvars gv)
     SEP (data_at Tsh t_header (hdr_val bus dev fn ws) v_initial;
          data_at Tsh t_device
            (Vint (Int.repr bus), (Vint (Int.repr dev), (Vint (Int.repr fn),
             (Vint (Int.repr (Zlength h)), (offs, (oks, vals)))))) v_d;
          data_at Tsh CapsSpecs.t_snapshot (Vint (Int.repr (Zlength caps)), map CapsSpecs.cap_val caps ++ rest)
            v_snapshot;
          data_at Tsh CapsSpecs.t_result
            (Vint (Int.repr (if qb then 0 else st)), Vint (Int.repr (if qb then ro else off))) v_result;
          TT; data_at Tsh (tarray tuint 4) ML v_masks; data_at Tsh (tarray tuchar 4) OL v_header_offsets;
          has_ext tt))
    c R.
Proof.
  intros until c. intros -> -> ->.
  unfold s_rf.
  start_tail.
  rename H4 into W. rename H5 into Nst. rename H7 into Ans. rename H8 into LA.
  pose proof LA as (L1 & L2 & L3 & F).
  pose proof (f_len ws h st off caps W) as Lh1.
  pose proof (f_st_range ws h st off caps W) as [Rst _].
  pose proof (f_off_range ws h st off caps W) as Roff.
  destruct (F (Zlength h - 1) ltac:(lia)) as (Fo & Fok & Fv).
  pose proof (answers_ok_Znth h (Zlength h - 1) Ans ltac:(lia)) as [RaL RvL].
  (* READ_FAILED: the last read failed, at the offset the result names *)
  forward_if.
  { pose proof (f_RF ws h st off caps W ltac:(unfold S_READ_FAILED; lia)) as [Lf Lo].
    rewrite Lf in Fok. simpl CapsSpecs.b2z in Fok.
    ldv Fok.
    forward_if (temp _t'27 (Vint Int.one)).
    { forward_if (temp _t'27 (Vint Int.one)).
      { tc_sel. }
      { forward. entailer!. }
      { match goal with E: (if _ then nullval else _) <> nullval |- _ => apply sel_ne_null in E end. subst qb.
        ldv Fo. forward. forward. all: try (entailer!; rewrite Lo, Int.eq_true; reflexivity). }
      all: try entailer!. }
    { exfalso. match goal with N: _ |- _ => solve [ apply N; reflexivity ] end. }
    gp_call.
    free_locals v_initial v_d v_snapshot v_result.
    forward.
    Exists (Int.repr 0). entailer!. }
  (* the last read succeeded *)
  pose proof (f_okL ws h st off caps W ltac:(unfold S_READ_FAILED; lia)) as OkL.
  rewrite OkL in Fok. simpl CapsSpecs.b2z in Fok.
  specialize (Fv OkL).
  ldv Fok.
  gp_call.
  (* HEADER_CHANGED: the last read is a header read that does not match *)
  forward_if.
  { pose proof (f_HC ws h st off caps W ltac:(unfold S_HEADER_CHANGED; lia)) as (Hl & Hn & Ho).
    unfold hmatch in Hn.
    forward_if (temp _t'28 (Vint Int.one)).
    { pose proof (hc_off_range (Zlength h - 1) ltac:(lia)) as [Rh Rh4].
      pose proof (hc_mask_range (Zlength h - 1) ltac:(lia)) as Rm.
      ldv Fv.
      ldv (Znth_ML (Zlength h - 1) ltac:(lia)).
      ldv (Znth_OL (Zlength h - 1) ltac:(lia)).
      unfold hdr_val.
      assert (Bw: 0 <= Int.signed (Int.divs (Int.repr (hc_off (Zlength h - 1))) (Int.repr 4)) < Zlength ws)
        by (rewrite divs4_repr by lia; rewrite Int.signed_repr by rep_lia; lia).
      forward;
        try rewrite divs4_repr by lia; try rewrite Int.signed_repr by rep_lia; try rewrite Znth_words by lia;
        try solve [ entailer! ].
      { div4_tc. }
      assert (Rw: 0 <= Znth (hc_off (Zlength h - 1) / 4) ws <= Int.max_unsigned) by (apply words_Znth; auto; lia).
      ldv (Znth_ML (Zlength h - 1) ltac:(lia)).
      forward.
      fold (hdr_val bus dev fn ws).
      entailer!. rewrite Int_eq_repr by (apply land_range; rep_lia).
      destruct (Z.eqb_spec (Z.land (aval (Znth (Zlength h - 1) h)) (hc_mask (Zlength h - 1)))
                           (Z.land (Znth (hc_off (Zlength h - 1) / 4) ws) (hc_mask (Zlength h - 1))));
        [ contradiction | reflexivity ]. }
    { exfalso. lia. }
    gp_call.
    forward_if (temp _t'29 (Vint Int.one)).
    { tc_sel. }
    { forward. entailer!. }
    { match goal with E: (if _ then nullval else _) <> nullval |- _ => apply sel_ne_null in E end. subst qb.
      ldv Fo. forward. all: try (entailer!; rewrite Ho, Int.eq_true; reflexivity). }
    gp_call.
    free_locals v_initial v_d v_snapshot v_result.
    forward.
    Exists (Int.repr 0). entailer!. }
  (* at least the four header reads *)
  pose proof (f_n4 ws h st off caps W ltac:(unfold S_READ_FAILED; lia) ltac:(unfold S_HEADER_CHANGED; lia)) as N4.
  fw.
  forward_call (Int.one).
  { entailer!. simpl. rewrite Int_ltu_repr by rep_lia. destruct (Z.ltb_spec (Zlength h) 4); [ lia | reflexivity ]. }
  (* the last read: not an absent capability header (unless ABSENT), or the fourth header read matching *)
  if_same.
  { pose proof (f_last_abs ws h st off caps W ltac:(unfold S_READ_FAILED; lia) ltac:(unfold S_HEADER_CHANGED; lia))
      as Abs.
    ldv Fv.
    ldv (Znth_ML 3 ltac:(lia)). change (hc_mask 3) with 255.
    forward_if (temp _t'30 (Vint Int.one)).
    { forward. entailer!. }
    { forward. entailer!.
      destruct (Z.eq_dec st 6) as [E6|N6]; [ subst st; reflexivity | ].
      exfalso. apply (Abs ltac:(unfold S_ABSENT; lia) ltac:(lia)).
      match goal with E: Int.and _ _ = Int.repr 255 |- _ =>
        rewrite and_repr in E; apply repr_eq_unsigned in E; [ exact E | apply land_range; rep_lia | rep_lia ] end. }
    gp_call.
    all: try entailer!. }
  { pose proof (f_last_hm ws h st off caps W ltac:(unfold S_READ_FAILED; lia) ltac:(unfold S_HEADER_CHANGED; lia)
      ltac:(lia)) as Hm.
    unfold hmatch in Hm.
    pose proof (hc_off_range (Zlength h - 1) ltac:(lia)) as [Rh Rh4].
    pose proof (hc_mask_range (Zlength h - 1) ltac:(lia)) as Rm.
    ldv Fv.
    ldv (Znth_ML (Zlength h - 1) ltac:(lia)).
    ldv (Znth_OL (Zlength h - 1) ltac:(lia)).
    unfold hdr_val.
    assert (Bw: 0 <= Int.signed (Int.divs (Int.repr (hc_off (Zlength h - 1))) (Int.repr 4)) < Zlength ws)
      by (rewrite divs4_repr by lia; rewrite Int.signed_repr by rep_lia; lia).
    forward;
      try rewrite divs4_repr by lia; try rewrite Int.signed_repr by rep_lia; try rewrite Znth_words by lia;
      try solve [ entailer! ].
    { div4_tc. }
    ldv (Znth_ML (Zlength h - 1) ltac:(lia)).
    forward_call (Int.one).
    { entailer!. simpl. rewrite ?and_repr. rewrite Hm. rewrite Int.eq_true. reflexivity. }
    all: try (fold (hdr_val bus dev fn ws); entailer!). }
  all: try entailer!.
  (* ABSENT: the last read is a list read of an absent header, at the offset the result names *)
  forward_if.
  { pose proof (f_AB ws h st off caps W ltac:(unfold S_ABSENT; lia)) as (Al & Av & Ao).
    forward_if (temp _t'31 (Vint Int.one)).
    { ldv Fv. forward. entailer!. rewrite ?and_repr. rewrite Av. rewrite Int.eq_true. reflexivity. }
    { exfalso. lia. }
    forward_if (temp _t'32 (Vint Int.one)).
    { forward_if (temp _t'32 (Vint Int.one)).
      { tc_sel. }
      { forward. entailer!. }
      { match goal with E: (if _ then nullval else _) <> nullval |- _ => apply sel_ne_null in E end. subst qb.
        ldv Fo. forward. forward. all: try (entailer!; rewrite Ao, Int.eq_true; reflexivity). }
      all: try entailer!. }
    { discriminate. }
    gp_call.
    free_locals v_initial v_d v_snapshot v_result.
    forward.
    Exists (Int.repr 0). entailer!. }
  deadvars!.
  eapply semax_pre;
    [ | apply (tail_pc gv v_initial v_d v_snapshot v_result v_header_offsets v_masks bus dev fn ws ro qb h st off
                 caps rest offs oks vals); first [ reflexivity | assumption ] ].
  unfold pc_pre. entailer!.
Qed.
