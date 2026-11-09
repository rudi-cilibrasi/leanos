(* Law capabilities_adversarial: main for the status OK (the walker published the list). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosCaps.harness.capabilities_adversarial.code.
Require Import LeanosCaps.proof.Defs.
Require LeanosCaps.proof.CapsSpecs.
Require Import LeanosCaps.proof.AdvProg LeanosCaps.proof.AdvWalk LeanosCaps.proof.AdvFacts LeanosCaps.proof.AdvSpecs
  LeanosCaps.proof.AdvLib LeanosCaps.proof.AdvMainDefs LeanosCaps.proof.AdvFacts2 LeanosCaps.proof.AdvTables.
Local Open Scope Z_scope.

(* The statement of main from the check of the result's offset on success on. *)
Definition s_ok : statement := ltac:(
  let b := eval cbv delta [f_main] beta iota zeta in (fn_body f_main) in
  match b with
  | context [Ssequence (Ssequence (Sifthenelse ?c (Sset _t'40 ?a) ?b) ?d) ?e] =>
      exact (Ssequence (Ssequence (Ssequence (Sifthenelse c (Sset _t'40 a) b) d) e)
               (Sreturn (Some (Econst_int (Int.repr 0) tint))))
  end).

Definition ok_pre (gv: globals) (v_initial v_d v_snapshot v_result v_header_offsets v_masks: val)
    (bus dev fn: Z) (ws: list Z) (ro: Z) (qb: bool) (h: list answer) (st off: Z) (caps: list (Z * Z))
    (rest: list (reptype CapsSpecs.t_cap)) (offs oks vals: list val) : environ -> mpred :=
    (PROP ()
     LOCAL (temp _offset (Vint (Int.repr (if qb then ro else off)));
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
          has_ext tt)).

(* A counting loop over j whose body keeps the state. *)
Ltac for_same_j n :=
  match goal with |- semax _ (PROPx ?Ps (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_for_simple_bound n (EX j: Z, PROPx Ps (LOCALx Q (SEPx R)))
  end.

(* The i-th published header, from Znth i caps = (p, v). *)
Ltac snap_rw caps rest i p v E :=
  repeat match goal with |- context [@Znth ?A ?d i (map CapsSpecs.cap_val caps ++ rest)] =>
    replace (@Znth A d i (map CapsSpecs.cap_val caps ++ rest)) with ((Vint (Int.repr p), Vint (Int.repr v)) : A)
      by (rewrite Znth_app1 by (rewrite Zlength_map; lia); rewrite Znth_map by lia; rewrite E; reflexivity)
  end;
  cbv beta iota zeta.

Lemma tail_ok {Espec: OracleKind} gv v_initial v_d v_snapshot v_result v_header_offsets v_masks
    bus dev fn ws ro (qb: bool) h st off caps (rest: list (reptype CapsSpecs.t_cap)) offs oks vals:
  isptr v_result -> Zlength ws = 16 -> Forall CapsSpecs.u32_ok ws -> 0 <= ro <= Byte.max_unsigned ->
  Zlength caps + Zlength rest = 48 ->
  walk ws h = Some (st, off, caps) -> st = S_OK ->
  Zlength h <= 52 -> answers_ok h -> log_at h offs oks vals ->
  forall Delta R c, Delta = Delta0 -> R = Post0 -> c = s_ok ->
  semax Delta
    (ok_pre gv v_initial v_d v_snapshot v_result v_header_offsets v_masks bus dev fn ws ro qb h st off caps rest
       offs oks vals)
    c R.
Proof.
  intros until c. intros -> -> ->.
  unfold s_ok, ok_pre.
  start_tail.
  rename H4 into W. rename H5 into E0. rename H6 into Lh52. rename H7 into Ans. rename H8 into LA.
  pose proof LA as (L1 & L2 & L3 & F).
  pose proof (f_OK ws h st off caps W E0) as (Off0 & Lhc & Lc48 & Hend & Hcaps).
  pose proof (f_hdr4 ws h st off caps W E0) as Hd4.
  pose proof (Zlength_nonneg caps) as Lc0.
  (* the result's offset is 0 *)
  forward_if (temp _t'40 (Vint Int.one)).
  { tc_sel. }
  { forward. entailer!. }
  { match goal with E: (if _ then nullval else _) <> nullval |- _ => apply sel_ne_null in E end. subst qb.
    forward. all: try (entailer!; rewrite Off0; reflexivity). }
  gp_call.
  (* count <= 48 and reads == 4 + count *)
  fw.
  forward_if (temp _t'41 (Vint Int.one)).
  { fw. forward. all: try (entailer!; rewrite add_repr, Int_eq_repr by rep_lia; rewrite Lhc, Z.eqb_refl; reflexivity). }
  { exfalso. lia. }
  gp_call.
  (* the four header reads, at the header offsets, successful and matching *)
  for_same 4.
  { entailer!. }
  { destruct (Hd4 i ltac:(lia)) as [Ok_i Hm_i]. unfold hmatch in Hm_i.
    destruct (F i ltac:(lia)) as (Fo & Fok & Fv).
    rewrite Ok_i in Fok. simpl CapsSpecs.b2z in Fok. specialize (Fv Ok_i).
    pose proof (f_hoff ws h st off caps W i ltac:(lia) ltac:(lia)) as Ho_i.
    pose proof (answers_ok_Znth h i Ans ltac:(lia)) as [Ra Rv].
    pose proof (hc_off_range i ltac:(lia)) as [Rh Rh4].
    pose proof (hc_mask_range i ltac:(lia)) as Rm.
    ldv Fo. rewrite Ho_i.
    ldv (Znth_OL i ltac:(lia)).
    forward_if (temp _t'42 (Vint Int.one)).
    { ldv Fok. forward. entailer!. }
    { exfalso. auto. }
    gp_call.
    ldv Fv.
    ldv (Znth_ML i ltac:(lia)).
    ldv (Znth_OL i ltac:(lia)).
    unfold hdr_val.
    assert (Bw: 0 <= Int.signed (Int.divs (Int.repr (hc_off i)) (Int.repr 4)) < Zlength ws)
      by (rewrite divs4_repr by lia; rewrite Int.signed_repr by rep_lia; lia).
    forward;
      try rewrite divs4_repr by lia; try rewrite Int.signed_repr by rep_lia; try rewrite Znth_words by lia;
      try solve [ entailer! ].
    { div4_tc. }
    ldv (Znth_ML i ltac:(lia)).
    forward_call (Int.one).
    { entailer!. simpl. rewrite ?and_repr. rewrite Hm_i. rewrite Int.eq_true. reflexivity. }
    fold (hdr_val bus dev fn ws). entailer!. }
  (* next = the list head *)
  deadvars!.
  unfold hdr_val.
  assert (W1: 0 <= Znth 1 ws <= Int.max_unsigned) by (apply words_Znth; auto; lia).
  assert (W13: 0 <= Znth 13 ws <= Int.max_unsigned) by (apply words_Znth; auto; lia).
  fw.
  forward_if (temp _t'43 (Vint (Int.repr (list_head ws)))).
  { fw. forward.
    entailer!. unfold list_head.
    destruct (Z.land (Znth 1 ws) 1048576 =? 0) eqn:E; [ | reflexivity ].
    apply Z.eqb_eq in E. exfalso.
    match goal with N: _ <> _ |- _ => apply N end. rewrite ?and_repr, E. reflexivity. }
  { forward. entailer!. unfold list_head.
    match goal with N: _ = _ |- _ => rewrite ?and_repr in N; apply repr_eq_unsigned in N;
      [ rewrite N; reflexivity | apply land_range; auto | rep_lia ] end. }
  forward.
  fold (hdr_val bus dev fn ws).
  deadvars!.
  (* the published headers: the list from the head *)
  match goal with |- semax _ (PROPx ?Ps (LOCALx (temp _next _ :: ?Q) (SEPx ?R))) _ _ =>
    forward_for_simple_bound (Zlength caps)
      (EX i: Z, PROPx Ps (LOCALx (temp _next (Vint (Int.repr (hptr ws h i))) :: Q) (SEPx R))) end.
  { rewrite hptr_0. entailer!. }
  { destruct (Hcaps i ltac:(lia)) as (Ci & P64 & P3 & Pd & Poff & Pok & Pabs & Pnext).
    pose proof (hptr_range ws h i ltac:(lia) ltac:(lia)) as Rp.
    pose proof (answers_ok_Znth h (4 + i) Ans ltac:(lia)) as [Ra4 Rv4].
    forward; snap_rw caps rest i (hptr ws h i) (aval (Znth (4 + i) h)) Ci;
      try solve [ entailer!; rep_lia ].
    forward; snap_rw caps rest i (hptr ws h i) (aval (Znth (4 + i) h)) Ci;
      try solve [ entailer!; rep_lia ].
    forward_if (temp _t'44 (Vint Int.one)).
    { forward. entailer!. bool_fin. }
    { exfalso. auto. }
    forward_if (temp _t'45 (Vint Int.one)).
    { forward. entailer!. rewrite ?and_repr, P3. reflexivity. }
    { discriminate. }
    gp_call.
    (* distinct from the headers before *)
    for_same_j i.
    { entailer!. }
    { rename i0 into j. destruct (Hcaps j ltac:(lia)) as (Cj & _ & _ & _ & _ & _ & _ & _).
      pose proof (hptr_range ws h j ltac:(lia) ltac:(lia)) as Rpj.
      forward; snap_rw caps rest j (hptr ws h j) (aval (Znth (4 + j) h)) Cj;
        try solve [ entailer!; rep_lia ].
      forward_call (Int.one).
      { entailer!. simpl. rewrite Int_eq_repr by rep_lia.
        rewrite (proj2 (Z.eqb_neq _ _) (Pd j ltac:(lia))). reflexivity. }
      entailer!. }
    (* the device answered the read at the offset with the raw word *)
    destruct (F (4 + i) ltac:(lia)) as (Fo4 & Fok4 & Fv4).
    rewrite Pok in Fok4. simpl CapsSpecs.b2z in Fok4. specialize (Fv4 Pok).
    ldv Fo4. rewrite Poff.
    forward_if (temp _t'46 (Vint Int.one)).
    { ldv Fok4. forward. entailer!. }
    { exfalso. auto. }
    forward_if (temp _t'47 (Vint Int.one)).
    { ldv Fv4. forward. all: try (entailer!; rewrite Int.eq_true; reflexivity). }
    { discriminate. }
    gp_call.
    (* not an absent header *)
    forward_call (Int.one).
    { entailer!. simpl. rewrite ?and_repr. rewrite Int_eq_repr by (first [ apply land_range; rep_lia | rep_lia ]).
      rewrite (proj2 (Z.eqb_neq _ _) Pabs). reflexivity. }
    (* next = the header's next pointer *)
    forward.
    entailer!. rewrite Pnext. unfold nptr. rewrite nptr_repr by rep_lia. reflexivity. }
  (* the list ends *)
  forward_call (Int.one).
  { entailer!. simpl. rewrite Hend. reflexivity. }
  free_locals v_initial v_d v_snapshot v_result.
  forward.
  Exists (Int.repr 0). entailer!.
Qed.
