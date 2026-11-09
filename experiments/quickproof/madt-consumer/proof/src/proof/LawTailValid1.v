(* Law consumer_obligations: main's checks after a valid call whose stream was accepted: the byte count and the
   offset, the record walk, the policy (then LawTailValid2). *)
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
Require Import LeanosMadt.proof.LawTailValid2.

(* The prefixes of main's tests of the policy. *)
Definition fiv1 (p: list Z) : bool := (Znth 0 p =? 1) && (Znth 3 p <=? 1).
Definition fiv2 (p: list Z) : bool := fiv1 p && (Znth 4 p <=? 4).
Ltac bool_fin1 := bool_fin_loc ltac:(unfold fiv2, fiv1, five_b, pacc, pac3, pac2, pac1).

Lemma fa_policy: forall v q,
  field_at Ews t_oracle (DOT _policy) v q = data_at Ews (tarray tulong 5) v (field_address t_oracle (DOT _policy) q).
Proof. intros. rewrite field_at_data_at. reflexivity. Qed.

(* qp_assert(e) on an expression e that holds. *)
Ltac gpx := to_branch; forward_call Int.one; try solve [ entailer!; simpl; rewrite ?add64_repr'; cmp_close ].

(* The statement of main after its check of a rejected stream. *)
Definition s_tv1 : statement := ltac:(
  let b := eval cbv delta [f_main] beta iota zeta in (fn_body f_main) in
  match b with
  | context [Ssequence (Ssequence (Sset _t'114 ?e) (Sifthenelse (Etempvar _t'114 tulong) ?th Sskip)) ?rest] =>
      exact (Ssequence rest (Sreturn (Some (Econst_int (Int.repr 0) tint))))
  end).

Lemma tail_v1 {Espec: OracleKind} gv v_out v_observation n bs ob s p stt d off a cc bb:
  isptr v_out -> isptr v_observation -> Zlength bs = n -> ost_ok s -> obs_ok ob ->
  main_ok (bs, ob) (stt, d, off, a, cc, bb) s -> os_rejected s = 0 ->
  forall Delta R c, Delta = Delta0 -> R = Post0 -> c = s_tv1 ->
  semax Delta
    (PROP ()
     LOCAL (temp _status (vl stt); temp _walk (Vint (Int.repr (if walk_b bs then 1 else 0)));
            temp _length (Vlong (Int64.repr n)); temp _o (gv _oracle);
            lvar _out t_result v_out; lvar _observation t_obs v_observation; gvars gv)
     SEP (ofields (gv _oracle) p (Zlength bs) ob s;
          @data_at LCS Tsh t_result (vl stt, (vl d, (vl off, (vl a, (vl cc, vl bb))))) v_out;
          @data_at LCS Tsh t_obs (obs_val ob) v_observation; TT))
    c R.
Proof.
  intros Po Pob Zbn Hok Hob M R0 Delta R c -> -> ->.
  unfold s_tv1. start_tail.
  pose proof M as Mall.
  unfold main_ok in M. destruct M as (Mst & Mz & _ & Mok). destruct (Mok R0) as (Mb & Moff & Mwf & Mwt). clear Mok.
  pose proof Hok as (Rph & Rby & Rwo & Rco & Rre & Lst & Lan & Lnm & Lpo & Lbo & Fst & Fan & Fnm & Fpo & Fbo).
  unfold u64_ok in Rph, Rby, Rwo, Rco, Rre.
  rng_list (os_state s) 1. rng_list (os_policy s) 5.
  unfold ofields. rewrite Mb. Intros.
  assert_PROP (headptr (gv _oracle)) as HO by entailer!.
  freeze_res [_byte; _state; _phase; _word; _policy] F1.
  subst n. subst off.
  (* the byte count and the offset *)
  forward. gpx.
  forward. forward. gpx.
  deadvars!.
  (* the record walk *)
  destruct (walk_b bs) eqn:Wb.
  2: { destruct (Mwf Wb) as (Mph & Mw & Ms & Md). subst stt d.
       forward_if (PROP (False) LOCAL () SEP ()).
       { rewrite Mph, Mw. if1. if1. if1. gp. thaw F1. free_locals. forward. Exists (Int.repr 0). entailer!. }
       { exfalso. match goal with E: Int.repr 0 <> Int.zero |- _ => exact (E eq_refl) end. } }
  destruct (Mwt Wb) as (Mph & Mpf & Mpt). clear Mwt Mwf.
  rewrite Mph.
  match goal with |- semax _ ?Pre _ _ => forward_if Pre end.
  { else_false'. }
  { forward. entailer!. }
  forward. gpx.
  (* the policy *)
  rewrite fa_policy, (fa_offset (gv _oracle) _policy HO ltac:(lnf)).
  change (nested_field_offset t_oracle (DOT _policy)) with 352.
  forward.
  set (pl := os_policy s) in *.
  forward.
  forward_if (temp _t'52 (Vint (Int.repr (Z.b2z (negb (pacc pl)))))).
  { forward.
    forward_if (temp _t'53 (Vint (Int.repr (Z.b2z (pac1 pl))))).
    { forward. forward. entailer!. bool_fin1. }
    { forward. entailer!. bool_fin1. }
    forward_if (temp _t'54 (Vint (Int.repr (Z.b2z (pac2 pl))))).
    { forward. forward. entailer!. bool_fin1. }
    { forward. entailer!. bool_fin1. }
    forward_if (temp _t'55 (Vint (Int.repr (Z.b2z (pac3 pl))))).
    { forward. forward. entailer!. bool_fin1. }
    { forward. entailer!. bool_fin1. }
    forward_if (temp _t'56 (Vint (Int.repr (Z.b2z (pacc pl))))).
    { forward. forward. entailer!. bool_fin1. }
    { forward. entailer!. bool_fin1. }
    forward. entailer!. destruct (pacc pl); reflexivity. }
  { else_false'. }
  destruct (pacc pl) eqn:Pa.
  - (* the policy accepted *)
    match goal with |- semax _ ?Pre _ _ => forward_if Pre end.
    { else_false'. }
    { forward. entailer!. }
    thaw F1. deadvars!.
    change 352 with (nested_field_offset t_oracle (DOT _policy)).
    rewrite <- (fa_offset (gv _oracle) _policy HO ltac:(lnf)), <- fa_policy.
    eapply semax_pre; [ | apply (tail_v2 gv v_out v_observation bs ob s p stt d (Znth 0 (os_state s)) a cc bb); auto ].
    unfold ofields. rewrite Mph, Mb. entailer!.
  - (* the policy rejected *)
    destruct (Mpf eq_refl) as (Es & Ed). clear Mpf Mpt.
    forward_if (PROP (False) LOCAL () SEP ()).
    { forward.
      forward_if (temp _t'46 (Vint (Int.repr (Z.b2z (fiv1 pl))))).
      { forward. forward. entailer!. bool_fin1. }
      { forward. entailer!. bool_fin1. }
      forward_if (temp _t'47 (Vint (Int.repr (Z.b2z (fiv2 pl))))).
      { forward. forward. entailer!. bool_fin1. }
      { forward. entailer!. bool_fin1. }
      forward_if (temp _t'48 (Vint (Int.repr (Z.b2z (five_b pl))))).
      { forward. forward. entailer!. bool_fin1. }
      { forward. entailer!. bool_fin1. }
      forward.
      forward_if (temp _t'49 (Vint (Int.repr (if five_b pl then 5 else 3)))).
      { forward. entailer!. if_b (five_b pl). }
      { forward. entailer!. if_b (five_b pl). }
      forward_if (temp _t'50 (Vint Int.one)).
      { forward_if (temp _t'51 (vl (if five_b pl then Znth 2 pl else 0))).
        { forward. forward. entailer!. if_b (five_b pl). }
        { forward. entailer!. if_b (five_b pl). }
        forward. forward. entailer!. try subst d. destruct (five_b pl); cmp_close. }
      { exfalso. match goal with E: _ <> _ |- _ => apply E end. try subst stt. destruct (five_b pl); reflexivity. }
      gp. thaw F1. free_locals. forward. Exists (Int.repr 0). entailer!. }
    { else_false'. }
Qed.
