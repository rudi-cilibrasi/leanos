(* Law consumer_obligations: the body of the harness's NMI policy export against nmi_spec Ora_law. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosMadt.harness.consumer_obligations.code.
Require Import LeanosMadt.proof.Defs.
Require Import LeanosMadt.proof.MadtSpecs.
Require Import LeanosMadt.proof.LawProg LeanosMadt.proof.LawDefs LeanosMadt.proof.LawFacts LeanosMadt.proof.LawLib.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

Lemma body_nmi: semax_body Vlaw Gexp f_leanos_qotom_madt_nmi_policy_query (nmi_spec Ora_law).
Proof.
  start_function.
  unfold Ora_law. Intros p sh s.
  destruct x as [bytes ob]. simpl fst in *; simpl snd in *.
  rename H0 into Hsh, H1 into Hlen, H2 into Hby, H3 into Hob, H4 into Hok, H5 into Hnmi, H6 into HJ.
  destruct (nmi_call _ _ _ _ _ _ _ H HJ) as (last & state & cur & R & G & -> & ->).
  simpl fst in *; simpl snd in *.
  pose proof G as (P & B & W & S & A & Pp & Rj & Rc & C).
  destruct (Hnmi _ _ Rc) as [Ec En]. subst count nmi.
  pose proof Hok as (Rph & Rby & Rwo & Rco & Rre & Lst & Lan & Lnm & Lpo & Lbo & Fst & Fan & Fnm & Fpo & Fbo).
  pose proof Hob as (Oe & Oc & Oa & Oab & Os & Or).
  unfold u64_ok in Rph, Rby, Rwo, Rco, Rre, Oe, Oc, Oa, Oab, Os, Or.
  rng_list (os_nmi s) 4. pose proof (Zlength_nonneg cur).
  unfold ofields. rewrite P, W, Rj. Intros.
  forward.
  (* the checks *)
  if1. gp. deadvars!.
  if1. if1. if1. if1. if1. gp. deadvars!.
  (* the answer *)
  forward_call tt. Intros v.
  change (vl (Zlength cur)) with (Vlong (Int64.repr (Zlength cur))).
  forward.
  rewrite upd_Znth_map_vl.
  forward_if (PROP () LOCAL (temp _v (vl v))
              SEP (Ora_law gv (bytes, ob) (h ++ [(Nmi (os_count s) (os_nmi s) (o_routing ob) (Zlength cur), v)]))).
  - (* a word of the policy *)
    forward.
    assert (Lw: Zlength cur < 4) by (uns64_hyps; lia).
    unfold Ora_law. Exists p sh (s_policy s v). unfold ofields. ost_cbn. rewrite W, P, Rj.
    entailer!.
    split; [ apply ost_ok_policy; auto; lia | ].
    rewrite (J_snoc_nmi _ _ _ _ _ _ _ _ _ _ R). apply Jp_policy_more; auto.
  - (* its last word *)
    assert (L4: Zlength cur = 4) by (uns64_hyps; lia).
    set (pl := upd_Znth (Zlength cur) (os_policy s) v).
    assert (Lp: Zlength pl = 5) by (unfold pl; rewrite upd_Znth_Zlength; lia).
    assert (Fp: Forall u64_ok pl) by (apply Forall_upd; auto).
    rng_list pl 5.
    forward.
    freeze_but [_policy] false F3.
    forward.
    forward_if (temp _t'8 (Vint (Int.repr (Z.b2z (pac1 pl))))).
    { forward. forward. entailer!. bool_fin. }
    { forward. entailer!. bool_fin. }
    forward_if (temp _t'9 (Vint (Int.repr (Z.b2z (pac2 pl))))).
    { forward. forward. entailer!. bool_fin. }
    { forward. entailer!. bool_fin. }
    forward_if (temp _t'10 (Vint (Int.repr (Z.b2z (pac3 pl))))).
    { forward. forward. entailer!. bool_fin. }
    { forward. entailer!. bool_fin. }
    forward_if (temp _t'11 (Vint (Int.repr (Z.b2z (pacc pl))))).
    { forward. forward. entailer!. rewrite pacc_pac. bool_fin. }
    { forward. entailer!. rewrite pacc_pac. bool_fin. }
    forward_if (temp _t'12 (Vint (Int.repr (if pacc pl then 2 else 3)))).
    { forward. entailer!. bool_fin. }
    { forward. entailer!. bool_fin. }
    thaw F3.
    forward.
    rewrite signed_if by rep_lia. change (Int.signed (Int.repr 0)) with 0.
    unfold Ora_law. Exists p sh (s_policy_done s pl). unfold ofields. ost_cbn. rewrite Rj.
    entailer!.
    split; [ unfold pl; rewrite L4; apply ost_ok_policy_done; auto | ].
    match goal with |- context [Nmi ?a ?b ?c ?k] =>
      replace (Nmi a b c k) with (Nmi a b c (Zlength cur)) by (f_equal; lia) end.
    rewrite (J_snoc_nmi _ _ _ _ _ _ _ _ _ _ R). unfold pl; rewrite L4. apply Jp_policy_done; auto.
  - forward. Exists v. entailer!.
Qed.
