(* Law consumer_obligations: the body of the harness's stream step export against step_spec Ora_law: its checks
   follow from the call the model expects (step_call), and the answer it records keeps the oracle's invariant. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosMadt.harness.consumer_obligations.code.
Require Import LeanosMadt.proof.Defs.
Require Import LeanosMadt.proof.MadtSpecs.
Require Import LeanosMadt.proof.LawProg LeanosMadt.proof.LawDefs LeanosMadt.proof.LawFacts LeanosMadt.proof.LawLib
  LeanosMadt.proof.LawStepTail.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

Lemma body_step: semax_body Vlaw Gexp f_leanos_qotom_madt_stream_byte_step_query (step_spec Ora_law).
Proof.
  start_function.
  unfold Ora_law. Intros p sh s.
  destruct x as [bytes ob]. simpl fst in *; simpl snd in *.
  rename H0 into Hsh, H1 into Hlen, H2 into Hby, H3 into Hob, H4 into Hok, H5 into Hnmi, H6 into HJ.
  destruct (step_call _ _ _ _ _ _ _ _ _ H HJ) as (i & cur & R & G & -> & -> & -> & -> & ->).
  simpl fst in *; simpl snd in *.
  pose proof G as (P & B & W & S & A & Rj & I & C). simpl fst in I.
  subst i state.
  pose proof Hok as (Rph & Rby & Rwo & Rco & Rre & Lst & Lan & Lnm & Lpo & Lbo & Fst & Fan & Fnm & Fpo & Fbo).
  pose proof Hlen as Hl. unfold length_ok in Hl. apply andb_true_iff in Hl as [Hl1 Hl2].
  apply Z.ltb_lt in Hl1. apply Z.leb_le in Hl2. unfold MAX_LENGTH in Hl2.
  pose proof Hob as (Oe & Oc & Oa & Oab & Os & Or).
  unfold u64_ok in Rph, Rby, Rwo, Rco, Rre, Oe, Oc, Oa, Oab, Os, Or.
  assert (Rb: 0 <= Znth (os_byte s) bytes <= Byte.max_unsigned) by (apply Forall_byte_Znth; auto).
  rng_list (os_state s) 12. pose proof (Zlength_nonneg cur).
  unfold ofields. rewrite P, W, Rj. Intros.
  forward.
  (* the checks *)
  if1. if1. gp. deadvars!.
  if1. if1. if1. gp. deadvars!.
  if1. if1. if1. gp. deadvars!.
  if1. if1. if1. gp. deadvars!.
  if1. gp. deadvars!.
  change (vl (os_byte s)) with (Vlong (Int64.repr (os_byte s))).
  to_branch. forward_if (temp _t'13 (Vint Int.one)).
  { forward. forward. forward.
    { entailer!. rewrite Znth_bytes_val by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    rewrite Znth_bytes_val by lia.
    forward. entailer!; cmp_close. }
  { else_false. }
  gp. deadvars!.
  (* the answer *)
  forward_call tt. Intros v.
  change (vl (Zlength cur)) with (Vlong (Int64.repr (Zlength cur))).
  forward.
  rewrite upd_Znth_map_vl.
  destruct (Z.lt_ge_cases (Zlength cur) 15) as [Lw | Lw].
  - (* a word of the transition *)
    forward_if (PROP (False) LOCAL () SEP ()).
    { forward. forward.
      Exists v. unfold Ora_law. Exists p sh (s_answer s v). unfold ofields. ost_cbn. rewrite W, P, Rj.
      entailer!.
      split; [ apply ost_ok_answer; auto; lia | ].
      rewrite (J_snoc_step _ _ _ _ _ _ _ _ R). apply Jp_stream_more; auto; lia. }
    { else_false. }
  - (* its last word *)
    assert (L15: Zlength cur = 15) by lia.
    match goal with |- semax _ ?Pre _ _ => forward_if Pre end.
    { else_false. }
    { forward. entailer!. }
    eapply semax_pre;
      [ | apply (step_tail gv bytes ob h s p sh cur v); first [ reflexivity | assumption | auto ] ].
    unfold ofields, s_store. ost_cbn. rewrite P, W, Rj. entailer!.
Qed.
