(* Law consumer_obligations: the body of the harness's stream finish export against finish_spec Ora_law. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosMadt.harness.consumer_obligations.code.
Require Import LeanosMadt.proof.Defs.
Require Import LeanosMadt.proof.MadtSpecs.
Require Import LeanosMadt.proof.LawProg LeanosMadt.proof.LawDefs LeanosMadt.proof.LawFacts LeanosMadt.proof.LawLib.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

Lemma body_finish: semax_body Vlaw Gexp f_leanos_qotom_madt_stream_finish_query (finish_spec Ora_law).
Proof.
  start_function.
  unfold Ora_law. Intros p sh s.
  destruct x as [bytes ob]. simpl fst in *; simpl snd in *.
  rename H0 into Hsh, H1 into Hlen, H2 into Hby, H3 into Hob, H4 into Hok, H5 into Hnmi, H6 into HJ.
  destruct (finish_call _ _ _ _ _ _ _ _ _ _ _ _ _ H HJ)
    as (last & cur & R & G & -> & -> & -> & -> & -> & -> & -> & -> & ->).
  simpl fst in *; simpl snd in *.
  pose proof G as (P & B & W & S & A & Pp & Bb & Rj & Rc & C).
  subst state last.
  pose proof Hok as (Rph & Rby & Rwo & Rco & Rre & Lst & Lan & Lnm & Lpo & Lbo & Fst & Fan & Fnm & Fpo & Fbo).
  pose proof Hlen as Hl. unfold length_ok in Hl. apply andb_true_iff in Hl as [Hl1 Hl2].
  apply Z.ltb_lt in Hl1. apply Z.leb_le in Hl2. unfold MAX_LENGTH in Hl2.
  pose proof Hob as (Oe & Oc & Oa & Oab & Os & Or).
  unfold u64_ok in Rph, Rby, Rwo, Rco, Rre, Oe, Oc, Oa, Oab, Os, Or.
  rng_list (os_state s) 12. rng_list (os_answer s) 3. pose proof (Zlength_nonneg cur).
  unfold ofields. rewrite P, W, Rj. Intros.
  forward.
  (* the checks *)
  if1. gp. deadvars!.
  if1. gp. deadvars!.
  if1. if1. if1. gp. deadvars!.
  if1. if1. if1. gp. deadvars!.
  if1. if1. if1. gp. deadvars!.
  if1. if1. if1. if1. if1. gp. deadvars!.
  (* the answer *)
  forward_call tt. Intros v.
  change (vl (Zlength cur)) with (Vlong (Int64.repr (Zlength cur))).
  forward.
  rewrite upd_Znth_map_vl.
  forward_if (PROP () LOCAL (temp _v (vl v))
              SEP (Ora_law gv (bytes, ob)
                     (h ++ [(Finish (Znth 1 (os_answer s)) (Znth 2 (os_answer s)) (os_state s) (44 + Zlength bytes)
                               (o_executing ob) (o_cpuid_edx ob) (o_available ob) (o_apic_base ob) (o_sample_id ob)
                               (Zlength cur), v)]))).
  - (* a word of the bound *)
    forward.
    assert (Lw: Zlength cur < 5) by (uns64_hyps; lia).
    unfold Ora_law. Exists p sh (s_bound s v). unfold ofields. ost_cbn. rewrite W, P, Rj.
    entailer!.
    split; [ apply ost_ok_bound; auto; lia | ].
    rewrite (J_snoc_finish _ _ _ _ _ _ _ _ R). apply Jp_bound_more; auto.
  - (* its last word *)
    assert (L5: Zlength cur = 5) by (uns64_hyps; lia).
    forward. forward.
    unfold Ora_law. Exists p sh (s_bound_done s (upd_Znth 5 (os_bound s) v)). unfold ofields. ost_cbn.
    rewrite Rj, L5.
    entailer!.
    split; [ apply ost_ok_bound_done; auto | ].
    match goal with |- context [Finish ?a ?b ?c ?d ?e ?f ?g ?i ?j ?k] =>
      replace (Finish a b c d e f g i j k) with (Finish a b c d e f g i j (Zlength cur)) by (f_equal; lia) end.
    rewrite (J_snoc_finish _ _ _ _ _ _ _ _ R). apply Jp_bound_done; auto.
  - forward. Exists v. entailer!.
Qed.
