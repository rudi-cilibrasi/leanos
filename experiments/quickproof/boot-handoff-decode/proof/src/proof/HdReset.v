(* The bodies of boot_decode_reset and boot_decode_transition: 41 calls of the decoder's reset or transition, each
   word into the row it fills; against Defs.step one answer at a time, up to decode_init_done or
   decode_step_done. *)
Require Import VST.floyd.proofauto.
Require Import LeanosHandoff.handoff.code.
Require Import LeanosHandoff.proof.Defs.
Require Import LeanosHandoff.proof.HandoffSpecs.
Require Import LeanosHandoff.proof.InternalSpecs.
Require Import LeanosHandoff.proof.HdLemmas.
#[local] Existing Instance HandoffSpecs.CS.
Local Open Scope Z_scope.

Lemma body_boot_decode_reset (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_boot_decode_reset (decode_reset_spec Ora).
Proof.
  start_function.
  rename H into IX, H0 into UT, H1 into R0.
  pose proof IX as IX'. destruct IX' as (UM & UA & _).
  pose proof UM as UM'. pose proof UA as UA'. pose proof UT as UT'. unfold u32_ok in UM', UA', UT'.
  forward_for_simple_bound 41 (EX q: Z, EX hs: list answer, EX a: list Z,
    PROP (Zlength a = q; Forall u64_ok a;
          run x (start x) (h ++ hs) = Some (if q <? WORDS then Go (ExpectDecodeInit a) m else decode_init_done x a m))
    LOCAL (temp _magic (vi (i_magic x)); temp _info_address (vi (i_address x)); temp _total (vi (m_total m));
           temp _target (vl (target x)); temp _state p; gvars gv)
    SEP (Ora gv ctx rctx x (h ++ hs); data_at sh t_state (map vl a ++ Zrepeat Vundef (WORDS - q)) p))%assert.
  - Exists (@nil answer) (@nil Z). rewrite app_nil_r. entailer!.
  - Intros.
    match goal with H: run _ _ (h ++ hs) = _ |- _ => rename H into R end.
    rewrite (proj2 (Z.ltb_lt i WORDS)) in R by lia.
    forward_call (gv, ctx, rctx, x, h ++ hs, i_magic x, i_address x, m_total m, target x, i).
    { rewrite (next_call_go _ _ _ _ R). cbn [expected]. subst i. reflexivity. }
    Intros v.
    forward.
    Exists (hs ++ [(DecodeInit (i_magic x) (i_address x) (m_total m) (target x) i, v)]) (a ++ [v]).
    entailer!.
    + split; [ rewrite Zlength_app, Zlength_cons, Zlength_nil; lia | ].
      split; [ apply Forall_app; split; auto | ].
      rewrite app_assoc.
      replace (DecodeInit (i_magic x) (i_address x) (m_total m) (target x) (Zlength a))
        with (expected x (ExpectDecodeInit a) m) by reflexivity.
      rewrite (run_snoc _ _ _ _ _ v R). cbn [step].
      rewrite Zlength_app, Zlength_cons, Zlength_nil. reflexivity.
    + rewrite upd_fill by lia. rewrite <- app_assoc. apply derives_refl.
  - Intros hs a. Exists hs a.
    match goal with H: run _ _ (h ++ hs) = _ |- _ => rename H into R end.
    rewrite Z.ltb_irrefl in R. change (Zrepeat Vundef (41 - 41)) with (@nil val). rewrite app_nil_r.
    entailer!.
Qed.
