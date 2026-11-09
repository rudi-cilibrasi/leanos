(* The body of boot_decode_transition: 41 calls of the decoder's transition, each asked words 0..18 and 23..38 of
   the old state, each word into the next row; against Defs.step one answer at a time, up to decode_step_done. *)
Require Import VST.floyd.proofauto.
Require Import LeanosHandoff.handoff.code.
Require Import LeanosHandoff.proof.Defs.
Require Import LeanosHandoff.proof.HandoffSpecs.
Require Import LeanosHandoff.proof.InternalSpecs.
Require Import LeanosHandoff.proof.HdLemmas.
#[local] Existing Instance HandoffSpecs.CS.
Local Open Scope Z_scope.

Lemma body_boot_decode_transition (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_boot_decode_transition (decode_transition_spec Ora).
Proof.
  start_function.
  rename H into IX, H0 into R0, H1 into K0, H2 into KT, H3 into UT, H4 into LS.
  pose proof IX as IX'. destruct IX' as (UM & UA & _).
  pose proof UA as UA'. unfold u32_ok in UA'.
  forward_for_simple_bound 41 (EX q: Z, EX hs: list answer, EX a: list Z,
    PROP (Zlength a = q; Forall u64_ok a;
          run x (start x) (h ++ hs) = Some (if q <? WORDS then Go (ExpectDecodeStep k a) m
                                            else decode_step_done x k a m))
    LOCAL (temp _state sp; temp _info_address (vi (i_address x)); temp _offset (vl (8 * k));
           temp _chunk (vl (Znth k (decoded x m))); temp _terminal (vl (terminal (m_total m) k));
           temp _next np; gvars gv)
    SEP (Ora gv ctx rctx x (h ++ hs); data_at ssh t_state (map vl (current m)) sp;
         data_at nsh t_state (map vl a ++ Zrepeat Vundef (WORDS - q)) np))%assert.
  - Exists (@nil answer) (@nil Z). rewrite app_nil_r. entailer!.
  - Intros.
    match goal with H: run _ _ (h ++ hs) = _ |- _ => rename H into R end.
    rewrite (proj2 (Z.ltb_lt i WORDS)) in R by lia.
    do 35 forward.
    forward_call (gv, ctx, rctx, x, h ++ hs, current m, i_address x, 8 * k, Znth k (decoded x m),
                  terminal (m_total m) k, i).
    { rewrite (next_call_go _ _ _ _ R). cbn [expected]. subst i. reflexivity. }
    Intros v.
    forward.
    Exists (hs ++ [(DecodeStep (current m) (i_address x) (8 * k) (Znth k (decoded x m)) (terminal (m_total m) k) i,
                    v)]) (a ++ [v]).
    entailer!.
    + split; [ rewrite Zlength_app, Zlength_cons, Zlength_nil; lia | ].
      split; [ apply Forall_app; split; auto | ].
      rewrite app_assoc.
      replace (DecodeStep (current m) (i_address x) (8 * k) (Znth k (decoded x m)) (terminal (m_total m) k)
                          (Zlength a))
        with (expected x (ExpectDecodeStep k a) m) by reflexivity.
      rewrite (run_snoc _ _ _ _ _ v R). cbn [step].
      rewrite Zlength_app, Zlength_cons, Zlength_nil. reflexivity.
    + rewrite upd_fill by lia. rewrite <- app_assoc. apply derives_refl.
  - Intros hs a. Exists hs a.
    match goal with H: run _ _ (h ++ hs) = _ |- _ => rename H into R end.
    rewrite Z.ltb_irrefl in R. change (Zrepeat Vundef (41 - 41)) with (@nil val). rewrite app_nil_r.
    entailer!.
Qed.
