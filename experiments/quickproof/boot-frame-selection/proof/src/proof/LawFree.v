(* Law frame_selection_exact: the body of the harness's export leanos_boot_projection_free against free_spec
   Ora_law: its checks follow from the free word the model expects (block b's usable and blocked words and the
   reserved word the overlay just wrote), and the answer moves the law's record as the model's free_done: the next
   block's overlay, or after block 63 the terminal result's word 0. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosFrameSelection.harness.frame_selection_exact.code.
Require Import LeanosFrameSelection.proof.Defs.
Require Import LeanosFrameSelection.proof.FrameSpecs.
Require Import LeanosFrameSelection.proof.LawProg LeanosFrameSelection.proof.LawDefs LeanosFrameSelection.proof.LawFacts
  LeanosFrameSelection.proof.LawLib LeanosFrameSelection.proof.LawLib2 LeanosFrameSelection.proof.LawRows
  LeanosFrameSelection.proof.LawLib3.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[local] Existing Instance LawProg.LCS.

Definition free_fspec : ident * funspec := free_spec Ora_law.

Definition Gfree : funspecs := [gp_assert_spec; any_u64_spec].

(* The free word v of block b. *)
Definition s_free_more (s: lst) (v: Z) : lst :=
  set_expect (set_word (set_block (set_free s (upd_Znth (w_block s) (w_free s) v)) (w_block s + 1)) 1) E_MANIFEST.
Definition s_free_last (s: lst) (v: Z) : lst :=
  set_expect (set_word (set_free s (upd_Znth (w_block s) (w_free s) v)) 0) E_FINISH.

Lemma lst_ok_free: forall s v, lst_ok s -> 0 <= w_block s < BLOCKS -> u64_ok v ->
  lst_ok (set_free s (upd_Znth (w_block s) (w_free s) v)).
Proof.
  intros s v L I V. unfold lst_ok in *; set_unfold; lst_cbn.
  destruct L as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 &
                 A19 & A20).
  split_and; auto. rewrite upd_Znth_Zlength; lia. apply Forall_upd; auto.
Qed.

Lemma J_free: forall x b ms me fw m s v,
  J x (Go (ExpectFree b ms me fw) m) s -> u64_ok v -> i_step x = FTerminal ->
  J x (free_done b ms me (fw ++ [v]) m) (if b + 1 <? BLOCKS then s_free_more s v else s_free_last s v).
Proof.
  intros x b ms me fw m s v (L & Q & G) V F. cbn [go_inv] in G.
  destruct G as (Ge & Gb & Gb' & Gms & Gme & Gfl & Gf).
  pose proof (lst_ok_free s v L ltac:(lia) V) as L'.
  lst_facts L. unfold J, free_done.
  destruct (Z.ltb_spec (b + 1) BLOCKS); split_and.
  - unfold s_free_more, set_expect, set_word, set_block.
    apply (lst_ok_mk (set_free s (upd_Znth (w_block s) (w_free s) v))); set_unfold; lst_cbn; auto;
      unfold u32_ok, u64_ok, E_MANIFEST in *; rep_lia.
  - unfold seq_ok. split; intros G; congruence.
  - cbn [go_inv]. unfold s_free_more; set_unfold; lst_cbn. subst b.
    rewrite Zlength_app, Zlength_cons, Zlength_nil, !sublist_nil. split_and; auto; try lia.
    rewrite <- Gf. list_solve.
  - unfold s_free_last, set_expect, set_word.
    apply (lst_ok_mk (set_free s (upd_Znth (w_block s) (w_free s) v))); set_unfold; lst_cbn; auto;
      unfold u32_ok, u64_ok, E_FINISH in *; rep_lia.
  - unfold seq_ok. split; intros G; congruence.
  - cbn [go_inv]. unfold s_free_last; set_unfold; lst_cbn. subst b.
    split_and; auto; try lia.
    assert (w_block s = 63) by lia. rewrite H0 in *.
    rewrite <- Gf. list_solve.
Qed.

(* ---------------------------------------------------------------------- *)
(* The body                                                                *)
(* ---------------------------------------------------------------------- *)

Lemma body_free: semax_body Vlaw Gfree f_leanos_boot_projection_free free_fspec.
Proof.
  start_function.
  match goal with H: next_call _ _ = _ |- _ => rename H into Nc end.
  ora_open p s.
  destruct (next_go x h p _ Hrun Nc) as (g & m & -> & Ec). cbn [mem_of].
  pose proof (progress_of_run x h _ Ix Ah Hrun) as (Fs & _ & Mm & Km).
  destruct (call_free x g m u bl r (eq_sym Ec)) as (b & ms & me & fw & -> & Eu & Ebl & Er).
  cbn [stage_step] in Fs.
  pose proof HJ as (Hs & Hq & Ge). cbn [go_inv] in Ge.
  destruct Ge as (Ge & Gb & Gb' & Gms & Gme & Gfl & Gf).
  lst_facts Hs. inputs_facts Ix. mem_facts Mm.
  subst u bl r b ms me fw.
  assert (Ru: 0 <= Znth (w_block s) (i_usable x) <= Int64.max_unsigned) by (apply Forall_u64_Znth; auto; lia).
  assert (Rb: 0 <= Znth (w_block s) (i_blocked x) <= Int64.max_unsigned) by (apply Forall_u64_Znth; auto; lia).
  assert (Rr: 0 <= Znth (w_block s) (m_reserved m) <= Int64.max_unsigned) by (apply Forall_u64_Znth; auto; lia).
  unfold lfields. Intros.
  freeze_but [_call; _expect; _block; _word; _usable; _blocked; _reserved_expect; _free_words] (@nil val) F.
  forward. gp.
  { entailer!. all: try (rewrite Ge; reflexivity). }
  forward. vl_temps. forward.
  forward_if (temp _t'1 (Vint Int.one)).
  { forward. vl_temps. forward. forward. entailer!. all: try (rewrite !Int64.eq_true; reflexivity). }
  { else_false. }
  forward_if (temp _t'2 (Vint Int.one)).
  { forward. vl_temps. forward. forward. entailer!. all: try (rewrite !Int64.eq_true; reflexivity). }
  { else_false. }
  forward_call Int.one.
  forward_call tt. Intros v.
  forward. vl_temps. forward.
  forward.
  upd_vl.
  assert (Rn: run x (start x) (h ++ [(Free (Znth (w_block s) (i_usable x)) (Znth (w_block s) (i_blocked x))
                                         (Znth (w_block s) (m_reserved m)), Word v)]) =
              Some (free_done (w_block s) (w_ms s) (w_me s) (sublist 0 (w_block s) (w_free s) ++ [v]) m)).
  { rewrite Ec. rewrite (run_word' x h _ m v Hrun) by (intros c k E; discriminate). reflexivity. }
  pose proof (J_free x (w_block s) (w_ms s) (w_me s) (sublist 0 (w_block s) (w_free s)) m s v HJ ltac:(assumption) (eq_sym Fs))
    as HJ'.
  unfold free_done in Rn, HJ'.
  apply semax_if_seq. forward_if.
  - (* the next block *)
    u64c. assert (Q: w_block s + 1 < BLOCKS) by lia. rewrite (proj2 (Z.ltb_lt _ _) Q) in Rn, HJ'.
    forward. forward. forward. forward. forward.
    Exists v. thaw F.
    unfold s_free_more in HJ'.
    ora_close_tac (Go (ExpectManifest (w_block s + 1) (w_ms s) (w_me s) (sublist 0 (w_block s) (w_free s) ++ [v]) nil) m)
      (set_expect (set_word (set_block (set_free s (upd_Znth (w_block s) (w_free s) v)) (w_block s + 1)) 1) E_MANIFEST).
  - (* after block 63: the terminal result *)
    u64c. assert (Q: BLOCKS <= w_block s + 1) by lia. rewrite (proj2 (Z.ltb_ge _ _) Q) in Rn, HJ'.
    forward. forward. forward.
    Exists v. thaw F.
    unfold s_free_last in HJ'.
    ora_close_tac (Go (ExpectFinish 0 (w_ms s) (w_me s) (sublist 0 (w_block s) (w_free s) ++ [v])) m)
      (set_expect (set_word (set_free s (upd_Znth (w_block s) (w_free s) v)) 0) E_FINISH).
Qed.
