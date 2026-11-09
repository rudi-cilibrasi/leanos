(* Law frame_selection_exact: the global `law` as main finds it, all zeros, as its fields (lzero), proved once
   (VST's unfold_data_at on the struct is slow), its padding dropped. *)
Require Import VST.floyd.proofauto.
Require Import LeanosFrameSelection.harness.frame_selection_exact.code.
Require Import LeanosFrameSelection.proof.Defs.
Require Import LeanosFrameSelection.proof.FrameSpecs.
Require Import LeanosFrameSelection.proof.LawProg LeanosFrameSelection.proof.LawDefs.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

Definition z64 (n: Z) : list val := Zrepeat (vl 0) n.

(* struct law as main finds it (all zeros), field by field: its 3552 zero bytes split at the fields' offsets (the
   padding between fields dropped), each field's bytes its zero value. *)
Definition lzero (q: val) : mpred :=
 (field_at Ews t_law (DOT _call) (vi 0) q *
  field_at Ews t_law (DOT _take_next) (vi 0) q *
  field_at Ews t_law (DOT _selected) (vl 0) q *
  field_at Ews t_law (DOT _selected_manifest) (vl 0) q *
  field_at Ews t_law (DOT _published) (vl 0) q *
  field_at Ews t_law (DOT _next) (vl 0) q *
  field_at Ews t_law (DOT _running) (vi 0) q *
  field_at Ews t_law (DOT _manifest) (z64 18) q *
  field_at Ews t_law (DOT _decoded) (z64 41) q *
  field_at Ews t_law (DOT _usable) (z64 64) q *
  field_at Ews t_law (DOT _blocked) (z64 64) q *
  field_at Ews t_law (DOT _reserved_expect) (z64 64) q *
  field_at Ews t_law (DOT _terminal_expect) (z64 9) q *
  field_at Ews t_law (DOT _states_expect) (Zrepeat (z64 41) 2) q *
  field_at Ews t_law (DOT _publication_expect) (z64 5) q *
  field_at Ews t_law (DOT _rescan_expect) (z64 5) q *
  field_at Ews t_law (DOT _selected_expect) (vl 0) q *
  field_at Ews t_law (DOT _manifest_expect) (vl 0) q *
  field_at Ews t_law (DOT _next_expect) (vl 0) q *
  field_at Ews t_law (DOT _decoder_expect) (vi 0) q *
  field_at Ews t_law (DOT _states) nullval q *
  field_at Ews t_law (DOT _step) (vi 0) q *
  field_at Ews t_law (DOT _expect) (vi 0) q *
  field_at Ews t_law (DOT _verdict) (vi 0) q *
  field_at Ews t_law (DOT _block) (vl 0) q *
  field_at Ews t_law (DOT _word) (vl 0) q *
  field_at Ews t_law (DOT _candidate) (vl 0) q *
  field_at Ews t_law (DOT _scan) (vi 0) q *
  field_at Ews t_law (DOT _manifest_status) (vl 0) q *
  field_at Ews t_law (DOT _manifest_error) (vl 0) q *
  field_at Ews t_law (DOT _free_words) (z64 64) q *
  field_at Ews t_law (DOT _candidate_manifest) (vl 0) q *
  field_at Ews t_law (DOT _first) (vl 0) q *
  field_at Ews t_law (DOT _first_manifest) (vl 0) q *
  field_at Ews t_law (DOT _second) (vl 0) q *
  field_at Ews t_law (DOT _answer) (z64 4) q *
  field_at Ews t_law (DOT _scrubbed) (vi 0) q)%logic.

Lemma mz_take: forall sh b o n k o' n', o' = o + k -> n' = n - k -> 0 <= k <= n -> 0 <= o -> o + n < Ptrofs.modulus ->
  mapsto_zeros n sh (Vptr b (Ptrofs.repr o)) |--
  (mapsto_zeros k sh (Vptr b (Ptrofs.repr o)) * mapsto_zeros n' sh (Vptr b (Ptrofs.repr o')))%logic.
Proof.
  intros sh b o n k o' n' E1 E2 K O M. subst o' n'.
  replace n with (k + (n - k)) at 1 by lia.
  rewrite aggregate_pred.mapsto_zeros_split by (unfold Ptrofs.modulus in *; lia). apply derives_refl.
Qed.

Ltac zv := apply JMeq_eq; eapply JMeq_trans; [ apply JMeq_zero_val_zero_val' | ]; vm_compute; apply JMeq_refl.

Ltac lnf := split; [ exact I | simpl; repeat (first [ left; reflexivity | right ]) ].

Lemma zfield: forall b f ofs sz (v: reptype (nested_field_type t_law (DOT f))),
  nested_field_offset t_law (DOT f) = ofs -> sizeof (nested_field_type t_law (DOT f)) = sz ->
  zero_val (nested_field_type t_law (DOT f)) = v ->
  complete_legal_cosu_type (nested_field_type t_law (DOT f)) = true ->
  fully_nonvolatile (rank_type cenv_cs (nested_field_type t_law (DOT f))) (nested_field_type t_law (DOT f)) = true ->
  legal_nested_field t_law (DOT f) ->
  field_compatible t_law nil (Vptr b Ptrofs.zero) ->
  mapsto_zeros sz Ews (Vptr b (Ptrofs.repr ofs)) |-- field_at Ews t_law (DOT f) v (Vptr b Ptrofs.zero).
Proof.
  intros b f ofs sz v Ho Hs Hv Hc Hn Hl FC. subst ofs sz v.
  assert (FC': field_compatible t_law (DOT f) (Vptr b Ptrofs.zero)).
  { unfold field_compatible in *. destruct FC as (F1 & F2 & F3 & F4 & F5).
    split; [ exact F1 | split; [ exact F2 | split; [ exact F3 | split; [ exact F4 | exact Hl ] ] ] ]. }
  rewrite field_at_data_at.
  pose proof (field_compatible_nested_field _ _ _ FC') as FN.
  unfold field_address in *. rewrite if_true in * by auto. simpl offset_val in *.
  rewrite Ptrofs.add_zero_l in *.
  apply mapsto_zero_data_at_zero; auto.
Qed.

Lemma law_zero_b: forall b, field_compatible t_law nil (Vptr b Ptrofs.zero) ->
  mapsto_zeros 3552 Ews (Vptr b (Ptrofs.repr 0)) |-- (lzero (Vptr b Ptrofs.zero) * TT)%logic.
Proof.
  intros b FC.
  sep_apply (mz_take Ews b 0 3552 4 4 3548 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _call 0 4 (vi 0) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 4 3548 4 8 3544 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _take_next 4 4 (vi 0) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 8 3544 8 16 3536 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _selected 8 8 (vl 0) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 16 3536 8 24 3528 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _selected_manifest 16 8 (vl 0) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 24 3528 8 32 3520 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _published 24 8 (vl 0) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 32 3520 8 40 3512 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _next 32 8 (vl 0) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 40 3512 4 44 3508 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _running 40 4 (vi 0) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 44 3508 4 48 3504 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (mz_take Ews b 48 3504 144 192 3360 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _manifest 48 144 (z64 18) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 192 3360 328 520 3032 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _decoded 192 328 (z64 41) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 520 3032 512 1032 2520 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _usable 520 512 (z64 64) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 1032 2520 512 1544 2008 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _blocked 1032 512 (z64 64) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 1544 2008 512 2056 1496 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _reserved_expect 1544 512 (z64 64) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 2056 1496 72 2128 1424 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _terminal_expect 2056 72 (z64 9) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 2128 1424 656 2784 768 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _states_expect 2128 656 (Zrepeat (z64 41) 2) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 2784 768 40 2824 728 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _publication_expect 2784 40 (z64 5) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 2824 728 40 2864 688 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _rescan_expect 2824 40 (z64 5) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 2864 688 8 2872 680 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _selected_expect 2864 8 (vl 0) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 2872 680 8 2880 672 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _manifest_expect 2872 8 (vl 0) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 2880 672 8 2888 664 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _next_expect 2880 8 (vl 0) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 2888 664 4 2892 660 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _decoder_expect 2888 4 (vi 0) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 2892 660 4 2896 656 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (mz_take Ews b 2896 656 8 2904 648 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _states 2896 8 (nullval) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 2904 648 4 2908 644 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _step 2904 4 (vi 0) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 2908 644 4 2912 640 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _expect 2908 4 (vi 0) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 2912 640 4 2916 636 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _verdict 2912 4 (vi 0) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 2916 636 4 2920 632 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (mz_take Ews b 2920 632 8 2928 624 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _block 2920 8 (vl 0) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 2928 624 8 2936 616 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _word 2928 8 (vl 0) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 2936 616 8 2944 608 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _candidate 2936 8 (vl 0) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 2944 608 4 2948 604 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _scan 2944 4 (vi 0) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 2948 604 4 2952 600 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (mz_take Ews b 2952 600 8 2960 592 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _manifest_status 2952 8 (vl 0) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 2960 592 8 2968 584 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _manifest_error 2960 8 (vl 0) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 2968 584 512 3480 72 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _free_words 2968 512 (z64 64) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 3480 72 8 3488 64 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _candidate_manifest 3480 8 (vl 0) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 3488 64 8 3496 56 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _first 3488 8 (vl 0) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 3496 56 8 3504 48 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _first_manifest 3496 8 (vl 0) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 3504 48 8 3512 40 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _second 3504 8 (vl 0) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 3512 40 32 3544 8 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _answer 3512 32 (z64 4) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 3544 8 4 3548 4 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _scrubbed 3544 4 (vi 0) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  unfold lzero. cancel.
Qed.

Lemma law_zero: forall gv, headptr (gv _law) ->
  globvars2pred gv [(_law, v_law)] |-- lzero (gv _law) * TT.
Proof.
  intros gv [b H]. unfold globvars2pred, globvar2pred. simpl. rewrite ?sepcon_emp. rewrite H.
  assert (FC: field_compatible t_law nil (Vptr b Ptrofs.zero)).
  { apply headptr_field_compatible; try (exists b; reflexivity);
      first [ reflexivity | exact I | (vm_compute; reflexivity) | (apply la_env_cs_sound; reflexivity) ]. }
  exact (law_zero_b b FC).
Qed.
