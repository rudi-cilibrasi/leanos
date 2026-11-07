(* Law handoff_decode_exact: the harness's struct law as its fields with any values (lraw) and its padding, proved
   once (VST's unfold_data_at on the struct is slow), and the global `law` as main finds it: all zeros. *)
Require Import VST.floyd.proofauto.
Require Import LeanosHandoff.harness.handoff_decode_exact.code.
Require Import LeanosHandoff.proof.Defs.
Require Import LeanosHandoff.proof.HandoffSpecs.
Require Import LeanosHandoff.proof.LawProg LeanosHandoff.proof.LawDefs.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

(* struct law with the values of its fields, in its order. *)
Definition law_val (c mg ad tt cand pj run ce ie: val) (us bl rs: list val) (ss: list (list val))
    (at0 eok rec ex vd ch wd bk va: val) (st an: list val) : reptype t_law :=
  (c, (mg, (ad, (tt, (cand, (pj, (run, (ce, (ie, (us, (bl, (rs, (ss, (at0, (eok, (rec, (ex, (vd, (ch, (wd, (bk,
   (va, (st, an))))))))))))))))))))))).

Definition lraw (q: val) (c mg ad tt cand pj run ce ie: val) (us bl rs: list val) (ss: list (list val))
    (at0 eok rec ex vd ch wd bk va: val) (st an: list val) : mpred :=
 (field_at Ews t_law (DOT _call) c q *
  field_at Ews t_law (DOT _magic) mg q *
  field_at Ews t_law (DOT _address) ad q *
  field_at Ews t_law (DOT _total) tt q *
  field_at Ews t_law (DOT _candidate) cand q *
  field_at Ews t_law (DOT _projection) pj q *
  field_at Ews t_law (DOT _running) run q *
  field_at Ews t_law (DOT _copy_expect) ce q *
  field_at Ews t_law (DOT _info_expect) ie q *
  field_at Ews t_law (DOT _usable_expect) us q *
  field_at Ews t_law (DOT _blocked_expect) bl q *
  field_at Ews t_law (DOT _reserved_expect) rs q *
  field_at Ews t_law (DOT _states_expect) ss q *
  field_at Ews t_law (DOT _at) at0 q *
  field_at Ews t_law (DOT _extent_ok) eok q *
  field_at Ews t_law (DOT _records) rec q *
  field_at Ews t_law (DOT _expect) ex q *
  field_at Ews t_law (DOT _verdict) vd q *
  field_at Ews t_law (DOT _chunk) ch q *
  field_at Ews t_law (DOT _word) wd q *
  field_at Ews t_law (DOT _block) bk q *
  field_at Ews t_law (DOT _value) va q *
  field_at Ews t_law (DOT _stream) st q *
  field_at Ews t_law (DOT _answer) an q)%logic.

Definition z32 : val := Vint (Int.repr 0).
Definition z64 : val := Vlong (Int64.repr 0).

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
  mapsto_zeros 2680 Ews (Vptr b (Ptrofs.repr 0)) |--
  (lraw (Vptr b Ptrofs.zero) z32 z32 z32 z32 z64 z32 z32 nullval nullval (Zrepeat z64 64) (Zrepeat z64 64)
    (Zrepeat z64 64) (Zrepeat (Zrepeat z64 41) 2) z32 z32 z32 z32 z32 z64 z64 z64 z64 (Zrepeat z64 7)
    (Zrepeat z64 41) * TT)%logic.
Proof.
  intros b FC.
  sep_apply (mz_take Ews b 0 2680 4 4 2676 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _call 0 4 z32 eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 4 2676 4 8 2672 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _magic 4 4 z32 eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 8 2672 4 12 2668 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _address 8 4 z32 eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 12 2668 4 16 2664 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _total 12 4 z32 eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 16 2664 8 24 2656 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _candidate 16 8 z64 eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 24 2656 4 28 2652 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _projection 24 4 z32 eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 28 2652 4 32 2648 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _running 28 4 z32 eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 32 2648 8 40 2640 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _copy_expect 32 8 nullval eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 40 2640 8 48 2632 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _info_expect 40 8 nullval eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 48 2632 512 560 2120 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _usable_expect 48 512 (Zrepeat z64 64) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 560 2120 512 1072 1608 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _blocked_expect 560 512 (Zrepeat z64 64) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 1072 1608 512 1584 1096 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _reserved_expect 1072 512 (Zrepeat z64 64) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 1584 1096 656 2240 440 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _states_expect 1584 656 (Zrepeat (Zrepeat z64 41) 2) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 2240 440 4 2244 436 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _at 2240 4 z32 eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 2244 436 4 2248 432 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _extent_ok 2244 4 z32 eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 2248 432 4 2252 428 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _records 2248 4 z32 eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 2252 428 4 2256 424 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _expect 2252 4 z32 eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 2256 424 4 2260 420 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _verdict 2256 4 z32 eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 2260 420 4 2264 416 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (mz_take Ews b 2264 416 8 2272 408 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _chunk 2264 8 z64 eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 2272 408 8 2280 400 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _word 2272 8 z64 eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 2280 400 8 2288 392 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _block 2280 8 z64 eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 2288 392 8 2296 384 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _value 2288 8 z64 eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 2296 384 56 2352 328 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _stream 2296 56 (Zrepeat z64 7) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 2352 328 328 2680 0 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _answer 2352 328 (Zrepeat z64 41) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  unfold lraw. cancel.
Qed.

Lemma law_zero: forall gv, headptr (gv _law) ->
  globvars2pred gv [(_law, v_law)] |--
  (lraw (gv _law) z32 z32 z32 z32 z64 z32 z32 nullval nullval (Zrepeat z64 64) (Zrepeat z64 64) (Zrepeat z64 64)
    (Zrepeat (Zrepeat z64 41) 2) z32 z32 z32 z32 z32 z64 z64 z64 z64 (Zrepeat z64 7) (Zrepeat z64 41) * TT)%logic.
Proof.
  intros gv [b H]. unfold globvars2pred, globvar2pred. simpl. rewrite ?sepcon_emp. rewrite H.
  assert (FC: field_compatible t_law nil (Vptr b Ptrofs.zero)).
  { apply headptr_field_compatible; try (exists b; reflexivity);
      first [ reflexivity | exact I | (vm_compute; reflexivity) | (apply la_env_cs_sound; reflexivity) ]. }
  exact (law_zero_b b FC).
Qed.

(* The law's fields as lfields. *)
Lemma lfields_raw: forall q x ce ie m s,
  lfields q x ce ie m s =
  lraw q (vi (call_code (i_call x))) (vi (i_magic x)) (vi (i_address x)) (vi (m_total m)) (vl (target x))
    (vi (proj_code x)) (vi (w_running s)) ce ie (map vl (m_usable m)) (map vl (m_blocked m)) (map vl (m_reserved m))
    (states_val (m_states m)) (vi (m_at m)) (vi (Z.b2z (m_extent_ok m))) (vi (w_records s)) (vi (w_expect s))
    (vi (w_verdict s)) (vl (w_chunk s)) (vl (w_word s)) (vl (w_block s)) (vl (w_value s)) (map vl (w_stream s))
    (map vl (w_answer s)).
Proof. reflexivity. Qed.
