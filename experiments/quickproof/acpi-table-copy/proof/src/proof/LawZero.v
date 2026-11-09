(* Law table_copy_exact: the global `law` as main finds it (all zeros), field by field: its 6408 zero bytes split
   at the fields' offsets (the padding between fields dropped), each field's bytes its zero value. *)
Require Import VST.floyd.proofauto.
Require Import LeanosAcpi.harness.table_copy_exact.code.
Require Import LeanosAcpi.proof.Defs.
Require Import LeanosAcpi.proof.AcpiSpecs.
Require Import LeanosAcpi.proof.LawProg LeanosAcpi.proof.LawDefs.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

Definition x0 : inputs := mk_inputs 0 0 (Zrepeat 0 36) nil nil.
Definition pl0 : place := mk_place nullval nullval nullval.
Definition hx0 : list Z := Zrepeat 0 36.
Definition s0 : lst :=
  mk_lst 0 0 0 0 0 nullval nullval 0 0 0 0 0 (Zrepeat 0 5) 0 0 0 0 0 0 (Zrepeat 0 256) 0 0 (Zrepeat 0 256)
    (Zrepeat 0 256) (Zrepeat 0 256) 0.

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

Lemma law_zero: forall b, field_compatible t_law nil (Vptr b Ptrofs.zero) ->
  mapsto_zeros 6408 Ews (Vptr b (Ptrofs.repr 0)) |--
  (lfields (Vptr b Ptrofs.zero) x0 pl0 nullval nullval hx0 s0 * TT)%logic.
Proof.
  intros b FC.
  sep_apply (mz_take Ews b 0 6408 8 8 6400 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _kind 0 8 (vl (i_kind x0)) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 8 6400 8 16 6392 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _address 8 8 (vl (i_address x0)) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 16 6392 8 24 6384 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _header 16 8 (p_header pl0) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 24 6384 8 32 6376 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _root 24 8 (p_root pl0) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 32 6376 8 40 6368 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _tables 32 8 (p_tables pl0) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 40 6368 4 44 6364 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _root_capacity 40 4 (vi (root_capacity x0)) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 44 6364 4 48 6360 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _table_capacity 44 4 (vi (table_capacity x0)) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 48 6360 36 84 6324 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _header_expect 48 36 (bytes_val hx0) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 84 6324 4 88 6320 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (mz_take Ews b 88 6320 8 96 6312 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _root_expect 88 8 (nullval) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 96 6312 8 104 6304 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _tables_expect 96 8 (nullval) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 104 6304 4 108 6300 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _expect 104 4 (vi (w_expect s0)) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 108 6300 4 112 6296 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _verdict 108 4 (vi (w_verdict s0)) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 112 6296 4 116 6292 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _is_root 112 4 (vi (w_is_root s0)) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 116 6292 4 120 6288 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _table 116 4 (vi (w_table s0)) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 120 6288 8 128 6280 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _sdt_address 120 8 (vl (w_sdt_address s0)) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 128 6280 8 136 6272 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _destination 128 8 (w_dest s0) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 136 6272 8 144 6264 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _destination_expect 136 8 (w_dexp s0) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 144 6264 4 148 6260 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _capacity 144 4 (vi (w_capacity s0)) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 148 6260 4 152 6256 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _length 148 4 (vi (w_length s0)) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 152 6256 8 160 6248 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _cursor 152 8 (vl (w_cursor s0)) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 160 6248 8 168 6240 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _byte 160 8 (vl (w_byte s0)) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 168 6240 4 172 6236 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _word 168 4 (vi (w_word s0)) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 172 6236 4 176 6232 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (mz_take Ews b 176 6232 40 216 6192 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _answer 176 40 (map vl (w_answer s0)) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 216 6192 4 220 6188 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _root_done 216 4 (vi (w_root_done s0)) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 220 6188 4 224 6184 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _root_length 220 4 (vi (w_root_length s0)) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 224 6184 4 228 6180 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _entries_done 224 4 (vi (w_entries_done s0)) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 228 6180 4 232 6176 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _width 228 4 (vi (w_width s0)) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 232 6176 4 236 6172 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _count 232 4 (vi (w_count s0)) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 236 6172 4 240 6168 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (mz_take Ews b 240 6168 8 248 6160 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _root_cursor 240 8 (vl (w_root_cursor s0)) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 248 6160 2048 2296 4112 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _addresses 248 2048 (map vl (w_addresses s0)) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 2296 4112 4 2300 4108 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _arena 2296 4 (vi (w_arena s0)) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 2300 4108 4 2304 4104 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _ended 2300 4 (vi (w_ended s0)) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 2304 4104 1024 3328 3080 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _offsets 2304 1024 (map vi (w_offsets s0)) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 3328 3080 1024 4352 2056 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _lengths 3328 1024 (map vi (w_lengths s0)) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 4352 2056 2048 6400 8 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _finals 4352 2048 (map vl (w_finals s0)) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  sep_apply (mz_take Ews b 6400 8 8 6408 0 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(rep_lia)).
  sep_apply (zfield b _ordinal 6400 8 (vl (w_ordinal s0)) eq_refl eq_refl ltac:(zv) eq_refl eq_refl ltac:(lnf) FC).
  unfold lfields. cancel.
Qed.
