(* The body of acpi_copy_root_tables: the loop over the root's entries, each table copied by acpi_copy_sdt into the
   table arena from the cursor (the arena split around it) and described in its slot (split out of the slots), the
   binding, budget and stream checks, the three copy-sequence calls and their check; against `begin_table`,
   `table_copied` and the Sequencing steps one table at a time.  BINDING cannot fail (the slot is what acpi_copy_sdt
   wrote), nor BUDGET on `padded_length < length` (a length is at most 65536), nor SEQUENCE after the loop (the
   carried ordinal is entry + 1 = count). *)
Require Import VST.floyd.proofauto.
Require Import LeanosAcpi.acpi.code.
Require Import LeanosAcpi.proof.Defs.
Require Import LeanosAcpi.proof.AcpiSpecs.
Require Import LeanosAcpi.proof.InternalSpecs.
Require Import LeanosAcpi.proof.PipeLemmas.
Require Import LeanosAcpi.proof.PipeModel.
Require Import LeanosAcpi.proof.PipeSlots.
Require Import LeanosAcpi.proof.PipeFast.
#[local] Ltac simplify_remove_localdef_temp ::= fast_remove_localdef_temp.
#[local] Existing Instance AcpiSpecs.CS.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[local] Opaque run step sdt_copied root_copied table_copied tables_done begin_sdt begin_table tables_start.

Lemma Znth_addr: forall (addresses: list Z) (arest: list val) e, 0 <= e < Zlength addresses ->
  Znth e (map vl addresses ++ arest) = vl (Znth e addresses).
Proof. intros. rewrite Znth_app1 by (rewrite Zlength_map; lia). rewrite Znth_map by lia. reflexivity. Qed.

Lemma slots_val_eq: forall pl m1 m2 (sold: list sdt_rep), m_slots m1 = m_slots m2 ->
  slots_val pl m1 sold = slots_val pl m2 sold.
Proof. intros. unfold slots_val. rewrite H. reflexivity. Qed.

Lemma slot_new_ok: forall x m' a off len c, mem_ok x m' -> HEADER_BYTES <= len -> len <= table_capacity x - off ->
  0 <= off -> u64_ok a -> len <= MAX_SDT_BYTES ->
  slot_ok (m_tables m') (mk_sdt a off len (c mod 2 ^ 32)).
Proof.
  intros x m' a off len c (_ & _ & T & _) L1 L2 O U L3. unfold slot_ok, MAX_SDT_BYTES, HEADER_BYTES in *. simpl.
  pose proof (Z.mod_pos_bound c (2 ^ 32) ltac:(lia)). unfold u32_ok, u64_ok in *. repeat split; try rep_lia.
Qed.

Lemma m_tables_add_slot: forall m s, m_tables (add_slot m s) = m_tables m.
Proof. reflexivity. Qed.
Lemma m_header_add_slot: forall m s, m_header (add_slot m s) = m_header m.
Proof. reflexivity. Qed.
Lemma m_slots_add_slot: forall m s, m_slots (add_slot m s) = m_slots m ++ [s].
Proof. reflexivity. Qed.

Lemma sdt_val_eq: forall base a o l n, sdt_val base (mk_sdt a o l n) = (vl a, (offset_val o base, (vi l, vi n))).
Proof. reflexivity. Qed.

Lemma sdt_val_eq': forall base a o l n,
  sdt_val base (mk_sdt a o l n) = (Vlong (Int64.repr a), (offset_val o base, (Vint (Int.repr l), Vint (Int.repr n)))).
Proof. reflexivity. Qed.

Lemma Znth_addr': forall (addresses: list Z) (arest: list val) e, 0 <= e < Zlength addresses ->
  Znth e (map vl addresses ++ arest) = Vlong (Int64.repr (Znth e addresses)).
Proof. intros. apply Znth_addr; auto. Qed.

Lemma eval_add_uchar: forall p off, isptr p -> 0 <= off <= Int.max_unsigned ->
  eval_binop Oadd (tptr tuchar) tuint p (Vint (Int.repr off)) = offset_val off p.
Proof.
  intros. destruct p; try contradiction. unfold eval_binop. simpl. unfold sem_add_ptr_int. simpl. f_equal. f_equal.
  unfold Ptrofs.of_intu, Ptrofs.of_int. rewrite Ptrofs.mul_commut, Ptrofs.mul_one. rewrite Int.unsigned_repr by auto.
  reflexivity.
Qed.

Lemma ne_self_ptr: forall q, isptr q ->
  force_val (sem_cast tint tbool (eval_binop Cop.One (tptr tuchar) (tptr tuchar) q q)) = Vint (Int.repr 0).
Proof.
  intros. destruct q; try contradiction. unfold eval_binop. simpl. unfold sem_cmp_pp. simpl.
  destruct (eq_block b b); [ | congruence ]. rewrite Ptrofs.eq_true. reflexivity.
Qed.

Lemma mem_ok_add_slot: forall x m s, mem_ok x m -> mem_ok x (add_slot m s).
Proof. intros. exact H. Qed.

Ltac dead_if :=
  match goal with
  | H: Int.repr ?a <> Int.zero |- _ => exfalso; apply H; reflexivity
  | H: ?a <> ?a |- _ => exfalso; apply H; reflexivity
  | H: Int.repr ?a = Int.zero |- _ => exfalso; discriminate H
  end.

Lemma final_word: forall a b,
  Int64.repr (Int.signed (Int.repr (Z.b2z (proj_sumbool (zeq a b))))) = Int64.repr (if a =? b then 1 else 0).
Proof. intros. destruct (zeq a b); destruct (Z.eqb_spec a b); try lia; reflexivity. Qed.

Lemma slots_val_nil: forall pl m (sold: list sdt_rep), m_slots m = [] -> Zlength sold = MAX_ENTRIES ->
  slots_val pl m sold = sold.
Proof. intros. unfold slots_val. rewrite H. simpl. apply sublist_same; auto. Qed.

Lemma body_acpi_copy_root_tables (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_acpi_copy_root_tables (copy_root_tables_spec Ora).
Proof.
  start_function.
  rename H into IX. rename H0 into M0. rename H1 into S0. rename H2 into R0. rename H3 into LA.
  rename H4 into LAR. rename H5 into FA. rename H6 into LS.
  assert_PROP (field_compatible (tarray tuchar (table_capacity x)) [] (p_tables pl)) as FCt by entailer!.
  assert_PROP (field_compatible (tarray t_sdt MAX_ENTRIES) [] cp) as FCc by entailer!.
  assert_PROP (isptr cp) as Pcp by entailer!.
  assert_PROP (isptr (p_tables pl)) as Ptp by entailer!.
  assert (TC: 0 <= table_capacity x <= Int.max_unsigned)
    by (destruct IX as (_ & _ & _ & _ & T & _); unfold table_capacity in *; pose proof (Zlength_nonneg (i_tables x)); lia).
  assert (Lmx: 0 <= Zlength addresses <= 256) by (pose proof (Zlength_nonneg addresses); unfold MAX_ENTRIES in *; lia).
  unfold vi.
  forward.
  forward_if.
  { (* no entries *)
    assert (R: run x (tables_start x addresses m) [] = Some (Return S_SEQUENCE None m))
      by (rewrite tables_start_nil by lia; apply run_nil).
    forward.
    Exists (@nil answer) S_SEQUENCE m. fix_status S_SEQUENCE. rewrite app_nil_r.
    rewrite (slots_val_nil pl m sold S0 LS).
    entailer!.
    split; [ rewrite S0; constructor | discriminate ]. }
  forward. forward. forward.
  forward_loop (EX off: Z, EX hs: list answer, EX mE: mem,
    PROP (0 <= (Zlength (m_slots mE)) <= Zlength addresses; 0 <= off <= table_capacity x; mem_ok x mE;
          m_root mE = m_root m; m_root_copy mE = m_root_copy m; m_entries mE = m_entries m;
          Forall (slot_ok (m_tables mE)) (m_slots mE);
          run x (tables_start x addresses m) hs =
            Some (if (Zlength (m_slots mE)) <? Zlength addresses
                  then begin_table x (mk_tloop addresses (Zlength (m_slots mE)) off (Zlength (m_slots mE))) mE
                  else tables_done (Zlength addresses) mE))
    LOCAL (temp _entry (Vint (Int.repr (Zlength (m_slots mE)))); temp _arena_offset (Vint (Int.repr off));
           temp _copied_ordinal (Vlong (Int64.repr (Zlength (m_slots mE))));
           temp _copy copy; temp _context ctx; temp _entries ep; temp _addresses ap; temp _header (p_header pl);
           temp _arena (p_tables pl); temp _arena_capacity (Vint (Int.repr (table_capacity x)));
           temp _copies cp; temp _copied_count np; gvars gv)
    SEP (func_ptr' (copy_spec Ora) copy; Ora gv ctx pl x (h ++ hs);
         data_at esh t_entries (eb, (Vint (Int.repr (Zlength addresses)), w)) ep;
         data_at ash (tarray tulong MAX_ENTRIES) (map vl addresses ++ arest) ap;
         data_at sh (tarray tuchar HEADER_BYTES) (bytes_val (m_header mE)) (p_header pl);
         data_at sh (tarray tuchar (table_capacity x)) (bytes_val (m_tables mE)) (p_tables pl);
         data_at csh (tarray t_sdt MAX_ENTRIES) (slots_val pl mE sold) cp; data_at nsh tuint nold np))%assert
  continue: (EX off: Z, EX hs: list answer, EX mE: mem,
    PROP (1 <= (Zlength (m_slots mE)) <= Zlength addresses; 0 <= off <= table_capacity x; mem_ok x mE;
          m_root mE = m_root m; m_root_copy mE = m_root_copy m; m_entries mE = m_entries m;
          Forall (slot_ok (m_tables mE)) (m_slots mE);
          run x (tables_start x addresses m) hs =
            Some (if (Zlength (m_slots mE)) <? Zlength addresses
                  then begin_table x (mk_tloop addresses (Zlength (m_slots mE)) off (Zlength (m_slots mE))) mE
                  else tables_done (Zlength addresses) mE))
    LOCAL (temp _entry (Vint (Int.repr ((Zlength (m_slots mE)) - 1))); temp _arena_offset (Vint (Int.repr off));
           temp _copied_ordinal (Vlong (Int64.repr (Zlength (m_slots mE))));
           temp _copy copy; temp _context ctx; temp _entries ep; temp _addresses ap; temp _header (p_header pl);
           temp _arena (p_tables pl); temp _arena_capacity (Vint (Int.repr (table_capacity x)));
           temp _copies cp; temp _copied_count np; gvars gv)
    SEP (func_ptr' (copy_spec Ora) copy; Ora gv ctx pl x (h ++ hs);
         data_at esh t_entries (eb, (Vint (Int.repr (Zlength addresses)), w)) ep;
         data_at ash (tarray tulong MAX_ENTRIES) (map vl addresses ++ arest) ap;
         data_at sh (tarray tuchar HEADER_BYTES) (bytes_val (m_header mE)) (p_header pl);
         data_at sh (tarray tuchar (table_capacity x)) (bytes_val (m_tables mE)) (p_tables pl);
         data_at csh (tarray t_sdt MAX_ENTRIES) (slots_val pl mE sold) cp; data_at nsh tuint nold np))%assert
  break: (EX off: Z, EX hs: list answer, EX mE: mem,
    PROP ((Zlength (m_slots mE)) = Zlength addresses; mem_ok x mE;
          m_root mE = m_root m; m_root_copy mE = m_root_copy m; m_entries mE = m_entries m;
          Forall (slot_ok (m_tables mE)) (m_slots mE);
          run x (tables_start x addresses m) hs = Some (tables_done (Zlength addresses) mE))
    LOCAL (temp _copied_ordinal (Vlong (Int64.repr (Zlength addresses))); temp _entries ep; temp _copied_count np)
    SEP (func_ptr' (copy_spec Ora) copy; Ora gv ctx pl x (h ++ hs);
         data_at esh t_entries (eb, (Vint (Int.repr (Zlength addresses)), w)) ep;
         data_at ash (tarray tulong MAX_ENTRIES) (map vl addresses ++ arest) ap;
         data_at sh (tarray tuchar HEADER_BYTES) (bytes_val (m_header mE)) (p_header pl);
         data_at sh (tarray tuchar (table_capacity x)) (bytes_val (m_tables mE)) (p_tables pl);
         data_at csh (tarray t_sdt MAX_ENTRIES) (slots_val pl mE sold) cp; data_at nsh tuint nold np))%assert.
  { Exists 0 (@nil answer) m.
    assert (R: run x (tables_start x addresses m) [] =
               Some (if (Zlength (m_slots m)) <? Zlength addresses
                     then begin_table x (mk_tloop addresses (Zlength (m_slots m)) 0 (Zlength (m_slots m))) m
                     else tables_done (Zlength addresses) m)).
    { rewrite S0, Zlength_nil, (proj2 (Z.ltb_lt 0 _)) by lia. rewrite run_nil, tables_start_go by lia. reflexivity. }
    rewrite app_nil_r, (slots_val_nil pl m sold S0 LS). entailer!. rewrite S0, Zlength_nil. repeat split; auto; lia. }
  { Intros off hs mE.
    match goal with H: run _ (tables_start _ _ _) hs = _ |- _ => rename H into R end.
    match goal with H: mem_ok x mE |- _ => rename H into ME end.
    match goal with H: m_root mE = _ |- _ => rename H into ER end.
    match goal with H: m_root_copy mE = _ |- _ => rename H into ERC end.
    match goal with H: m_entries mE = _ |- _ => rename H into EEN end.
    match goal with H: Forall (slot_ok _) (m_slots mE) |- _ => rename H into FS end.
    forward. forward_if.
    2: { (* the loop ends *)
      rewrite (proj2 (Z.ltb_ge _ _)) in R by lia.
      assert (Ec: (Zlength (m_slots mE)) = Zlength addresses) by lia.
      forward. Exists off hs mE. rewrite Ec. entailer!. }
    rewrite (proj2 (Z.ltb_lt _ _)) in R by lia.
    assert (LE: (Zlength (m_slots mE)) < Zlength addresses) by lia.
    forward_if.
    { (* the arena is full *)
      rewrite begin_table_fail in R by (cbn [l_offset]; lia).
      forward.
      Exists hs S_BUDGET mE. fix_status S_BUDGET. entailer!; try discriminate. }
    rewrite begin_table_go in R by (cbn [l_offset]; lia).
    forward.
    rewrite add_ptr_sdt_uint, Int.unsigned_repr by (auto; rep_lia).
    forward.
    { entailer!. rewrite Znth_addr by lia. unfold vl. simpl. auto. }
    rewrite Znth_addr by lia.
    assert (UA: u64_ok (Znth (Zlength (m_slots mE)) addresses))
      by (pose proof (proj1 (Forall_Znth addresses _) FA (Zlength (m_slots mE)) ltac:(lia)); cbv beta in *; unfold u64_ok, MAX_U32 in *; rep_lia).
    rewrite (tables_split sh x mE off (p_tables pl) ME ltac:(lia) FCt).
    rewrite (slots_split csh pl mE sold cp ltac:(unfold MAX_ENTRIES in *; lia) LS FCc).
    Intros.
    forward_call (gv, copy, ctx, pl, sh, x, h ++ hs, TTable (mk_tloop addresses (Zlength (m_slots mE)) off (Zlength (m_slots mE))), mE, csh, offset_val (SDT_BYTES * (Zlength (m_slots mE))) cp,
                  Znth (Zlength (m_slots mE)) sold).
    { split; [ eapply run_glue; eauto | cbn [l_offset]; lia ]. }
    Intros vret. destruct vret as [[[[hs' st] m'] len] cursor]. cbn [fst snd] in *.
    match goal with H: run _ (begin_sdt _ _ _) hs' = _ |- _ => rename H into R' end.
    match goal with H: mem_ok x m' |- _ => rename H into M' end.
    match goal with H: copy_frame _ mE m' |- _ => rename H into CF end.
    match goal with H: st = S_OK -> _ |- _ => rename H into OKS end.
    cbn [copy_frame capacity_of dest_of dest_ptr l_offset l_entry l_addresses address_of offset_of base_of] in *.
    destruct CF as (CF1 & CF2 & CF3 & CF4 & CF5 & CF6 & CF7 & CF8).
    rewrite <- app_assoc.
    match goal with H: status_ok st |- _ => rename H into SOK end.
    assert (P1: m_root m' = m_root m) by congruence.
    assert (P2: m_root_copy m' = m_root_copy m) by congruence.
    assert (P3: m_entries m' = m_entries m) by congruence.
    assert (P4: Forall (slot_ok (m_tables m')) (m_slots m'))
      by (rewrite CF6; eapply Forall_slot_ok_len; [ | exact FS ]; congruence).
    unfold vi.
    forward.
    forward_if.
    { (* acpi_copy_sdt failed *)
      assert (ST: (st =? S_OK) = false)
        by (apply Z.eqb_neq; intro Es; subst st; match goal with H: Int.repr _ <> Int.repr _ |- _ => apply H; reflexivity end).
      rewrite ST in R' |- *. cbv iota.
      sep_apply (tables_join sh x mE m' off (p_tables pl) M' ltac:(lia) CF8 FCt).
      sep_apply (slots_join_old csh pl mE sold cp ltac:(unfold MAX_ENTRIES in *; lia) LS FCc).
      rewrite (slots_val_eq pl mE m' sold) by auto.
      assert (RR: run x (tables_start x addresses m) (hs ++ hs') = Some (Return st None m'))
        by (rewrite run_app, R; exact R').
      forward.
      Exists (hs ++ hs') st m'. rewrite ST. cbv iota.
      entailer!. }
    assert (ST: st = S_OK) by (apply status_ok_repr; auto).
    subst st. rewrite Z.eqb_refl in R' |- *. cbv iota.
    destruct (OKS eq_refl) as (L1 & L2 & UC). clear OKS.
    rewrite sdt_copied_table, table_copied_eq in R'. cbn [l_offset l_entry l_addresses] in R'.
    rewrite sdt_val_eq'.
    forward. forward.
    { entailer!. rewrite Znth_addr' by lia. simpl. auto. }
    rewrite Znth_addr' by lia.
    forward_if (temp _t'2 (Vint (Int.repr 0))).
    { exfalso. contradiction. }
    { forward. forward.
      { entailer!. apply denote_tc_test_eq_split; auto 50 with valid_pointer. }
      entailer!. destruct (eq_dec (offset_val off (p_tables pl)) (offset_val off (p_tables pl))) as [_ | C]; [ reflexivity | contradiction C; reflexivity ]. }
    forward_if; [ dead_if | ].
    unfold HEADER_BYTES, MAX_SDT_BYTES in L1.
    forward. forward.
    rewrite padded_int by (unfold MAX_SDT_BYTES; lia).
    pose proof (padded_bounds len ltac:(lia)) as PB.
    forward.
    forward_if (temp _t'3 (Vint (bint (table_capacity x - off <? padded len)))).
    { exfalso. lia. }
    { forward. entailer!. rewrite zlt_ltb, bool2val_bint. reflexivity. }
    assert (Q0: mem_ok x (add_slot m' (mk_sdt (Znth (Zlength (m_slots mE)) addresses) off len (cursor mod 2 ^ 32)))) by (apply mem_ok_add_slot; auto).
    assert (Q1: m_root (add_slot m' (mk_sdt (Znth (Zlength (m_slots mE)) addresses) off len (cursor mod 2 ^ 32))) = m_root m) by exact P1.
    assert (Q2: m_root_copy (add_slot m' (mk_sdt (Znth (Zlength (m_slots mE)) addresses) off len (cursor mod 2 ^ 32))) = m_root_copy m) by exact P2.
    assert (Q3: m_entries (add_slot m' (mk_sdt (Znth (Zlength (m_slots mE)) addresses) off len (cursor mod 2 ^ 32))) = m_entries m) by exact P3.
    assert (Q4: Forall (slot_ok (m_tables (add_slot m' (mk_sdt (Znth (Zlength (m_slots mE)) addresses) off len (cursor mod 2 ^ 32))))) (m_slots (add_slot m' (mk_sdt (Znth (Zlength (m_slots mE)) addresses) off len (cursor mod 2 ^ 32))))).
    { rewrite m_slots_add_slot, m_tables_add_slot. apply Forall_app; split; auto. constructor; [ | constructor ].
      apply slot_new_ok with x; auto; unfold HEADER_BYTES, MAX_SDT_BYTES; lia. }
    assert (Q5: Zlength (m_slots (add_slot m' (mk_sdt (Znth (Zlength (m_slots mE)) addresses) off len (cursor mod 2 ^ 32)))) = (Zlength (m_slots mE)) + 1)
      by (rewrite m_slots_add_slot, Zlength_app, CF6, Zlength_cons, Zlength_nil; lia).
    forward_if.
    { (* the table does not fit *)
      bfix. match goal with H: (_ <? _) = true |- _ => rename H into BUD end.
      assert (RB: run x (tables_start x addresses m) (hs ++ hs') = Some (Return S_BUDGET None (add_slot m' (mk_sdt (Znth (Zlength (m_slots mE)) addresses) off len (cursor mod 2 ^ 32)))))
        by (rewrite run_app, R, R', BUD; reflexivity).
      rewrite <- sdt_val_eq'.
      sep_apply (tables_join sh x mE m' off (p_tables pl) M' ltac:(lia) CF8 FCt).
      sep_apply (slots_join_add csh pl mE (mk_sdt (Znth (Zlength (m_slots mE)) addresses) off len (cursor mod 2 ^ 32)) sold cp ltac:(unfold MAX_ENTRIES in *; lia) LS FCc).
      rewrite (slots_val_eq pl (add_slot mE (mk_sdt (Znth (Zlength (m_slots mE)) addresses) off len (cursor mod 2 ^ 32))) (add_slot m' (mk_sdt (Znth (Zlength (m_slots mE)) addresses) off len (cursor mod 2 ^ 32))) sold) by (rewrite !m_slots_add_slot; congruence).
      forward.
      Exists (hs ++ hs') S_BUDGET (add_slot m' (mk_sdt (Znth (Zlength (m_slots mE)) addresses) off len (cursor mod 2 ^ 32))). fix_status S_BUDGET.
      rewrite m_tables_add_slot, m_header_add_slot.
      entailer!; try discriminate. }
    bfix. match goal with H: (_ <? _) = false |- _ => rename H into BUD end.
    apply Z.ltb_ge in BUD.
    pose proof (Z.mod_pos_bound cursor (2 ^ 32) ltac:(lia)) as CB.
    forward.
    forward_if.
    { (* the cursor is not where the table ends *)
      match goal with H: Int.repr _ <> Int.add (Int.repr off) _ |- _ => rename H into NE end.
      change (Z.pow_pos 2 32) with (2 ^ 32) in NE. rewrite ?add_repr in NE. apply repr32_neq in NE.
      assert (RS: run x (tables_start x addresses m) (hs ++ hs') = Some (Return S_STREAM None (add_slot m' (mk_sdt (Znth (Zlength (m_slots mE)) addresses) off len (cursor mod 2 ^ 32))))).
      { rewrite run_app, R, R', (proj2 (Z.ltb_ge _ _) BUD), (proj2 (Z.eqb_neq _ _) NE). reflexivity. }
      rewrite <- sdt_val_eq'.
      sep_apply (tables_join sh x mE m' off (p_tables pl) M' ltac:(lia) CF8 FCt).
      sep_apply (slots_join_add csh pl mE (mk_sdt (Znth (Zlength (m_slots mE)) addresses) off len (cursor mod 2 ^ 32)) sold cp ltac:(unfold MAX_ENTRIES in *; lia) LS FCc).
      rewrite (slots_val_eq pl (add_slot mE (mk_sdt (Znth (Zlength (m_slots mE)) addresses) off len (cursor mod 2 ^ 32))) (add_slot m' (mk_sdt (Znth (Zlength (m_slots mE)) addresses) off len (cursor mod 2 ^ 32))) sold) by (rewrite !m_slots_add_slot; congruence).
      forward.
      Exists (hs ++ hs') S_STREAM (add_slot m' (mk_sdt (Znth (Zlength (m_slots mE)) addresses) off len (cursor mod 2 ^ 32))). fix_status S_STREAM.
      rewrite m_tables_add_slot, m_header_add_slot.
      entailer!; try discriminate. }
    match goal with H: Int.repr _ = Int.add (Int.repr off) _ |- _ => rename H into EQ end.
    change (Z.pow_pos 2 32) with (2 ^ 32) in EQ. rewrite ?add_repr in EQ. apply repr32_inj in EQ; [ | unfold u32_ok; rep_lia | unfold u32_ok; rep_lia ].
    assert (RG: run x (tables_start x addresses m) (hs ++ hs') =
                Some (Go (Sequencing (mk_tloop addresses (Zlength (m_slots mE)) (off + padded len) (Zlength (m_slots mE))) []) (add_slot m' (mk_sdt (Znth (Zlength (m_slots mE)) addresses) off len (cursor mod 2 ^ 32))))).
    { rewrite run_app, R, R', (proj2 (Z.ltb_ge _ _) BUD), (proj2 (Z.eqb_eq _ _) EQ). reflexivity. }
    rewrite <- sdt_val_eq'.
    sep_apply (tables_join sh x mE m' off (p_tables pl) M' ltac:(lia) CF8 FCt).
    sep_apply (slots_join_add csh pl mE (mk_sdt (Znth (Zlength (m_slots mE)) addresses) off len (cursor mod 2 ^ 32)) sold cp ltac:(unfold MAX_ENTRIES in *; lia) LS FCc).
    rewrite (slots_val_eq pl (add_slot mE (mk_sdt (Znth (Zlength (m_slots mE)) addresses) off len (cursor mod 2 ^ 32))) (add_slot m' (mk_sdt (Znth (Zlength (m_slots mE)) addresses) off len (cursor mod 2 ^ 32))) sold) by (rewrite !m_slots_add_slot; congruence).
    rewrite <- m_tables_add_slot with (s := (mk_sdt (Znth (Zlength (m_slots mE)) addresses) off len (cursor mod 2 ^ 32))), <- m_header_add_slot with (s := (mk_sdt (Znth (Zlength (m_slots mE)) addresses) off len (cursor mod 2 ^ 32))).
    forward. forward. forward.
    rewrite add_repr, final_word.
    deadvars!.
    forward.
    forward_call (gv, ctx, pl, x, h ++ (hs ++ hs'), (Zlength (m_slots mE)), Zlength addresses, (Zlength (m_slots mE)), 1, (if (Zlength (m_slots mE)) + 1 =? Zlength addresses then 1 else 0), 1).
    { rewrite (next_call_at _ _ _ _ _ _ R0 RG). reflexivity. }
    Intros q1. rewrite <- app_assoc.
    assert (G1: run x (tables_start x addresses m) ((hs ++ hs') ++ [(Sequence (Zlength (m_slots mE)) (Zlength addresses) (Zlength (m_slots mE)) 1 (if (Zlength (m_slots mE)) + 1 =? Zlength addresses then 1 else 0) 1, Word q1)]) = Some (Go (Sequencing (mk_tloop addresses (Zlength (m_slots mE)) (off + padded len) (Zlength (m_slots mE))) [q1]) (add_slot m' (mk_sdt (Znth (Zlength (m_slots mE)) addresses) off len (cursor mod 2 ^ 32)))))
      by (apply seq_more with (cur := []); [ exact RG | rewrite Zlength_nil; lia | reflexivity ]).
    forward. forward.
    forward_call (gv, ctx, pl, x, h ++ ((hs ++ hs') ++ [(Sequence (Zlength (m_slots mE)) (Zlength addresses) (Zlength (m_slots mE)) 1 (if (Zlength (m_slots mE)) + 1 =? Zlength addresses then 1 else 0) 1, Word q1)]), (Zlength (m_slots mE)), Zlength addresses, (Zlength (m_slots mE)), 1, (if (Zlength (m_slots mE)) + 1 =? Zlength addresses then 1 else 0), 2).
    { rewrite (next_call_at _ _ _ _ _ _ R0 G1). reflexivity. }
    Intros q2. rewrite <- app_assoc.
    assert (G2: run x (tables_start x addresses m) (((hs ++ hs') ++ [(Sequence (Zlength (m_slots mE)) (Zlength addresses) (Zlength (m_slots mE)) 1 (if (Zlength (m_slots mE)) + 1 =? Zlength addresses then 1 else 0) 1, Word q1)]) ++ [(Sequence (Zlength (m_slots mE)) (Zlength addresses) (Zlength (m_slots mE)) 1 (if (Zlength (m_slots mE)) + 1 =? Zlength addresses then 1 else 0) 2, Word q2)]) = Some (Go (Sequencing (mk_tloop addresses (Zlength (m_slots mE)) (off + padded len) (Zlength (m_slots mE))) [q1; q2]) (add_slot m' (mk_sdt (Znth (Zlength (m_slots mE)) addresses) off len (cursor mod 2 ^ 32)))))
      by (apply seq_more with (cur := [q1]); [ exact G1 | rewrite Zlength_cons, Zlength_nil; lia | reflexivity ]).
    forward. forward.
    forward_call (gv, ctx, pl, x, h ++ (((hs ++ hs') ++ [(Sequence (Zlength (m_slots mE)) (Zlength addresses) (Zlength (m_slots mE)) 1 (if (Zlength (m_slots mE)) + 1 =? Zlength addresses then 1 else 0) 1, Word q1)]) ++ [(Sequence (Zlength (m_slots mE)) (Zlength addresses) (Zlength (m_slots mE)) 1 (if (Zlength (m_slots mE)) + 1 =? Zlength addresses then 1 else 0) 2, Word q2)]), (Zlength (m_slots mE)), Zlength addresses, (Zlength (m_slots mE)), 1, (if (Zlength (m_slots mE)) + 1 =? Zlength addresses then 1 else 0), 3).
    { rewrite (next_call_at _ _ _ _ _ _ R0 G2). reflexivity. }
    Intros q3. rewrite <- app_assoc.
    assert (G3: run x (tables_start x addresses m) ((((hs ++ hs') ++ [(Sequence (Zlength (m_slots mE)) (Zlength addresses) (Zlength (m_slots mE)) 1 (if (Zlength (m_slots mE)) + 1 =? Zlength addresses then 1 else 0) 1, Word q1)]) ++ [(Sequence (Zlength (m_slots mE)) (Zlength addresses) (Zlength (m_slots mE)) 1 (if (Zlength (m_slots mE)) + 1 =? Zlength addresses then 1 else 0) 2, Word q2)]) ++ [(Sequence (Zlength (m_slots mE)) (Zlength addresses) (Zlength (m_slots mE)) 1 (if (Zlength (m_slots mE)) + 1 =? Zlength addresses then 1 else 0) 3, Word q3)]) =
      Some (if negb (q1 =? 1) || negb (q2 =? 0) || negb (q3 =? (Zlength (m_slots mE)) + 1) then Return S_SEQUENCE None (add_slot m' (mk_sdt (Znth (Zlength (m_slots mE)) addresses) off len (cursor mod 2 ^ 32)))
            else if (Zlength (m_slots mE)) + 1 <? Zlength addresses
                 then begin_table x (mk_tloop addresses ((Zlength (m_slots mE)) + 1) (off + padded len) q3) (add_slot m' (mk_sdt (Znth (Zlength (m_slots mE)) addresses) off len (cursor mod 2 ^ 32)))
                 else tables_done (Zlength addresses) (add_slot m' (mk_sdt (Znth (Zlength (m_slots mE)) addresses) off len (cursor mod 2 ^ 32)))))
      by (apply seq_last with (l := (mk_tloop addresses (Zlength (m_slots mE)) (off + padded len) (Zlength (m_slots mE)))); [ exact G2 | reflexivity ]).
    forward.
    forward_if (temp _t'7 (Vint (bint (negb (q1 =? 1) || negb (q2 =? 0))))).
    { w64. forward. entailer!. rewrite (proj2 (Z.eqb_neq q1 1)) by assumption. reflexivity. }
    { w64. forward. entailer!. rewrite cmpu_ne64, bool2val_bint by (unfold u64_ok in *; rep_lia). reflexivity. }
    forward_if (temp _t'8 (Vint (bint (negb (q1 =? 1) || negb (q2 =? 0) || negb (q3 =? Zlength (m_slots mE) + 1))))).
    { bfix. forward. entailer!. match goal with H: (_ || _) = true |- _ => rewrite H end. reflexivity. }
    { bfix. forward. entailer!. match goal with H: (_ || _) = false |- _ => rewrite H end.
      rewrite cmpu_ne64, bool2val_bint by (unfold u64_ok in *; rep_lia). reflexivity. }
    forward_if.
    { (* the copy sequence rejected the step *)
      bfix. match goal with H: (_ || _ || _) = true |- _ => rename H into BAD end.
      rewrite BAD in G3.
      forward.
      match goal with |- context [Ora gv ctx pl x (h ++ ?hh)] => Exists hh S_SEQUENCE (add_slot m' (mk_sdt (Znth (Zlength (m_slots mE)) addresses) off len (cursor mod 2 ^ 32))) end.
      fix_status S_SEQUENCE.
      entailer!; try discriminate. }
    bfix. match goal with H: (_ || _ || _) = false |- _ => rename H into GOOD end.
    rewrite GOOD in G3.
    apply orb_false_iff in GOOD as [GOOD G3e]. apply orb_false_iff in GOOD as [G1e G2e].
    apply negb_false_iff, Z.eqb_eq in G1e, G2e, G3e.
    rewrite G3e in G3.
    forward.
    match goal with |- context [Ora gv ctx pl x (h ++ ?hh)] => Exists (off + padded len) hh (add_slot m' (mk_sdt (Znth (Zlength (m_slots mE)) addresses) off len (cursor mod 2 ^ 32))) end.
    rewrite Q5. replace ((Zlength (m_slots mE)) + 1 - 1) with (Zlength (m_slots mE)) by lia.
    entailer!. }
  { Intros off hs mE. forward. Exists off hs mE. entailer!. f_equal. f_equal. lia. }
  Intros off hs mE.
  match goal with H: Zlength (m_slots mE) = Zlength addresses |- _ => rename H into EL end.
  forward.
  forward_if.
  { exfalso. match goal with H: Int64.repr _ <> _ |- _ => apply H end.
    rewrite Int.unsigned_repr by rep_lia. reflexivity. }
  forward. forward. forward.
  Exists hs S_OK mE.
  assert (SO: status_ok S_OK) by reflexivity.
  rewrite Z.eqb_refl. cbv iota.
  entailer!.
Qed.
