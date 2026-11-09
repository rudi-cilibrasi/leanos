(* The bodies of acpi_copy_root_and_tables (the selection check, the root's copy into result->root, its validation,
   its entries into result->entries, its addresses into the local array, the tables, the MADT selection and the
   result's count and MADT) and acpi_pipeline (one call); against `start`, `root_copied` and `tables_done`.
   ROOT_COPY, ROOT_VECTOR, INCOMPLETE and MADT_SELECTION cannot fail: each tests what the pipeline just computed. *)
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

Lemma root_copied_eq: forall x len cursor m, root_copied x len cursor m =
  (if negb (validate len (m_root m) (Some (if i_kind x =? 1 then RSDT else XSDT)) =? S_OK)
   then Return (validate len (m_root m) (Some (if i_kind x =? 1 then RSDT else XSDT))) None
          (set_root_copy m (mk_sdt (i_address x) 0 len (cursor mod 2 ^ 32)))
   else match decode_entries (i_kind x) len with
        | inl st => Return st None (set_root_copy m (mk_sdt (i_address x) 0 len (cursor mod 2 ^ 32)))
        | inr (count, w) =>
          match decode_addresses (sublist HEADER_BYTES (Zlength (m_root m)) (m_root m)) w count with
          | inl st => Return st None (set_entries (set_root_copy m (mk_sdt (i_address x) 0 len (cursor mod 2 ^ 32))) count w)
          | inr addrs => tables_start x addrs (set_entries (set_root_copy m (mk_sdt (i_address x) 0 len (cursor mod 2 ^ 32))) count w)
          end
        end).
Proof. reflexivity. Qed.

Lemma sdt_copied_root: forall x len cursor m, sdt_copied x TRoot len cursor m = root_copied x len cursor m.
Proof. reflexivity. Qed.

Lemma tables_done_eq: forall count m, tables_done count m =
  match select_from (m_tables m) (m_slots m) 0 None with
  | inl st => Return st None m
  | inr i => Return S_OK (Some (count, i)) m
  end.
Proof. reflexivity. Qed.

Lemma decode_entries_inr_w: forall len count w ww, 0 < ww ->
  (if len <? HEADER_BYTES then inl S_ROOT_HEADER
   else if negb ((len - HEADER_BYTES) mod ww =? 0) then inl S_ROOT_WIDTH
   else if MAX_ENTRIES <? (len - HEADER_BYTES) / ww then inl S_ROOT_ENTRIES
   else inr ((len - HEADER_BYTES) / ww, ww)) = inr (count, w) ->
  w = ww /\ HEADER_BYTES <= len /\ len - HEADER_BYTES = count * w /\ 0 <= count <= MAX_ENTRIES.
Proof.
  intros len count w ww P H.
  destruct (len <? HEADER_BYTES) eqn:L; [ discriminate | ].
  destruct (negb ((len - HEADER_BYTES) mod ww =? 0)) eqn:M; [ discriminate | ].
  destruct (MAX_ENTRIES <? (len - HEADER_BYTES) / ww) eqn:C; [ discriminate | ].
  injection H as <- <-.
  apply Z.ltb_ge in L. apply negb_false_iff, Z.eqb_eq in M. apply Z.ltb_ge in C.
  split; [ auto | split; [ auto | split ] ].
  - fold (Z.div (len - HEADER_BYTES) ww). rewrite (Z.div_mod (len - HEADER_BYTES) ww) at 1 by lia. rewrite M. ring.
  - fold (Z.div (len - HEADER_BYTES) ww). split; [ apply Z.div_pos; unfold HEADER_BYTES in *; lia | auto ].
Qed.

Lemma decode_entries_inr: forall k len count w, decode_entries k len = inr (count, w) ->
  (w = 4 \/ w = 8) /\ HEADER_BYTES <= len /\ len - HEADER_BYTES = count * w /\ 0 <= count <= MAX_ENTRIES /\
  (if k =? 1 then 4 else 8) = w.
Proof.
  intros. unfold decode_entries in H.
  destruct (Z.eq_dec k 1) as [K1 | K1]; [ | destruct (Z.eq_dec k 2) as [K2 | K2] ].
  - subst k. change (if 1 =? 1 then 4 else if 1 =? 2 then 8 else 0) with 4 in H. cbv zeta in H.
    change (4 =? 0) with false in H. cbv iota in H.
    apply decode_entries_inr_w in H as (E & A & B & C); [ subst w | lia ]. auto 6.
  - subst k. change (if 2 =? 1 then 4 else if 2 =? 2 then 8 else 0) with 8 in H. cbv zeta in H.
    change (8 =? 0) with false in H. cbv iota in H.
    apply decode_entries_inr_w in H as (E & A & B & C); [ subst w | lia ]. auto 6.
  - rewrite (proj2 (Z.eqb_neq _ _) K1), (proj2 (Z.eqb_neq _ _) K2) in H. discriminate.
Qed.

Lemma decode_entries_inl_range: forall k l st, decode_entries k l = inl st -> 19 <= st <= 22.
Proof.
  unfold decode_entries. intros k l st H.
  repeat match type of H with context [if ?b then _ else _] => destruct b end;
    inversion H; subst; unfold S_ROOT_KIND, S_ROOT_HEADER, S_ROOT_WIDTH, S_ROOT_ENTRIES; lia.
Qed.

Lemma validate_range': forall len bs sig, validate len bs sig = S_OK \/ validate len bs sig = S_SDT_ENVELOPE \/
  validate len bs sig = S_SDT_CHECKSUM.
Proof. intros. unfold validate. destruct (_ || _); [ auto | ]. destruct (negb _); auto. Qed.

Lemma validate_zero': forall len bs sig, Int.repr (validate len bs sig) = Int.repr 0 -> validate len bs sig = S_OK.
Proof.
  intros. destruct (validate_range' len bs sig) as [E | [E | E]]; auto; rewrite E in *;
    apply (f_equal Int.unsigned) in H; unfold S_SDT_ENVELOPE, S_SDT_CHECKSUM in H;
    rewrite !Int.unsigned_repr in H by rep_lia; discriminate.
Qed.

Lemma select_from_some: forall T ss k sel i, select_from T ss k sel = inr i ->
  sel = Some i \/
  (k <= i < k + Zlength ss /\
   signature_matches (s_length (Znth (i - k) ss)) (sublist (s_offset (Znth (i - k) ss)) (Zlength T) T) APIC = true).
Proof.
  induction ss as [ | s ss IH]; intros k sel i H; simpl in H.
  - destruct sel; inversion H; auto.
  - destruct (negb (validate _ _ None =? S_OK)); [ discriminate | ].
    destruct (signature_matches (s_length s) (sublist (s_offset s) (Zlength T) T) APIC) eqn:SM.
    + destruct sel; [ discriminate | ].
      destruct (IH _ _ _ H) as [E | (R & S')]; [ inversion E; subst | ]; right; rewrite Zlength_cons.
      * replace (i - i) with 0 by lia. rewrite Znth_0_cons. pose proof (Zlength_nonneg ss). split; [ lia | auto ].
      * replace (i - k) with (i - (k + 1) + 1) by lia. rewrite Znth_pos_cons by lia.
        replace (i - (k + 1) + 1 - 1) with (i - (k + 1)) by lia. split; [ lia | auto ].
    + destruct (IH _ _ _ H) as [E | (R & S')]; [ left; auto | right; rewrite Zlength_cons ].
      replace (i - k) with (i - (k + 1) + 1) by lia. rewrite Znth_pos_cons by lia.
      replace (i - (k + 1) + 1 - 1) with (i - (k + 1)) by lia. split; [ lia | auto ].
Qed.

Lemma select_from_madt: forall T ss i, select_from T ss 0 None = inr i ->
  0 <= i < Zlength ss /\ signature_matches (s_length (Znth i ss)) (sublist (s_offset (Znth i ss)) (Zlength T) T) APIC = true.
Proof.
  intros. destruct (select_from_some T ss 0 None i H) as [E | (R & S')]; [ discriminate | ].
  rewrite Z.sub_0_r in S'. split; [ lia | auto ].
Qed.

Lemma lits_swap: forall (b: bool) (p3 p2: val),
  sepcon (literal (if b then RSDT else XSDT) (if b then p3 else p2))
         (literal (if b then XSDT else RSDT) (if b then p2 else p3)) =
  sepcon (literal RSDT p3) (literal XSDT p2).
Proof. intros [ | ] p3 p2; [ reflexivity | apply sepcon_comm ]. Qed.

Lemma decode_from_inl_range: forall vec w es pre st, decode_from vec w es pre = inl st -> 25 <= st <= 26.
Proof.
  induction es as [ | e es IH]; simpl; intros pre st H; [ discriminate | ].
  repeat match type of H with context [if ?b then _ else _] => destruct b end;
    try (inversion H; subst; unfold S_ROOT_ENTRY_ADDRESS, S_ROOT_ENTRY_DUPLICATE; lia); eauto.
Qed.

Lemma select_from_inl_range: forall T ss i sel st, select_from T ss i sel = inl st -> 17 <= st <= 32.
Proof.
  induction ss as [ | s ss IH]; simpl; intros i sel st H.
  - destruct sel; inversion H; subst; unfold S_MADT_MISSING; lia.
  - destruct (negb (validate (s_length s) (sublist (s_offset s) (Zlength T) T) None =? S_OK)) eqn:E.
    + inversion H; subst. destruct (validate_range' (s_length s) (sublist (s_offset s) (Zlength T) T) None)
        as [V | [V | V]]; rewrite V in *; [ discriminate | unfold S_SDT_ENVELOPE | unfold S_SDT_CHECKSUM ]; lia.
    + destruct (signature_matches _ _ _); [ destruct sel; [ inversion H; subst; unfold S_MADT_DUPLICATE; lia | ] | ];
        eauto.
Qed.

Lemma weak_valid_at: forall sh n (l: list val) p k, readable_share sh -> 0 <= k <= n -> 0 < n ->
  data_at sh (tarray tuchar n) l p |-- weak_valid_pointer (offset_val k p).
Proof.
  intros. eapply derives_trans; [ apply data_at_memory_block | ].
  apply memory_block_weak_valid_pointer; [ simpl sizeof; rewrite Z.max_r by lia; lia | simpl sizeof; rewrite Z.max_r by lia; lia | ].
  apply readable_nonidentity; auto.
Qed.

#[local] Transparent denote_tc_test_eq.
Lemma test_eq_self_weak: forall P q, isptr q -> (P |-- weak_valid_pointer q) -> P |-- denote_tc_test_eq q q.
Proof.
  intros. destruct q; try contradiction. unfold denote_tc_test_eq, test_eq_ptrs. simpl.
  unfold sameblock. destruct (peq b b); [ | congruence ]. simpl. apply andp_right; auto.
Qed.
#[local] Opaque denote_tc_test_eq.

#[local] Hint Extern 1 (data_at _ (tarray tuchar _) _ _ |-- weak_valid_pointer (offset_val _ _)) =>
  (apply weak_valid_at; [ auto | lia | lia ]) : valid_pointer.

Ltac kill_branch :=
  exfalso; first [ contradiction | discriminate | match goal with H: _ <> _ |- _ => apply H; reflexivity end
                 | match goal with H: Int.one = Int.zero |- _ => exact (Int.one_not_zero H) end ].

Lemma repr_status_zero: forall st, 0 < st <= 64 -> Int.repr st <> Int.repr 0.
Proof. intros st B E. apply repr_inj_unsigned in E; [ lia | rep_lia | rep_lia ]. Qed.

Lemma sdt_val_root: forall p a len c, isptr p -> sdt_val p (mk_sdt a 0 len c) = (vl a, (p, (vi len, vi c))).
Proof. intros. unfold sdt_val. cbn [s_address s_offset s_length s_next]. rewrite isptr_offset_val_zero by auto. reflexivity. Qed.

Lemma sdt_val_unfold: forall tp s,
  sdt_val tp s = (vl (s_address s), (offset_val (s_offset s) tp, (vi (s_length s), vi (s_next s)))).
Proof. reflexivity. Qed.

Ltac dead_status :=
  exfalso;
  match goal with
  | H: Int.repr ?a = Int.repr 0 |- _ => apply (repr_status_zero a); [ | exact H ]
  | H: Int.repr ?a = Int.zero |- _ => apply (repr_status_zero a); [ | exact H ]
  end;
  repeat match goal with E: _ = inl _ |- _ => rewrite E end; simpl status_of; lia.


Lemma decode_addresses_inl_range: forall vec w count st, decode_addresses vec w count = inl st -> 25 <= st <= 26.
Proof. intros. unfold decode_addresses in H. eapply decode_from_inl_range; eauto. Qed.

Lemma decode_addresses_inr_facts: forall vec w count addrs, decode_addresses vec w count = inr addrs ->
  Forall byte_ok vec -> 0 <= count -> Zlength addrs = count /\ Forall addr_ok addrs.
Proof.
  intros. unfold decode_addresses in H. apply decode_from_inr in H; auto.
  rewrite Zlength_nil, Zlength_range in H by auto. destruct H; split; auto; lia.
Qed.

Lemma lits_to: forall (b: bool) (p3 p2: val),
  sepcon (literal RSDT p3) (literal XSDT p2) |--
  sepcon (literal (if b then RSDT else XSDT) (if b then p3 else p2))
         (literal (if b then XSDT else RSDT) (if b then p2 else p3)).
Proof. intros. rewrite lits_swap. apply derives_refl. Qed.

Lemma lits_from: forall (b: bool) (p3 p2: val),
  sepcon (literal (if b then RSDT else XSDT) (if b then p3 else p2))
         (literal (if b then XSDT else RSDT) (if b then p2 else p3)) |--
  sepcon (literal RSDT p3) (literal XSDT p2).
Proof. intros. rewrite lits_swap. apply derives_refl. Qed.

#[local] Opaque run step sdt_copied root_copied table_copied tables_done begin_sdt begin_table tables_start
  validate decode_entries decode_addresses select_from signature_matches.

(* The result record, field by field. *)
Lemma result_split: forall sh (r: sdt_rep) (e: entries_rep) (c d: val) res,
  data_at sh t_result (r, (e, (c, d))) res =
  (data_at sh t_sdt r (field_address t_result (DOT _root) res) *
   data_at sh t_entries e (field_address t_result (DOT _entries) res) *
   field_at sh t_result (DOT _table_count) c res * spacer sh 44 48 res *
   field_at sh t_result (DOT _madt) d res)%logic.
Proof.
  intros. unfold_data_at (data_at sh t_result _ res).
  rewrite (field_at_data_at sh t_result (DOT _root)), (field_at_data_at sh t_result (DOT _entries)).
  change (nested_field_type t_result (DOT _root)) with t_sdt.
  change (nested_field_type t_result (DOT _entries)) with t_entries.
  apply pred_ext; cancel.
Qed.

Lemma pipeline_of: forall x h st pub m, run x (start x) h = Some (Return st pub m) -> pipeline x h = Some (st, pub, m).
Proof. intros. unfold pipeline. rewrite H. reflexivity. Qed.

Lemma start_fail: forall x, ((i_kind x <> 1 /\ i_kind x <> 2) \/ i_address x = 0) ->
  start x = Return S_ROOT_SELECTION None (initial x).
Proof.
  intros. unfold start. destruct H as [[A B] | C].
  - rewrite (proj2 (Z.eqb_neq _ _) A), (proj2 (Z.eqb_neq _ _) B). reflexivity.
  - rewrite C, Z.eqb_refl, orb_true_r. reflexivity.
Qed.

Lemma start_go: forall x, (i_kind x = 1 \/ i_kind x = 2) -> i_address x <> 0 -> start x = begin_sdt x TRoot (initial x).
Proof.
  intros. unfold start. rewrite (proj2 (Z.eqb_neq _ _) H0).
  destruct H as [-> | ->]; reflexivity.
Qed.

Lemma slots_val_initial: forall pl x (sold: list sdt_rep), Zlength sold = MAX_ENTRIES ->
  slots_val pl (initial x) sold = sold.
Proof. intros. unfold slots_val. simpl. apply sublist_same; auto. Qed.

Lemma slots_val_nil': forall pl m (sold: list sdt_rep), m_slots m = [] -> Zlength sold = MAX_ENTRIES ->
  slots_val pl m sold = sold.
Proof. intros. unfold slots_val. rewrite H. simpl. apply sublist_same; auto. Qed.

Lemma region_root_all: forall x m, mem_ok x m -> region m DRoot (root_capacity x) = m_root m.
Proof. intros x m (_ & R & _). simpl. apply sublist_same; auto. Qed.

Lemma body_acpi_copy_root_and_tables (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_acpi_copy_root_and_tables (copy_root_and_tables_spec Ora).
Proof.
  start_function.
  rename H into IX. rename H0 into LS.
  pose proof IX as IX'. destruct IX' as (UK & UA & HL & RC & TC & BH & BR & BT).
  unfold u64_ok in UK, UA.
  forward_if (temp _t'1 (Vint (bint (negb ((i_kind x =? 1) || (i_kind x =? 2)))))).
  { w64. forward. entailer!. rewrite cmpu_ne64, bool2val_bint by (unfold u64_ok; rep_lia).
    rewrite (proj2 (Z.eqb_neq _ 1)) by auto. reflexivity. }
  { w64. match goal with H: i_kind x = 1 |- _ => rename H into K1 end. forward. entailer!. rewrite K1. reflexivity. }
  forward_if (temp _t'2 (Vint (bint (negb ((i_kind x =? 1) || (i_kind x =? 2)) || (i_address x =? 0))))).
  { bfix. forward. entailer!. match goal with H: negb _ = true |- _ => rewrite H end. reflexivity. }
  { bfix. forward. entailer!. match goal with H: negb _ = false |- _ => rewrite H end.
    rewrite cmpu_eq64, bool2val_bint by (unfold u64_ok; rep_lia). reflexivity. }
  forward_if.
  { (* the selection is not RSDT/XSDT, or its address is 0 *)
    bfix. match goal with H: (_ || _) = true |- _ => rename H into BADSEL end.
    assert (P: pipeline x [] = Some (S_ROOT_SELECTION, None, initial x)).
    { apply pipeline_of. rewrite run_nil. f_equal. unfold start. rewrite BADSEL. reflexivity. }
    forward.
    Exists (@nil answer) S_ROOT_SELECTION (@None (Z * Z)) (initial x).
    unfold result_val. cbn [m_root_copy m_entries m_header m_root m_tables initial].
    rewrite slots_val_initial by auto.
    entailer!. }
  bfix. match goal with H: (_ || _) = false |- _ => rename H into SEL end.
  apply orb_false_iff in SEL as [SK SA]. apply negb_false_iff, orb_true_iff in SK. apply Z.eqb_neq in SA.
  assert (KK: i_kind x = 1 \/ i_kind x = 2) by (destruct SK as [E | E]; apply Z.eqb_eq in E; auto).
  clear SK.
  assert_PROP (field_compatible t_result [] res) as FCr by entailer!.
  assert (FCr1: field_compatible t_result (DOT _root) res) by auto with field_compatible.
  assert (FCr2: field_compatible t_result (DOT _entries) res) by auto with field_compatible.
  assert (FA1: field_address t_result (DOT _root) res = offset_val 0 res)
    by (rewrite field_address_offset by auto; reflexivity).
  assert (FA2: field_address t_result (DOT _entries) res = offset_val 24 res)
    by (rewrite field_address_offset by auto; reflexivity).
  rewrite (result_split osh rroot rentries rcount rmadt res). rewrite FA1, FA2. Intros.
  forward.
  replace (align 0 (bitalignof cenv_cs (Tstruct _copied_acpi_sdt noattr)) / 8) with 0 by reflexivity.
  unfold storage_val. forward. forward. forward.
  assert (R0: run x (start x) [] = Some (begin_sdt x TRoot (initial x))) by (rewrite run_nil, start_go by auto; reflexivity).
  assert (M0: mem_ok x (initial x)) by (repeat split; simpl; auto).
  replace (bytes_val (i_root x)) with (bytes_val (region (initial x) (dest_of TRoot) (capacity_of x TRoot)))
    by (simpl; rewrite sublist_same by (unfold root_capacity; lia); reflexivity).
  replace (bytes_val (i_header x)) with (bytes_val (m_header (initial x))) by reflexivity.
  forward_call (gv, copy, ctx, pl, sh, x, @nil answer, TRoot, initial x, osh, offset_val 0 res, rroot).
  Intros vret. destruct vret as [[[[hs1 st1] m1] len] cursor]. cbn [fst snd] in *.
  match goal with H: run _ (begin_sdt _ _ _) hs1 = _ |- _ => rename H into R1 end.
  match goal with H: mem_ok x m1 |- _ => rename H into M1 end.
  match goal with H: copy_frame TRoot _ m1 |- _ => rename H into CF end.
  match goal with H: status_ok st1 |- _ => rename H into SO1 end.
  match goal with H: st1 = S_OK -> _ |- _ => rename H into OK1 end.
  cbn [copy_frame capacity_of dest_of dest_ptr address_of offset_of base_of cursor_of initial
       m_header m_root m_tables m_root_copy m_entries m_slots] in *.
  destruct CF as (CF1 & CF2 & CF3 & CF4 & CF5 & CF6 & CF7).
  rewrite app_nil_l.
  rewrite (region_root_all x m1 M1).
  assert (RS1: run x (start x) hs1 = run x (begin_sdt x TRoot (initial x)) hs1) by (rewrite start_go; auto).
  unfold vi.
  forward. forward_if.
  { (* the root's copy failed *)
    assert (ST: (st1 =? S_OK) = false)
      by (apply Z.eqb_neq; intro Es; subst st1; match goal with H: Int.repr _ <> Int.repr _ |- _ => apply H; reflexivity end).
    rewrite ST in R1 |- *. cbv iota.
    assert (P: pipeline x hs1 = Some (st1, None, m1)) by (apply pipeline_of; rewrite RS1; exact R1).
    forward.
    Exists hs1 st1 (@None (Z * Z)) m1.
    unfold result_val. rewrite CF4, CF5. cbn [m_root_copy m_entries initial]. cbv iota.
    rewrite CF7, (slots_val_nil' pl m1 sold) by auto.
    rewrite result_split, FA1, FA2.
    entailer!. }
  assert (ST: st1 = S_OK) by (apply status_ok_repr; auto).
  subst st1. rewrite Z.eqb_refl in R1 |- *. cbv iota.
  destruct (OK1 eq_refl) as (L1 & L2 & UC). clear OK1. unfold HEADER_BYTES, MAX_SDT_BYTES in L1.
  rewrite sdt_copied_root, root_copied_eq in R1.
  assert_PROP (isptr (p_root pl)) as IPR by entailer!.
  assert (MR1: Zlength (m_root m1) = root_capacity x) by (destruct M1 as (_ & A & _); auto).
  assert (BR1: Forall byte_ok (m_root m1)) by (destruct M1 as (_ & _ & _ & _ & A & _); auto).
  unfold sdt_val at 1. cbn [s_address s_offset s_length s_next]. rewrite (isptr_offset_val_zero (p_root pl)) by auto.
  unfold vl, vi.
  forward.
  forward_if (temp _t'4 (Vint (Int.repr 0))).
  { exfalso. auto. }
  { forward. forward. forward.
    all: entailer!.
    all: try (apply denote_tc_test_eq_split; auto 50 with valid_pointer).
    all: try (destruct (eq_dec (p_root pl) (p_root pl)) as [_ | C]; [ reflexivity | contradiction C; reflexivity ]). }
  forward_if (temp _t'5 (Vint (Int.repr 0))).
  { exfalso. auto. }
  { forward. forward. entailer!. rewrite zlt_ltb, (proj2 (Z.ltb_ge len 36)) by lia. reflexivity. }
  forward_if; [ exfalso; auto | ].
  forward_if (temp _t'6 (if i_kind x =? 1 then gv ___stringlit_acpi_3 else gv ___stringlit_acpi_2)).
  { w64. forward. entailer!. rewrite (proj2 (Z.eqb_eq _ _)) by assumption. reflexivity. }
  { w64. forward. entailer!. rewrite (proj2 (Z.eqb_neq _ _)) by assumption. reflexivity. }
  sep_apply (lits_to (i_kind x =? 1) (gv ___stringlit_acpi_3) (gv ___stringlit_acpi_2)). Intros.
  rewrite <- MR1.
  forward_call (osh, res, Vlong (Int64.repr (i_address x)), len, Vint (Int.repr (cursor mod 2 ^ 32)),
                p_root pl, sh, m_root m1, if i_kind x =? 1 then gv ___stringlit_acpi_3 else gv ___stringlit_acpi_2,
                Some (if i_kind x =? 1 then RSDT else XSDT)).
  { split; [ unfold u32_ok; lia | ].
    destruct (i_kind x =? 1); (split; [ reflexivity | unfold RSDT, XSDT; repeat constructor; lia ]). }
  sep_apply (lits_from (i_kind x =? 1) (gv ___stringlit_acpi_3) (gv ___stringlit_acpi_2)).
  rewrite MR1. Intros.
  forward. unfold vi.
  assert (MS1: m_slots m1 = []) by auto.
  forward_if.
  { (* the root is not a valid RSDT or XSDT *)
    assert (VN: (negb ((validate len (m_root m1) (Some (if i_kind x =? 1 then RSDT else XSDT))) =? S_OK)) = true)
      by (apply negb_true_iff, Z.eqb_neq; intro E; rewrite E in *;
          match goal with H: Int.repr _ <> Int.repr _ |- _ => apply H; reflexivity end).
    rewrite VN in R1.
    assert (P: pipeline x hs1 = Some ((validate len (m_root m1) (Some (if i_kind x =? 1 then RSDT else XSDT))), None, (set_root_copy m1 (mk_sdt (i_address x) 0 len (cursor mod 2 ^ 32))))) by (apply pipeline_of; rewrite RS1; exact R1).
    forward.
    Exists hs1 (validate len (m_root m1) (Some (if i_kind x =? 1 then RSDT else XSDT))) (@None (Z * Z)) (set_root_copy m1 (mk_sdt (i_address x) 0 len (cursor mod 2 ^ 32))).
    unfold result_val. cbn [m_header m_root m_tables m_root_copy m_entries m_slots set_root_copy].
    rewrite CF5. cbv iota.
    rewrite CF7, slots_val_nil' by (cbn [m_slots set_root_copy set_entries]; auto).
    rewrite result_split, FA1, FA2. unfold sdt_val. cbn [s_address s_offset s_length s_next].
    rewrite (isptr_offset_val_zero (p_root pl)) by auto.
    entailer!. }
  assert (VO: (validate len (m_root m1) (Some (if i_kind x =? 1 then RSDT else XSDT))) = S_OK) by (apply validate_zero'; match goal with H: Int.repr _ = Int.repr 0 |- _ => exact H end).
  forward.
  replace (align (next_field cenv_cs 0 (Member_plain _root (Tstruct _copied_acpi_sdt noattr)))
             (bitalignof cenv_cs (Tstruct _acpi_root_entries noattr)) / 8) with 24 by reflexivity.
  forward_call (osh, res, Vlong (Int64.repr (i_address x)), p_root pl, len, Vint (Int.repr (cursor mod 2 ^ 32)),
                i_kind x, osh, offset_val 24 res, rentries).
  { split; unfold u32_ok, u64_ok; rep_lia. }
  destruct (decode_entries (i_kind x) len) as [st2 | [count w]] eqn:DE.
  { (* the root's length does not fit its kind *)
    pose proof (decode_entries_inl _ _ _ DE) as NZ.
    assert (P: pipeline x hs1 = Some (st2, None, (set_root_copy m1 (mk_sdt (i_address x) 0 len (cursor mod 2 ^ 32))))).
    { apply pipeline_of. rewrite RS1, R1, VO. rewrite ?DE. reflexivity. }
    pose proof (decode_entries_inl_range _ _ _ DE) as NR.
    unfold vi.
    forward_if; [ | exfalso; apply NZ; apply repr32_inj; auto; unfold u32_ok, S_OK; rep_lia ].
    forward.
    Exists hs1 st2 (@None (Z * Z)) (set_root_copy m1 (mk_sdt (i_address x) 0 len (cursor mod 2 ^ 32))).
    unfold result_val. cbn [m_header m_root m_tables m_root_copy m_entries m_slots set_root_copy].
    rewrite CF5. cbv iota.
    rewrite CF7, slots_val_nil' by (cbn [m_slots set_root_copy set_entries]; auto).
    rewrite result_split, FA1, FA2. unfold sdt_val. cbn [s_address s_offset s_length s_next].
    rewrite (isptr_offset_val_zero (p_root pl)) by auto.
    entailer!. }
  destruct (decode_entries_inr _ _ _ _ DE) as (W & L36' & PL & CNT & EW). clear EW.
  unfold HEADER_BYTES, MAX_ENTRIES in L36', PL, CNT.
  assert (R3: run x (begin_sdt x TRoot (initial x)) hs1 =
              Some (match decode_addresses (sublist HEADER_BYTES (Zlength (m_root m1)) (m_root m1)) w count with
                    | inl st => Return st None (set_entries (set_root_copy m1 (mk_sdt (i_address x) 0 len (cursor mod 2 ^ 32))) count w)
                    | inr addrs => tables_start x addrs (set_entries (set_root_copy m1 (mk_sdt (i_address x) 0 len (cursor mod 2 ^ 32))) count w)
                    end)) by (rewrite R1, VO; rewrite ?DE; reflexivity).
  clear R1.
  unfold vi. simpl status_of.
  forward_if; [ kill_branch | ].
  unfold entries_val.
  forward. forward.
  assert_PROP (field_compatible (tarray tuchar (root_capacity x)) [] (p_root pl)) as FCR by entailer!.
  forward_if (temp _t'9 (Vint (Int.repr 0))).
  { entailer!. apply test_eq_self_weak; [ auto | auto 50 with valid_pointer ]. }
  { exfalso. match goal with H: offset_val _ _ <> _ |- _ => apply H end.
    generalize IPR. destruct (p_root pl); intro; try contradiction; reflexivity. }
  { forward. forward_if.
    { forward. forward. forward. entailer!.
      destruct W as [E | E]; rewrite E;
        [ exfalso; match goal with H: _ <> 4 |- _ => apply H; exact E end | reflexivity ]. }
    { forward. entailer!. } }
  forward_if; [ kill_branch | ].
  rewrite (split2_bytes sh (m_root m1) (root_capacity x) 36 (p_root pl) MR1 ltac:(lia) FCR). Intros.
  assert (EV: sublist 36 (root_capacity x) (m_root m1) = (sublist HEADER_BYTES (Zlength (m_root m1)) (m_root m1))) by (unfold HEADER_BYTES; rewrite MR1; reflexivity).
  assert (LV: root_capacity x - 36 = Zlength (sublist HEADER_BYTES (Zlength (m_root m1)) (m_root m1))) by (unfold HEADER_BYTES; rewrite Zlength_sublist by lia; lia).
  rewrite EV, LV.
  change (data_at_ Tsh (tarray tulong 256) v_root_table_addresses)
    with (data_at Tsh (tarray tulong MAX_ENTRIES) (Zrepeat Vundef MAX_ENTRIES) v_root_table_addresses).
  forward_call (osh, offset_val 24 res, offset_val 36 (p_root pl), count, w, sh, (sublist HEADER_BYTES (Zlength (m_root m1)) (m_root m1)), Tsh,
                v_root_table_addresses, Zrepeat Vundef MAX_ENTRIES).
  { repeat match goal with |- _ /\ _ => split end; auto;
      try (apply Forall_sublist; auto); try (rewrite Zlength_Zrepeat by (unfold MAX_ENTRIES; lia); reflexivity);
      try (generalize IPR; destruct (p_root pl); simpl; intro; first [ contradiction | exact I ]);
      unfold MAX_ENTRIES, HEADER_BYTES in *; rewrite ?Zlength_sublist by lia; rep_lia. }
  Intros aout.
  match goal with H: Zlength aout = MAX_ENTRIES |- _ => rename H into LAO end.
  match goal with H: context [aout] |- _ =>
    match type of H with Zlength _ = _ => fail 1 | _ => rename H into AO end end.
  rewrite <- LV, <- EV.
  sep_apply (join2_bytes sh (m_root m1) (root_capacity x) 36 (p_root pl) MR1 ltac:(lia) FCR).
  rewrite EV.
  destruct (decode_addresses (sublist HEADER_BYTES (Zlength (m_root m1)) (m_root m1)) w count) as [st3 | addrs] eqn:DA.
  { (* an entry is 0, wider than 32 bits or a duplicate *)
    pose proof (decode_addresses_inl_range _ _ _ _ DA) as NR3.
    assert (P: pipeline x hs1 = Some (st3, None, (set_entries (set_root_copy m1 (mk_sdt (i_address x) 0 len (cursor mod 2 ^ 32))) count w))).
    { apply pipeline_of. rewrite RS1, R3. rewrite ?DA. reflexivity. }
    unfold vi. simpl status_of.
    forward_if; [ | dead_status ].
    forward.
    Exists hs1 st3 (@None (Z * Z)) (set_entries (set_root_copy m1 (mk_sdt (i_address x) 0 len (cursor mod 2 ^ 32))) count w).
    unfold result_val. cbn [m_header m_root m_tables m_root_copy m_entries m_slots set_root_copy set_entries].
    cbv iota.
    rewrite result_split, FA1, FA2. unfold sdt_val, entries_val. cbn [s_address s_offset s_length s_next].
    rewrite (isptr_offset_val_zero (p_root pl)) by auto.
    rewrite CF7, slots_val_nil' by (cbn [m_slots set_root_copy set_entries]; auto).
    entailer!. }
  unfold vi. simpl status_of.
  forward_if; [ kill_branch | ].
  destruct (decode_addresses_inr_facts _ _ _ _ DA ltac:(apply Forall_sublist; auto) ltac:(lia)) as (LA & FA).
  rewrite ?DA in AO. cbv iota in AO. subst aout. subst count.
  assert (RT: run x (start x) hs1 = Some (tables_start x addrs (set_entries (set_root_copy m1 (mk_sdt (i_address x) 0 len (cursor mod 2 ^ 32))) (Zlength addrs) w))) by (rewrite RS1, R3; rewrite ?DA; reflexivity).
  assert (MME: mem_ok x (set_entries (set_root_copy m1 (mk_sdt (i_address x) 0 len (cursor mod 2 ^ 32))) (Zlength addrs) w)) by exact M1.
  assert (SME: m_slots (set_entries (set_root_copy m1 (mk_sdt (i_address x) 0 len (cursor mod 2 ^ 32))) (Zlength addrs) w) = []) by exact MS1.
  assert (LA256: Zlength addrs <= MAX_ENTRIES) by (unfold MAX_ENTRIES; lia).
  assert (FA': Forall (fun a => 0 < a <= MAX_U32) addrs) by exact FA.
  change (bytes_val (i_tables x)) with (bytes_val (m_tables (initial x))). rewrite <- CF7. change (m_header m1) with (m_header (set_entries (set_root_copy m1 (mk_sdt (i_address x) 0 len (cursor mod 2 ^ 32))) (Zlength addrs) w)). change (m_tables m1) with (m_tables (set_entries (set_root_copy m1 (mk_sdt (i_address x) 0 len (cursor mod 2 ^ 32))) (Zlength addrs) w)).
  forward. forward. forward. forward. forward.
  forward_call (gv, copy, ctx, pl, sh, x, hs1, addrs, (set_entries (set_root_copy m1 (mk_sdt (i_address x) 0 len (cursor mod 2 ^ 32))) (Zlength addrs) w), osh, offset_val 24 res, offset_val 36 (p_root pl),
                Vint (Int.repr w), Tsh, v_root_table_addresses,
                sublist (Zlength addrs) MAX_ENTRIES (Zrepeat Vundef MAX_ENTRIES),
                osh, copies, sold, Tsh, v_copied_table_count, Vint (Int.repr 0)).
  all: try (solve [ repeat match goal with |- _ /\ _ => split end; auto ]).
  Intros vret. destruct vret as [[hs4 st4] m4]. cbn [fst snd] in *.
  match goal with H: run _ (tables_start _ _ _) hs4 = _ |- _ => rename H into R4 end.
  match goal with H: mem_ok x m4 |- _ => rename H into M4 end.
  match goal with H: m_root m4 = _ |- _ => rename H into RR4 end.
  match goal with H: m_root_copy m4 = _ |- _ => rename H into RC4 end.
  match goal with H: m_entries m4 = _ |- _ => rename H into RE4 end.
  match goal with H: Forall (slot_ok _) (m_slots m4) |- _ => rename H into FS4 end.
  match goal with H: status_ok st4 |- _ => rename H into SO4 end.
  match goal with H: st4 = S_OK -> _ |- _ => rename H into OK4 end.
  cbn [m_root m_root_copy m_entries set_root_copy set_entries] in RR4, RC4, RE4.
  forward. unfold vi.
  forward_if.
  { (* a table was not copied *)
    assert (ST4: (st4 =? S_OK) = false)
      by (apply Z.eqb_neq; intro Es; subst st4; match goal with H: Int.repr _ <> Int.repr _ |- _ => apply H; reflexivity end).
    rewrite ST4 in R4 |- *. cbv iota in R4 |- *.
    assert (P: pipeline x (hs1 ++ hs4) = Some (st4, None, m4)) by (apply pipeline_of; exact (run_glue x hs1 _ hs4 _ RT R4)).
    forward.
    Exists (hs1 ++ hs4) st4 (@None (Z * Z)) m4.
    unfold result_val. rewrite RC4, RE4, RR4. cbv iota.
    rewrite result_split, FA1, FA2, (sdt_val_root (p_root pl)) by auto. unfold entries_val.
    change (offset_val HEADER_BYTES (p_root pl)) with (offset_val 36 (p_root pl)).
    entailer!. }
  assert (ST4: st4 = S_OK) by (apply status_ok_repr; auto).
  subst st4. rewrite Z.eqb_refl in R4 |- *. cbv iota in R4 |- *.
  pose proof (OK4 eq_refl) as LS4. clear OK4.
  assert (DN: data_at Tsh tuint (Vint (Int.repr (Zlength addrs))) v_copied_table_count =
              data_at Tsh tuint (Vint (Int.repr (Zlength (m_slots m4)))) v_copied_table_count) by (rewrite LS4; reflexivity).
  rewrite DN.
  forward. forward.
  forward_if; [ exfalso; match goal with H: _ <> _ |- _ => apply H; rewrite ?LS4; reflexivity end | ].
  forward. forward. forward.
  pose proof M4 as (MH4 & MRt4 & MT4 & BH4 & BR4 & BT4).
  assert (DT4: data_at sh (tarray tuchar (table_capacity x)) (bytes_val (m_tables m4)) (p_tables pl) =
               data_at sh (tarray tuchar (Zlength (m_tables m4))) (bytes_val (m_tables m4)) (p_tables pl))
    by (rewrite MT4; reflexivity).
  rewrite DT4. unfold slots_val.
  assert (LSS: Zlength (m_slots m4) + Zlength (sublist (Zlength (m_slots m4)) MAX_ENTRIES sold) = MAX_ENTRIES)
    by (rewrite Zlength_sublist by (unfold MAX_ENTRIES in *; lia); lia).
  match goal with |- context [data_at Tsh _ ?v v_selected_madt] =>
    forward_call (gv, copies, osh, m_slots m4, sublist (Zlength (m_slots m4)) MAX_ENTRIES sold, p_tables pl, sh,
                  m_tables m4, v_selected_madt, Tsh, v) end.
  all: try (solve [ repeat match goal with |- _ /\ _ => split end; auto ]).
  forward.
  destruct (select_from (m_tables m4) (m_slots m4) 0 None) as [st5 | i] eqn:SF.
  { (* no MADT, two of them, or an invalid table *)
    pose proof (select_from_inl_range _ _ _ _ _ SF) as NR5.
    unfold vi. simpl status_of. cbv iota.
    forward_if.
    2: { dead_status. }
    rewrite <- DT4.
    assert (P: pipeline x (hs1 ++ hs4) = Some (st5, None, m4)).
    { apply pipeline_of. rewrite (run_glue x hs1 _ hs4 _ RT R4), tables_done_eq, SF. reflexivity. }
    forward.
    Exists (hs1 ++ hs4) st5 (@None (Z * Z)) m4.
    unfold result_val. rewrite RC4, RE4, RR4. cbv iota.
    rewrite result_split, FA1, FA2, (sdt_val_root (p_root pl)) by auto. unfold entries_val.
    change (offset_val HEADER_BYTES (p_root pl)) with (offset_val 36 (p_root pl)).
    entailer!. }
  pose proof (select_from_madt _ _ _ SF) as (IR & SMi).
  unfold vi. simpl status_of. cbv iota.
  forward_if; [ kill_branch | ].
  forward.
  assert_PROP (field_compatible (tarray t_sdt MAX_ENTRIES) [] copies) as FCc by entailer!.
  assert_PROP (field_compatible (tarray tuchar (Zlength (m_tables m4))) [] (p_tables pl)) as FCt by entailer!.
  set (L := map (sdt_val (p_tables pl)) (m_slots m4) ++ sublist (Zlength (m_slots m4)) MAX_ENTRIES sold).
  assert (LL: Zlength L = MAX_ENTRIES) by (unfold L; rewrite Zlength_app, Zlength_map; exact LSS).
  set (s := Znth i (m_slots m4)).
  assert (OKs: slot_ok (m_tables m4) s) by (apply (proj1 (Forall_Znth _ _) FS4); lia).
  destruct OKs as (Ua & L36s & O0 & OL & Ul & Un). unfold HEADER_BYTES in L36s.
  rewrite (split_slot osh L i copies) by (auto; unfold MAX_ENTRIES in *; lia).
  assert (ZL: Znth i L = sdt_val (p_tables pl) s)
    by (unfold L, s; rewrite Znth_app1 by (rewrite Zlength_map; lia); rewrite Znth_map by lia; reflexivity).
  rewrite ZL, (sdt_val_unfold (p_tables pl) s).
  rewrite (split2_bytes sh (m_tables m4) (Zlength (m_tables m4)) (s_offset s) (p_tables pl)) by (auto; lia).
  set (bs := sublist (s_offset s) (Zlength (m_tables m4)) (m_tables m4)).
  assert (Lbs: Zlength bs = Zlength (m_tables m4) - s_offset s) by (unfold bs; rewrite Zlength_sublist by lia; lia).
  assert (Fbs: Forall byte_ok bs) by (unfold bs; apply Forall_sublist; exact BT4).
  rewrite <- Lbs.
  Intros.
  assert (SM: signature_matches (s_length s) bs APIC = true) by exact SMi.
  forward_call (osh, offset_val (SDT_BYTES * i) copies, vl (s_address s), s_length s, vi (s_next s),
                offset_val (s_offset s) (p_tables pl), sh, bs, gv ___stringlit_acpi_1, APIC).
  all: try (solve [ repeat match goal with |- _ /\ _ => split end; try assumption; try (intros; unfold HEADER_BYTES in *; lia);
      try (unfold APIC; repeat constructor; lia) ]).
  rewrite SM. cbv iota.
  forward_if; [ kill_branch | ].
  rewrite Lbs. unfold bs.
  sep_apply (join2_bytes sh (m_tables m4) (Zlength (m_tables m4)) (s_offset s) (p_tables pl) eq_refl ltac:(lia) FCt).
  rewrite <- (sdt_val_unfold (p_tables pl) s), <- ZL.
  sep_apply (join_slot osh L i copies ltac:(unfold MAX_ENTRIES in *; lia) LL FCc).
  forward. forward. forward. forward.
  rewrite <- DT4.
  assert (P: pipeline x (hs1 ++ hs4) = Some (S_OK, Some (Zlength (m_slots m4), i), m4)).
  { apply pipeline_of. rewrite (run_glue x hs1 _ hs4 _ RT R4), tables_done_eq, SF, LS4. reflexivity. }
  forward.
  Exists (hs1 ++ hs4) S_OK (Some (Zlength (m_slots m4), i)) m4.
  unfold result_val. rewrite RC4, RE4, RR4. cbv iota.
  rewrite result_split, FA1, FA2, (sdt_val_root (p_root pl)) by auto. unfold entries_val.
  change (offset_val HEADER_BYTES (p_root pl)) with (offset_val 36 (p_root pl)).
  unfold L.
  entailer!.
Qed.
