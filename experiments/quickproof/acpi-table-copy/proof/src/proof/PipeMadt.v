(* The body of acpi_select_unique_madt: the loop over the first copied_count slots, each split out of the slot
   array (and its bytes out of the table arena) for acpi_validate_copied_sdt and acpi_signature_matches; against
   `select_from` one slot at a time. *)
Require Import VST.floyd.proofauto.
Require Import LeanosAcpi.acpi.code.
Require Import LeanosAcpi.proof.Defs.
Require Import LeanosAcpi.proof.AcpiSpecs.
Require Import LeanosAcpi.proof.InternalSpecs.
Require Import LeanosAcpi.proof.PipeLemmas.
Require Import LeanosAcpi.proof.PipeSlots.
Require Import LeanosAcpi.proof.PipeFast.
#[local] Ltac simplify_remove_localdef_temp ::= fast_remove_localdef_temp.
#[local] Existing Instance AcpiSpecs.CS.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[local] Opaque select_from validate signature_matches.

Lemma select_from_cons: forall T s ss i sel,
  select_from T (s :: ss) i sel =
  (if negb (validate (s_length s) (sublist (s_offset s) (Zlength T) T) None =? S_OK)
   then inl (validate (s_length s) (sublist (s_offset s) (Zlength T) T) None)
   else if signature_matches (s_length s) (sublist (s_offset s) (Zlength T) T) APIC then
     match sel with Some _ => inl S_MADT_DUPLICATE | None => select_from T ss (i + 1) (Some i) end
   else select_from T ss (i + 1) sel).
Proof. #[local] Transparent select_from. reflexivity. Qed.

Lemma select_from_nil: forall T i sel,
  select_from T [] i sel = match sel with None => inl S_MADT_MISSING | Some j => inr j end.
Proof. #[local] Transparent select_from. reflexivity. Qed.

Lemma sublist_cons_Znth: forall {A} {d: Inhabitant A} (l: list A) i n, 0 <= i < n -> n <= Zlength l ->
  sublist i n l = Znth i l :: sublist (i + 1) n l.
Proof.
  intros. rewrite (sublist_split i (i + 1) n) by lia. rewrite sublist_len_1 by lia. reflexivity.
Qed.

Lemma Znth_slots: forall tp (ss: list sdt) (rest: list sdt_rep) i, 0 <= i < Zlength ss ->
  Znth i (map (sdt_val tp) ss ++ rest) = sdt_val tp (Znth i ss).
Proof.
  intros. rewrite Znth_app1 by (rewrite Zlength_map; lia). rewrite Znth_map by lia. reflexivity.
Qed.

Lemma validate_range: forall len bs sig, validate len bs sig = S_OK \/ validate len bs sig = S_SDT_ENVELOPE \/
  validate len bs sig = S_SDT_CHECKSUM.
Proof.
  #[local] Transparent validate. intros. unfold validate.
  destruct (_ || _); [ auto | ]. destruct (negb _); auto.
Qed.

Ltac rejoin_slot :=
  match goal with
  | Lbs: Zlength ?bs = Zlength ?T - s_offset ?s, ZL: Znth ?i ?L = sdt_val ?tp ?s,
    FCt: field_compatible (tarray tuchar (Zlength ?T)) [] ?tp,
    FCc: field_compatible (tarray t_sdt MAX_ENTRIES) [] ?copies |- _ =>
      rewrite Lbs; unfold bs;
      sep_apply (join2_bytes _ T (Zlength T) (s_offset s) tp eq_refl ltac:(lia) FCt);
      fold (sdt_val tp s); rewrite <- ZL;
      sep_apply (join_slot _ L i copies ltac:(unfold MAX_ENTRIES in *; lia) ltac:(auto) FCc)
  end.

Lemma validate_zero: forall len bs sig, Int.repr (validate len bs sig) = Int.repr 0 -> validate len bs sig = S_OK.
Proof.
  intros. destruct (validate_range len bs sig) as [E | [E | E]]; auto; rewrite E in *;
    apply (f_equal Int.unsigned) in H; unfold S_SDT_ENVELOPE, S_SDT_CHECKSUM in H;
    rewrite !Int.unsigned_repr in H by rep_lia; discriminate.
Qed.

Definition sel_ptr (copies: val) (sel: option Z) : val :=
  match sel with Some j => offset_val (SDT_BYTES * j) copies | None => nullval end.

Lemma body_acpi_select_unique_madt (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_acpi_select_unique_madt select_unique_madt_spec.
Proof.
  start_function.
  assert_PROP (field_compatible (tarray t_sdt MAX_ENTRIES) [] copies) as FCc by entailer!.
  assert_PROP (field_compatible (tarray tuchar (Zlength T)) [] tp) as FCt by entailer!.
  assert_PROP (isptr copies) as Pc by entailer!.
  set (L := map (sdt_val tp) ss ++ rest).
  assert (LL: Zlength L = MAX_ENTRIES) by (unfold L; rewrite Zlength_app, Zlength_map; lia).
  pose proof (Zlength_nonneg rest).
  assert (Iss: Zlength ss <= 256) by (unfold MAX_ENTRIES in *; lia).
  unfold vi.
  forward.
  forward_for_simple_bound (Zlength ss) (EX i: Z, EX sel: option Z,
    PROP (select_from T ss 0 None = select_from T (sublist i (Zlength ss) ss) i sel;
          match sel with Some j => 0 <= j < i | None => True end)
    LOCAL (temp _selected (sel_ptr copies sel); temp _copies copies; temp _copied_count (Vint (Int.repr (Zlength ss)));
           temp _madt mp; gvars gv)
    SEP (data_at osh (tarray t_sdt MAX_ENTRIES) L copies;
         data_at sh (tarray tuchar (Zlength T)) (bytes_val T) tp; literal APIC (gv ___stringlit_acpi_1);
         data_at msh (tptr t_sdt) mold mp))%assert.
  { Exists (@None Z). entailer!. rewrite sublist_same by lia. reflexivity. }
  { (* slot i *)
    cbv beta. Intros sel.
    match goal with H: select_from T ss 0 None = _ |- _ => rename H into SF end.
    forward.
    rewrite add_ptr_sdt_uint, Int.unsigned_repr by (auto; rep_lia).
    set (s := Znth i ss).
    assert (OK: slot_ok T s) by (apply (proj1 (Forall_Znth ss _) H1); lia).
    destruct OK as (Ua & L36 & O0 & OL & Ul & Un). unfold HEADER_BYTES in L36.
    rewrite (split_slot osh L i copies) by (auto; lia).
    assert (ZL: Znth i L = sdt_val tp s) by (unfold L, s; apply Znth_slots; lia). rewrite ZL.
    unfold sdt_val at 1.
    rewrite (split2_bytes sh T (Zlength T) (s_offset s) tp) by (auto; lia).
    set (bs := sublist (s_offset s) (Zlength T) T).
    assert (Lbs: Zlength bs = Zlength T - s_offset s) by (unfold bs; rewrite Zlength_sublist by lia; lia).
    assert (Fbs: Forall byte_ok bs) by (unfold bs; apply Forall_sublist; auto).
    rewrite <- Lbs.
    Intros.
    forward_call (osh, offset_val (SDT_BYTES * i) copies, vl (s_address s), s_length s, vi (s_next s),
                  offset_val (s_offset s) tp, sh, bs, nullval, @None (list Z)).
    { cancel. }
    assert (SUBL: sublist i (Zlength ss) ss = s :: sublist (i + 1) (Zlength ss) ss)
      by (unfold s; apply sublist_cons_Znth; lia).
    rewrite SUBL, select_from_cons in SF. fold bs in SF.
    pose proof (validate_range (s_length s) bs None) as VR.
    forward_if.
    { (* the copy is not a valid SDT *)
      assert (VN: validate (s_length s) bs None <> S_OK)
        by (intro E; rewrite E in *; match goal with H: Int.repr _ <> Int.repr _ |- _ => apply H end; reflexivity).
      rewrite (proj2 (negb_true_iff _) (proj2 (Z.eqb_neq _ _) VN)) in SF.
      rewrite Lbs. unfold bs.
      sep_apply (join2_bytes sh T (Zlength T) (s_offset s) tp eq_refl ltac:(lia) FCt).
      fold (sdt_val tp s). rewrite <- ZL.
      sep_apply (join_slot osh L i copies ltac:(unfold MAX_ENTRIES in *; lia) LL FCc).
      forward.
      rewrite SF. simpl status_of. unfold vi. entailer!. }
    assert (VO: validate (s_length s) bs None = S_OK)
      by (apply validate_zero; match goal with H: Int.repr _ = Int.repr _ |- _ => exact H end).
    assert (SF2: select_from T ss 0 None =
                 if signature_matches (s_length s) bs APIC
                 then match sel with
                      | Some _ => inl S_MADT_DUPLICATE
                      | None => select_from T (sublist (i + 1) (Zlength ss) ss) (i + 1) (Some i)
                      end
                 else select_from T (sublist (i + 1) (Zlength ss) ss) (i + 1) sel)
      by (rewrite SF, VO; reflexivity).
    clear SF.
    forward_call (osh, offset_val (SDT_BYTES * i) copies, vl (s_address s), s_length s, vi (s_next s),
                  offset_val (s_offset s) tp, sh, bs, gv ___stringlit_acpi_1, APIC).
    { unfold APIC; repeat constructor; lia. }
    rewrite Lbs. unfold bs.
    sep_apply (join2_bytes sh T (Zlength T) (s_offset s) tp eq_refl ltac:(lia) FCt).
    fold (sdt_val tp s). rewrite <- ZL.
    sep_apply (join_slot osh L i copies ltac:(unfold MAX_ENTRIES in *; lia) LL FCc).
    fold bs.
    assert (Vj: forall j, 0 <= j < MAX_ENTRIES ->
              data_at osh (tarray t_sdt MAX_ENTRIES) L copies |-- valid_pointer (offset_val (SDT_BYTES * j) copies))
      by (intros; apply slot_valid; auto).
    destruct (signature_matches (s_length s) bs APIC) eqn:SM.
    { (* an APIC table *)
      forward_if; try (exfalso; first [ discriminate | contradiction ]).
      destruct sel as [j | ]; unfold sel_ptr.
      { (* a second one *)
        forward_if.
        { apply denote_tc_test_eq_split; [ | apply valid_pointer_null ].
          sep_apply (Vj j ltac:(unfold MAX_ENTRIES in *; lia)). apply extend_valid_pointer. }
        { forward. rewrite SF2. simpl status_of. entailer!. }
        { exfalso. destruct copies; try contradiction. discriminate. } }
      forward_if.
      { discriminate. }
      forward. Exists (Some i). entailer!; try (rewrite SF2; reflexivity). }
    forward_if; try (exfalso; first [ discriminate | contradiction ]).
    forward. Exists sel. entailer!; destruct sel; auto; lia. }
  Intros sel.
  match goal with H: select_from T ss 0 None = _ |- _ => rename H into SF end.
  rewrite sublist_nil, select_from_nil in SF.
  destruct sel as [j | ]; unfold sel_ptr.
  { forward_if.
    { apply denote_tc_test_eq_split; [ | apply valid_pointer_null ].
      sep_apply (slot_valid osh L j copies SH ltac:(unfold MAX_ENTRIES in *; lia)). apply extend_valid_pointer. }
    { exfalso. destruct copies; try contradiction. discriminate. }
    forward. forward. rewrite SF. simpl status_of. entailer!. }
  forward_if.
  { forward. rewrite SF. simpl status_of. entailer!. }
  { exfalso; first [ discriminate | contradiction | auto ]. }
Qed.
