(* The bodies of acpi_decode_root_entries (the kind, the length, the payload's width and count) and
   acpi_decode_root_entry (the index and width checks, the little-endian entry, the address checks). *)
Require Import VST.floyd.proofauto.
Require Import LeanosAcpi.acpi.code.
Require Import LeanosAcpi.proof.Defs.
Require Import LeanosAcpi.proof.AcpiSpecs.
Require Import LeanosAcpi.proof.InternalSpecs.
Require Import LeanosAcpi.proof.PipeLemmas.
#[local] Existing Instance AcpiSpecs.CS.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Lemma decode_entries_kind: forall kind len, kind <> 1 -> kind <> 2 -> decode_entries kind len = inl S_ROOT_KIND.
Proof.
  intros. unfold decode_entries. rewrite (proj2 (Z.eqb_neq kind 1)), (proj2 (Z.eqb_neq kind 2)) by auto.
  reflexivity.
Qed.

Lemma decode_entries_w: forall kind len, kind = 1 \/ kind = 2 ->
  decode_entries kind len =
  (let w := if kind =? 1 then 4 else 8 in
   if len <? HEADER_BYTES then inl S_ROOT_HEADER
   else if negb ((len - HEADER_BYTES) mod w =? 0) then inl S_ROOT_WIDTH
   else if MAX_ENTRIES <? (len - HEADER_BYTES) / w then inl S_ROOT_ENTRIES
   else inr ((len - HEADER_BYTES) / w, w)).
Proof. intros. destruct H; subst; reflexivity. Qed.

Lemma body_acpi_decode_root_entries (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_acpi_decode_root_entries decode_root_entries_spec.
Proof.
  start_function.
  unfold u32_ok, u64_ok in *.
  forward_if (PROP (kind = 1 \/ kind = 2)
              LOCAL (temp _width (vi (if kind =? 1 then 4 else 8)); temp _root rp; temp _selected_kind (vl kind);
                     temp _entries ep)
              SEP (data_at rsh t_sdt (ra, (base, (vi len, rn))) rp; data_at esh t_entries eold ep)).
  { forward. entailer!. uconst. w64. subst. auto. }
  { forward_if.
    { forward. entailer!. uconst. w64. subst. auto. }
    { forward. uconst. w64. rewrite (decode_entries_kind kind len H2 H3). entailer!. } }
  Intros. destruct (decode_entries_w' kind len H2) as (w & W & EW & DK). rewrite EW. clear EW.
  unfold HEADER_BYTES, MAX_ENTRIES in DK.
  forward. forward_if.
  { forward. rewrite DK, (proj2 (Z.ltb_lt len 36)) by lia. entailer!. }
  rewrite (proj2 (Z.ltb_ge len 36)) in DK by lia.
  forward. forward.
  rewrite sub_repr.
  pose proof (Z.mod_pos_bound (len - 36) w ltac:(lia)) as MB.
  assert (DB: 0 <= (len - 36) / w <= len - 36) by (split; [ apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia ]).
  assert (Wnz: Int.repr w <> Int.zero) by (apply repr_nonzero; rep_lia).
  forward_if.
  { rewrite modu_repr in H4 by (unfold u32_ok; lia). w64.
    forward. rewrite DK, (proj2 (Z.eqb_neq _ _) H4). entailer!. }
  rewrite modu_repr in H4 by (unfold u32_ok; lia). w64.
  forward.
  rewrite divu_repr by (unfold u32_ok; try split; try lia; apply Z.div_pos; lia).
  forward_if.
  { fold (Z.div (len - 36) w) in H5. rewrite Int.unsigned_repr in H5 by rep_lia.
    forward. rewrite DK, H4, (proj2 (Z.ltb_lt _ _) H5). entailer!. }
  fold (Z.div (len - 36) w) in H5. rewrite Int.unsigned_repr in H5 by rep_lia.
  forward. forward. forward. forward. forward.
  rewrite DK, H4, Z.eqb_refl, (proj2 (Z.ltb_ge _ _)) by lia. simpl negb. cbv iota.
  entailer!.
Qed.

Lemma body_acpi_decode_root_entry (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_acpi_decode_root_entry decode_root_entry_spec.
Proof.
  start_function.
  unfold u32_ok in *. unfold vi, vl.
  forward.
  forward_if (temp _t'1 (Vint (bint ((count <=? index) || negb ((w =? 4) || (w =? 8)))))).
  { forward. entailer!. rewrite (proj2 (Z.leb_le count index)) by lia. reflexivity. }
  { forward.
    forward_if.
    { forward. forward. forward. entailer!.
      rewrite (proj2 (Z.leb_gt count index)), (proj2 (Z.eqb_neq w 4)) by lia. rewrite zeq_eqb.
      rewrite bool2val_bint. reflexivity. }
    { forward. entailer!. rewrite (proj2 (Z.leb_gt count index)) by lia. reflexivity. } }
  forward_if.
  { forward. bfix. unfold decode_entry. match goal with H: (_ || _) = true |- _ => rewrite H end. entailer!. }
  bfix. match goal with H: (_ || _) = false |- _ => apply orb_false_iff in H as [Ci Cw] end. apply Z.leb_gt in Ci. apply negb_false_iff in Cw.
  assert (W: w = 4 \/ w = 8) by (apply orb_true_iff in Cw as [E|E]; apply Z.eqb_eq in E; auto).
  specialize (H2 Ci W).
  forward. forward. forward. forward.
  assert_PROP (field_compatible (tarray tuchar (Zlength vec)) [] eb) as FC by entailer!.
  rewrite (split3_bytes bsh vec (Zlength vec) (index * w) (index * w + w)) by (auto; nia).
  replace (index * w + w - index * w) with w by lia.
  Intros.
  rewrite mul_uint, add_ptr_uchar_uint, Int.unsigned_repr by (auto; nia).
  set (mid := sublist (index * w) (index * w + w) vec).
  assert (Lmid: Zlength mid = w) by (subst mid; rewrite Zlength_sublist; nia).
  assert (Bmid: Forall byte_ok mid) by (apply Forall_sublist; auto).
  change (Int.signed (Int.repr 0)) with 0.
  forward.
  forward_loop (EX k: Z,
    PROP (0 <= k <= w)
    LOCAL (temp _physical_address (Vlong (Int64.repr (little (sublist 0 k mid)))); temp _byte (Vint (Int.repr k));
           temp _encoded (offset_val (index * w) eb); temp _entries ep; temp _address ap)
    SEP (data_at esh t_entries (eb, (Vint (Int.repr count), Vint (Int.repr w))) ep;
         data_at bsh (tarray tuchar (index * w)) (bytes_val (sublist 0 (index * w) vec)) eb;
         data_at bsh (tarray tuchar w) (bytes_val mid) (offset_val (index * w) eb);
         data_at bsh (tarray tuchar (Zlength vec - (index * w + w)))
           (bytes_val (sublist (index * w + w) (Zlength vec) vec)) (offset_val (index * w + w) eb);
         data_at ash tulong aold ap))%assert
  continue: (EX k: Z,
    PROP (0 <= k < w)
    LOCAL (temp _physical_address (Vlong (Int64.repr (little (sublist 0 (k + 1) mid))));
           temp _byte (Vint (Int.repr k));
           temp _encoded (offset_val (index * w) eb); temp _entries ep; temp _address ap)
    SEP (data_at esh t_entries (eb, (Vint (Int.repr count), Vint (Int.repr w))) ep;
         data_at bsh (tarray tuchar (index * w)) (bytes_val (sublist 0 (index * w) vec)) eb;
         data_at bsh (tarray tuchar w) (bytes_val mid) (offset_val (index * w) eb);
         data_at bsh (tarray tuchar (Zlength vec - (index * w + w)))
           (bytes_val (sublist (index * w + w) (Zlength vec) vec)) (offset_val (index * w + w) eb);
         data_at ash tulong aold ap))%assert
  break: (
    PROP ()
    LOCAL (temp _physical_address (Vlong (Int64.repr (little mid))); temp _entries ep; temp _address ap)
    SEP (data_at esh t_entries (eb, (Vint (Int.repr count), Vint (Int.repr w))) ep;
         data_at bsh (tarray tuchar (index * w)) (bytes_val (sublist 0 (index * w) vec)) eb;
         data_at bsh (tarray tuchar w) (bytes_val mid) (offset_val (index * w) eb);
         data_at bsh (tarray tuchar (Zlength vec - (index * w + w)))
           (bytes_val (sublist (index * w + w) (Zlength vec) vec)) (offset_val (index * w + w) eb);
         data_at ash tulong aold ap))%assert.
  { Exists 0. entailer!. }
  { Intros k. forward. forward_if.
    { forward.
      { entailer!. rewrite Znth_bytes_val by lia. apply tc_byte, byte_at; auto; lia. }
      rewrite Znth_bytes_val by lia.
      forward.
      { entailer!. change (Int.unsigned Int64.iwordsize') with 64. lia. }
      rewrite compose64_0 by (auto; lia).
      Exists k. entailer!. }
    { forward. entailer!. assert (k = w) by lia. subst k. rewrite sublist_same by lia. reflexivity. } }
  { Intros k. forward. Exists (k + 1). entailer!. }
  assert (J: data_at bsh (tarray tuchar (index * w)) (bytes_val (sublist 0 (index * w) vec)) eb *
             data_at bsh (tarray tuchar w) (bytes_val mid) (offset_val (index * w) eb) *
             data_at bsh (tarray tuchar (Zlength vec - (index * w + w)))
               (bytes_val (sublist (index * w + w) (Zlength vec) vec)) (offset_val (index * w + w) eb)
             |-- data_at bsh (tarray tuchar (Zlength vec)) (bytes_val vec) eb).
  { rewrite (split3_bytes bsh vec (Zlength vec) (index * w) (index * w + w)) by (auto; nia).
    replace (index * w + w - index * w) with w by lia. cancel. }
  sep_apply J. clear J.
  pose proof (decode_entry_ok vec count w index Ci W) as DE. cbv zeta in DE.
  change (entry_at vec w index) with (little mid) in DE.
  assert (U: u64_ok (little mid)) by (apply little_u64; auto; lia).
  unfold u64_ok in U.
  forward_if (temp _t'2 (Vint (bint ((little mid =? 0) || (MAX_U32 <? little mid))))).
  { change Int64.zero with (Int64.repr 0) in H6. apply repr64_inj in H6; [ | unfold u64_ok; lia | unfold u64_ok; rep_lia ].
    forward. entailer!. rewrite H6. reflexivity. }
  { apply repr64_neq in H6.
    forward. entailer!. unfold Int64.cmpu. rewrite ltu64_repr by (unfold u64_ok; rep_lia).
    rewrite (proj2 (Z.eqb_neq _ _) H6), bool2val_bint. reflexivity. }
  forward_if.
  { forward. bfix. rewrite DE, H6. entailer!. }
  bfix. forward. forward. rewrite DE, H6. entailer!.
Qed.
