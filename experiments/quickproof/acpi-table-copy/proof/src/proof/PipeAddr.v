(* The body of acpi_decode_root_addresses: the loop over the entries, each decoded by acpi_decode_root_entry into
   its cell of `addresses` (split out of the array for the call), then compared with the earlier ones; against
   `decode_from` one entry at a time.  ROOT_ENTRY_INDEX cannot fail here: the entry is below count and the width is
   4 or 8. *)
Require Import VST.floyd.proofauto.
Require Import LeanosAcpi.acpi.code.
Require Import LeanosAcpi.proof.Defs.
Require Import LeanosAcpi.proof.AcpiSpecs.
Require Import LeanosAcpi.proof.InternalSpecs.
Require Import LeanosAcpi.proof.PipeLemmas.
Require Import LeanosAcpi.proof.PipeFast.
#[local] Ltac simplify_remove_localdef_temp ::= fast_remove_localdef_temp.
#[local] Existing Instance AcpiSpecs.CS.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[local] Opaque decode_addresses decode_from range.

Lemma upd_cell: forall (pre: list Z) a (aold: list val), Zlength pre < MAX_ENTRIES -> Zlength aold = MAX_ENTRIES ->
  sublist 0 (Zlength pre) (map vl pre ++ sublist (Zlength pre) MAX_ENTRIES aold) = map vl pre /\
  sublist (Zlength pre + 1) MAX_ENTRIES (map vl pre ++ sublist (Zlength pre) MAX_ENTRIES aold) =
    sublist (Zlength pre + 1) MAX_ENTRIES aold /\
  sublist 0 (Zlength pre) (map vl (pre ++ [a]) ++ sublist (Zlength pre + 1) MAX_ENTRIES aold) = map vl pre /\
  Znth (Zlength pre) (map vl (pre ++ [a]) ++ sublist (Zlength pre + 1) MAX_ENTRIES aold) = vl a /\
  sublist (Zlength pre + 1) MAX_ENTRIES (map vl (pre ++ [a]) ++ sublist (Zlength pre + 1) MAX_ENTRIES aold) =
    sublist (Zlength pre + 1) MAX_ENTRIES aold /\
  Zlength (map vl (pre ++ [a]) ++ sublist (Zlength pre + 1) MAX_ENTRIES aold) = MAX_ENTRIES.
Proof.
  intros. unfold MAX_ENTRIES in *. pose proof (Zlength_nonneg pre).
  repeat split; list_solve.
Qed.

Lemma body_acpi_decode_root_addresses (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_acpi_decode_root_addresses decode_root_addresses_spec.
Proof.
  start_function.
  assert_PROP (field_compatible (tarray tulong MAX_ENTRIES) [] ap) as FCa by entailer!.
  assert (Wb: u32_ok w) by (destruct H0 as [-> | ->]; unfold u32_ok; rep_lia).
  assert (Cb: u32_ok count) by (unfold u32_ok, MAX_ENTRIES in *; rep_lia).
  forward.
  forward_loop (EX pre: list Z,
    PROP (0 <= Zlength pre <= count; Forall addr_ok pre;
          decode_addresses vec w count = decode_from vec w (sublist (Zlength pre) count (range count)) pre)
    LOCAL (temp _entry (Vint (Int.repr (Zlength pre))); temp _entries ep; temp _addresses ap)
    SEP (data_at esh t_entries (eb, (vi count, vi w)) ep;
         data_at bsh (tarray tuchar (Zlength vec)) (bytes_val vec) eb;
         data_at ash (tarray tulong MAX_ENTRIES) (map vl pre ++ sublist (Zlength pre) MAX_ENTRIES aold) ap))%assert
  continue: (EX pre: list Z,
    PROP (1 <= Zlength pre <= count; Forall addr_ok pre;
          decode_addresses vec w count = decode_from vec w (sublist (Zlength pre) count (range count)) pre)
    LOCAL (temp _entry (Vint (Int.repr (Zlength pre - 1))); temp _entries ep; temp _addresses ap)
    SEP (data_at esh t_entries (eb, (vi count, vi w)) ep;
         data_at bsh (tarray tuchar (Zlength vec)) (bytes_val vec) eb;
         data_at ash (tarray tulong MAX_ENTRIES) (map vl pre ++ sublist (Zlength pre) MAX_ENTRIES aold) ap))%assert
  break: (EX pre: list Z,
    PROP (decode_addresses vec w count = inr pre; Zlength pre = count)
    LOCAL (temp _entries ep; temp _addresses ap)
    SEP (data_at esh t_entries (eb, (vi count, vi w)) ep;
         data_at bsh (tarray tuchar (Zlength vec)) (bytes_val vec) eb;
         data_at ash (tarray tulong MAX_ENTRIES) (map vl pre ++ sublist (Zlength pre) MAX_ENTRIES aold) ap))%assert.
  { assert (D0: decode_addresses vec w count = decode_from vec w (sublist 0 count (range count)) [])
      by (apply decode_addresses_from; lia).
    Exists (@nil Z).
    replace (map vl [] ++ sublist (Zlength (@nil Z)) MAX_ENTRIES aold) with aold
      by (rewrite Zlength_nil; rewrite sublist_same by lia; reflexivity).
    entailer!. rewrite Zlength_nil. lia. }
  { Intros pre. forward. forward_if.
    { match goal with H: decode_addresses _ _ _ = _ |- _ => rename H into DA end.
      match goal with H: Forall addr_ok pre |- _ => rename H into Fpre end.
      assert (LP: Zlength pre < MAX_ENTRIES) by (unfold MAX_ENTRIES in *; lia).
      destruct (upd_cell pre 0 aold LP H4) as (U1 & U2 & _).
      rewrite (split_cell64 ash (map vl pre ++ sublist (Zlength pre) MAX_ENTRIES aold) (Zlength pre) ap)
        by first [ assumption | unfold MAX_ENTRIES in *; lia
                 | rewrite Zlength_app, Zlength_map, Zlength_sublist by (unfold MAX_ENTRIES in *; lia);
                   unfold MAX_ENTRIES in *; lia ].
      rewrite U1, U2. Intros.
      forward_call (esh, ep, eb, count, w, bsh, vec, Zlength pre, ash, offset_val (8 * (Zlength pre)) ap,
                    Znth (Zlength pre) (map vl pre ++ sublist (Zlength pre) MAX_ENTRIES aold)).
      { unfold u32_ok; rep_lia. }
      pose proof (decode_entry_ok vec count w (Zlength pre) ltac:(lia) H0) as DE. cbv zeta in DE.
      rewrite DE.
      set (a := entry_at vec w (Zlength pre)) in *.
      assert (LA: 0 <= a) by (apply entry_at_nonneg; auto).
      destruct ((a =? 0) || (MAX_U32 <? a)) eqn:BAD.
      { (* the address is 0 or wider than 32 bits *)
        replace (vi (status_of (@inl Z Z S_ROOT_ENTRY_ADDRESS))) with (Vint (Int.repr 25)) by reflexivity.
        forward_if; try (exfalso; first [ discriminate | contradiction ]).
        forward.
        Exists (map vl pre ++ [Znth (Zlength pre) (map vl pre ++ sublist (Zlength pre) MAX_ENTRIES aold)] ++
                sublist (Zlength pre + 1) MAX_ENTRIES aold).
        assert (D: decode_addresses vec w count = inl S_ROOT_ENTRY_ADDRESS).
        { rewrite DA, sublist_range_cons by lia. rewrite decode_from_cons. cbv zeta. fold a. rewrite BAD. reflexivity. }
        rewrite D.
        sep_apply (join_cell64 ash pre (Znth (Zlength pre) (map vl pre ++ sublist (Zlength pre) MAX_ENTRIES aold))
                     aold ap LP H4 FCa).
        entailer!; unfold MAX_ENTRIES in *; list_solve. }
      replace (vi (status_of (@inr Z Z a))) with (Vint (Int.repr 0)) by reflexivity.
      forward_if; try (exfalso; first [ discriminate | contradiction ]).
      sep_apply (join_cell64 ash pre (vl a) aold ap LP H4 FCa).
      replace (map vl pre ++ [vl a] ++ sublist (Zlength pre + 1) MAX_ENTRIES aold)
        with (map vl (pre ++ [a]) ++ sublist (Zlength pre + 1) MAX_ENTRIES aold)
        by (rewrite map_app, <- app_assoc; reflexivity).
      apply orb_false_iff in BAD as [B0 B1]. apply Z.eqb_neq in B0. apply Z.ltb_ge in B1.
      assert (Ua: u64_ok a) by (unfold u64_ok, MAX_U32 in *; rep_lia).
      assert (Fa: Forall (fun v => u64_ok v) pre)
        by (eapply Forall_impl; [ | exact Fpre ]; intros v [? ?]; unfold u64_ok, MAX_U32 in *; rep_lia).
      forward_for_simple_bound (Zlength pre) (EX j: Z,
        PROP (forall i, 0 <= i < j -> Znth i pre <> a)
        LOCAL (temp _entry (Vint (Int.repr (Zlength pre))); temp _entries ep; temp _addresses ap)
        SEP (data_at esh t_entries (eb, (vi count, vi w)) ep;
             data_at bsh (tarray tuchar (Zlength vec)) (bytes_val vec) eb;
             data_at ash (tarray tulong MAX_ENTRIES) (map vl (pre ++ [a]) ++ sublist (Zlength pre + 1) MAX_ENTRIES aold)
               ap))%assert.
      { entailer!; intros; lia. }
      { cbv beta. Intros. forward.
        { entailer!; rewrite Znth_pre by lia; unfold vl; simpl; auto. }
        rewrite Znth_pre by lia.
        forward.
        { entailer!; rewrite Znth_cur; unfold vl; simpl; auto. }
        rewrite Znth_cur.
        assert (Ui: u64_ok (Znth i pre)) by (apply (proj1 (Forall_Znth pre _) Fa); lia).
        forward_if.
        { (* a duplicate *)
          unfold vl in *. w64.
          assert (D: decode_addresses vec w count = inl S_ROOT_ENTRY_DUPLICATE).
          { rewrite DA, sublist_range_cons by lia. rewrite decode_from_cons. cbv zeta. fold a.
            rewrite (proj2 (Z.eqb_neq a 0) B0), (proj2 (Z.ltb_ge MAX_U32 a) B1).
            rewrite (existsb_true a pre i) by (auto; lia). reflexivity. }
          forward.
          match goal with |- context [data_at ash (tarray tulong MAX_ENTRIES) ?L ap] => Exists L end.
          rewrite D. entailer!; unfold MAX_ENTRIES in *; list_solve. }
        { unfold vl in *. w64.
          match goal with H: Znth i pre <> a |- _ => rename H into Ni end.
          match goal with H: forall i0, 0 <= i0 < i -> Znth i0 pre <> a |- _ => rename H into Hj end.
          assert (Hj': forall i0, 0 <= i0 < i + 1 -> Znth i0 pre <> a)
            by (intros i0 Hi0; destruct (Z.eq_dec i0 i); [ subst; auto | apply Hj; lia ]).
          forward. entailer!. } }

      Intros.
      assert (DA': decode_addresses vec w count =
                   decode_from vec w (sublist (Zlength pre + 1) count (range count)) (pre ++ [a])).
      { rewrite DA, sublist_range_cons by lia. rewrite decode_from_cons. cbv zeta. fold a.
        rewrite (proj2 (Z.eqb_neq a 0) B0), (proj2 (Z.ltb_ge MAX_U32 a) B1).
        rewrite existsb_false by auto. reflexivity. }
      Exists (pre ++ [a]).
      replace (Zlength (pre ++ [a])) with (Zlength pre + 1) by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
      replace (Zlength pre + 1 - 1) with (Zlength pre) by lia.
      entailer!.
      apply Forall_app; split; auto. constructor; [ unfold addr_ok; lia | constructor ]. }
    { match goal with H: decode_addresses _ _ _ = _ |- _ => rename H into DA end.
      assert (Lc: Zlength pre = count) by lia.
      rewrite Lc, sublist_nil in DA.
      forward. Exists pre. entailer!. } }
  { Intros pre. forward. Exists pre. entailer!. f_equal. f_equal. lia. }
  Intros pre. forward.
  match goal with |- context [data_at ash (tarray tulong MAX_ENTRIES) ?L ap] => Exists L end.
  match goal with H: decode_addresses _ _ _ = _ |- _ => rewrite H end.
  entailer!; try (unfold MAX_ENTRIES in *; list_solve); try (f_equal; lia).
Qed.
