(* Law consumer_obligations: the bodies of the harness's helpers any_u64 and records_ok. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosMadt.harness.consumer_obligations.code.
Require Import LeanosMadt.proof.Defs.
Require Import LeanosMadt.proof.MadtSpecs.
Require Import LeanosMadt.proof.LawProg LeanosMadt.proof.LawDefs LeanosMadt.proof.LawFacts LeanosMadt.proof.LawLib
  LeanosMadt.proof.LawWalk.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

(* records_ok returns 0: the walk is None. *)
Ltac walk_none W bs :=
  repeat match goal with
  | E: ?b = true |- _ => match type of b with bool => rewrite E in W; clear E end
  | E: ?b = false |- _ => match type of b with bool => rewrite E in W; clear E end
  end;
  assert (Rn: records bs = None) by (rewrite <- W; cmp_atoms; first [ reflexivity | exfalso; lia ]);
  unfold walk_b; rewrite Rn; repeat split; auto; unfold u64_ok; try rep_lia.

Lemma body_any_u64: semax_body nil [nondet_u32_spec] f_any_u64 any_u64_spec.
Proof.
  start_function.
  rewrite <- seq_assoc. forward_call. Intros hi. forward.
  rewrite <- seq_assoc. forward_call. Intros lo. forward.
  forward.
  Exists (Int64.unsigned (Int64.or (Int64.shl (Int64.repr hi) (Int64.repr 32)) (Int64.repr lo))).
  entailer!. split; [ apply Int64.unsigned_range_2 | unfold vl; rewrite Int64.repr_unsigned; reflexivity ].
Qed.

Lemma body_records_ok: semax_body nil nil f_records_ok records_ok_spec.
Proof.
  start_function.
  rename H into Hby, H0 into Hn.
  assert (Hn0: 0 <= Zlength bytes) by apply Zlength_nonneg.
  unfold MAX_LENGTH in Hn.
  forward.
  forward_for_simple_bound 4
    (EX k: Z, PROP ()
     LOCAL (temp _e e; temp _length (vl (Zlength bytes)); temp _count cp; temp _nmi np)
     SEP (data_at sh (tarray tuchar (Zlength bytes)) (bytes_val bytes) e;
          data_at Ews tulong (vl 0) cp;
          data_at Ews (tarray tulong 4) (Zrepeat (vl 0) k ++ Zrepeat Vundef (4 - k)) np))%assert.
  { entailer!. }
  { forward. entailer!. apply derives_refl'. f_equal. list_solve. }
  forward.
  forward_while
    (EX at_: Z, EX c: Z, EX m: list Z, EX f: nat,
     PROP (0 <= at_ <= Zlength bytes; walk_records f bytes at_ c m = records bytes;
           (Z.to_nat (Zlength bytes - at_) < f)%nat; 0 <= c <= at_; Zlength m = 4; Forall u64_ok m)
     LOCAL (temp _at (vl at_); temp _e e; temp _length (vl (Zlength bytes)); temp _count cp; temp _nmi np)
     SEP (data_at sh (tarray tuchar (Zlength bytes)) (bytes_val bytes) e; data_at Ews tulong (vl c) cp;
          data_at Ews (tarray tulong 4) (map vl m) np))%assert.
  - Exists 0 0 [0; 0; 0; 0] (S (Z.to_nat (Zlength bytes))). entailer!.
    repeat constructor; unfold u64_ok; rep_lia.
  - entailer!.
  - (* a record *)
    destruct f as [ | f ]; [ lia | ].
    assert (Rat: 0 <= at_ < Zlength bytes) by (rewrite Int64_ltu_repr in HRE by rep_lia; apply Z.ltb_lt in HRE; lia).
    rewrite walk_S in H0.
    replace (Zlength bytes <=? at_) with false in H0 by (symmetry; apply Z.leb_gt; lia).
    forward_if (PROP (2 <= Zlength bytes - at_)
                LOCAL (temp _at (vl at_); temp _e e; temp _length (vl (Zlength bytes)); temp _count cp; temp _nmi np)
                SEP (data_at sh (tarray tuchar (Zlength bytes)) (bytes_val bytes) e; data_at Ews tulong (vl c) cp;
                     data_at Ews (tarray tulong 4) (map vl m) np)).
    { u64c. forward. Exists c m. entailer!. walk_none H0 bytes. }
    { u64c. forward. entailer!. }
    Intros.
    assert (Rl: 0 <= Znth (at_ + 1) bytes <= Byte.max_unsigned) by (apply Forall_byte_Znth; auto; lia).
    forward.
    { entailer!. rewrite Znth_bytes_val by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    rewrite Znth_bytes_val by lia.
    forward.
    rewrite Int.unsigned_repr by rep_lia.
    set (len := Znth (at_ + 1) bytes) in *.
    forward_if (temp _t'1 (Vint (Int.repr (Z.b2z ((len <? 2) || (Zlength bytes - at_ <? len))%bool)))).
    { forward. entailer!. bool_fin. }
    { forward. entailer!. bool_fin. }
    forward_if (PROP (((len <? 2) || (Zlength bytes - at_ <? len))%bool = false)
                LOCAL (temp _n (vl len); temp _at (vl at_); temp _e e; temp _length (vl (Zlength bytes));
                       temp _count cp; temp _nmi np)
                SEP (data_at sh (tarray tuchar (Zlength bytes)) (bytes_val bytes) e; data_at Ews tulong (vl c) cp;
                     data_at Ews (tarray tulong 4) (map vl m) np)).
    { forward. Exists c m. entailer!. try b2z_hyp. walk_none H0 bytes. }
    { forward. entailer!; try b2z_hyp; auto. }
    Intros.
    assert (Lr: 2 <= len <= Zlength bytes - at_)
      by (match goal with E: ((len <? 2) || _)%bool = false |- _ =>
            apply orb_false_iff in E as [E1 E2]; apply Z.ltb_ge in E1, E2; lia end).
    assert (Rt: 0 <= Znth at_ bytes <= Byte.max_unsigned) by (apply Forall_byte_Znth; auto; lia).
    change (vl at_) with (Vlong (Int64.repr at_)).
    forward.
    { entailer!. rewrite Znth_bytes_val by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    rewrite Znth_bytes_val by lia.
    set (tp := Znth at_ bytes) in *.
    destruct (Z.eqb_spec tp 4) as [Et | Et].
    + (* an NMI record *)
      forward_if (PROP (len = 6)
                  LOCAL (temp _n (vl len); temp _at (Vlong (Int64.repr at_)); temp _e e;
                         temp _length (vl (Zlength bytes)); temp _count cp; temp _nmi np)
                  SEP (data_at sh (tarray tuchar (Zlength bytes)) (bytes_val bytes) e;
                       data_at Ews tulong (vl (c + 1)) cp;
                       data_at Ews (tarray tulong 4)
                         (map vl (if c <? 4 then upd_Znth c m (pack6 bytes at_) else m)) np)).
      * forward_if (PROP (len = 6)
                    LOCAL (temp _n (vl len); temp _at (Vlong (Int64.repr at_)); temp _e e;
                           temp _length (vl (Zlength bytes)); temp _count cp; temp _nmi np)
                    SEP (data_at sh (tarray tuchar (Zlength bytes)) (bytes_val bytes) e; data_at Ews tulong (vl c) cp;
                         data_at Ews (tarray tulong 4) (map vl m) np)).
        { forward. Exists c m. entailer!. u64c. walk_none H0 bytes. }
        { forward. entailer!. u64c. lia. }
        Intros.
        forward.
        forward_if (PROP ()
                    LOCAL (temp _n (vl len); temp _at (Vlong (Int64.repr at_)); temp _e e;
                           temp _length (vl (Zlength bytes)); temp _count cp; temp _nmi np)
                    SEP (data_at sh (tarray tuchar (Zlength bytes)) (bytes_val bytes) e; data_at Ews tulong (vl c) cp;
                         data_at Ews (tarray tulong 4)
                           (map vl (if c <? 4 then upd_Znth c m (pack6 bytes at_) else m)) np)).
        { assert (Lc: c < 4) by (u64c; lia).
          forward.
          forward_for_simple_bound 6
            (EX b: Z, PROP ()
             LOCAL (temp _packed (vl (pk bytes at_ (Z.to_nat b))); temp _n (vl len); temp _at (Vlong (Int64.repr at_));
                    temp _e e; temp _length (vl (Zlength bytes)); temp _count cp; temp _nmi np)
             SEP (data_at sh (tarray tuchar (Zlength bytes)) (bytes_val bytes) e; data_at Ews tulong (vl c) cp;
                  data_at Ews (tarray tulong 4) (map vl m) np))%assert.
          { entailer!. }
          { assert (Rj: 0 <= Znth (at_ + i) bytes <= Byte.max_unsigned) by (apply Forall_byte_Znth; auto; lia).
            forward.
            { entailer!. rewrite Znth_bytes_val by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
            rewrite Znth_bytes_val by lia.
            forward.
            { entailer!. apply shift_amount; lia. }
            rewrite Int.unsigned_repr by rep_lia. change (Int.signed (Int.repr 8)) with 8. rewrite mul64_repr'.
            rewrite or_shl_pk by (try lia; intros j Hj; pose proof (Forall_byte_Znth bytes (at_ + j) Hby ltac:(lia));
                                  unfold Byte.max_unsigned in *; simpl in *; lia).
            entailer!. }
          forward. change (vl c) with (Vlong (Int64.repr c)). forward.
          rewrite (proj2 (Z.ltb_lt c 4) Lc). rewrite upd_Znth_map_vl, pk_6.
          entailer!. }
        { assert (Lc: 4 <= c) by (u64c; lia). forward. rewrite (proj2 (Z.ltb_ge c 4) Lc). entailer!. }
        forward. forward. entailer!.
      * exfalso. u64c. contradiction.
      * Intros. forward.
        Exists (at_ + len, c + 1, if c <? 4 then upd_Znth c m (pack6 bytes at_) else m, f).
        entailer!. try subst len.
        split; [ lia | ]. split; [ rewrite <- H0; cmp_atoms; first [ reflexivity | exfalso; lia ] | ].
        split; [ lia | ]. split; [ lia | ].
        destruct (Z.ltb_spec c 4); [ | split; auto ].
        split; [ rewrite upd_Znth_Zlength by lia; lia | ].
        apply Forall_upd; auto. apply pack6_bound. intros j Hj.
        pose proof (Forall_byte_Znth bytes (at_ + j) Hby ltac:(lia)). unfold Byte.max_unsigned in *; simpl in *; lia.
    + (* another record *)
      forward_if (PROP ()
                  LOCAL (temp _n (vl len); temp _at (Vlong (Int64.repr at_)); temp _e e;
                         temp _length (vl (Zlength bytes)); temp _count cp; temp _nmi np)
                  SEP (data_at sh (tarray tuchar (Zlength bytes)) (bytes_val bytes) e; data_at Ews tulong (vl c) cp;
                       data_at Ews (tarray tulong 4) (map vl m) np)).
      * exfalso. u64c. contradiction.
      * forward. entailer!.
      * forward. Exists (at_ + len, c, m, f). entailer!. try subst len.
        split; [ lia | ]. split; [ rewrite <- H0; cmp_atoms; first [ reflexivity | exfalso; lia ] | ].
        split; lia.
  - (* past the last record *)
    assert (at_ = Zlength bytes) by (rewrite Int64_ltu_repr in HRE by rep_lia; apply Z.ltb_ge in HRE; lia).
    subst at_. destruct f as [ | f ]; [ lia | ].
    rewrite walk_S, Z.leb_refl in H0.
    forward. Exists c m. entailer!.
    unfold walk_b. rewrite <- H0. split; [ unfold u64_ok; rep_lia | auto ].
Qed.
