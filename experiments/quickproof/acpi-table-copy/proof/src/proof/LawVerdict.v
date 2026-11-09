(* Law table_copy_exact: the body of madt_verdict against the model's MADT selection (Defs.select_from). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosAcpi.harness.table_copy_exact.code.
Require Import LeanosAcpi.proof.Defs.
Require Import LeanosAcpi.proof.AcpiSpecs.
Require Import LeanosAcpi.proof.LawProg LeanosAcpi.proof.LawDefs LeanosAcpi.proof.LawFacts LeanosAcpi.proof.LawLib
  LeanosAcpi.proof.LawLib2.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[local] Existing Instance LawProg.LCS.

(* One copy record of the MADT selection, as madt_verdict checks it. *)
Lemma select_step: forall T sd rest index sel,
  HEADER_BYTES <= s_length sd -> 0 <= s_offset sd -> s_offset sd + s_length sd <= Zlength T ->
  select_from T (sd :: rest) index sel =
  if negb (little (sublist (s_offset sd + 4) (s_offset sd + 4 + 4) T) =? s_length sd) then inl S_SDT_ENVELOPE
  else if negb ((fold_left Z.add (sublist (s_offset sd) (s_offset sd + s_length sd) T) 0) mod 256 =? 0)
  then inl S_SDT_CHECKSUM
  else if sig_at T (s_offset sd) [65; 80; 73; 67] then
    match sel with Some _ => inl S_MADT_DUPLICATE | None => select_from T rest (index + 1) (Some index) end
  else select_from T rest (index + 1) sel.
Proof.
  intros T sd rest index sel L O F. unfold HEADER_BYTES in L. cbn [select_from].
  unfold validate, signature_matches.
  replace (s_length sd <? HEADER_BYTES) with false by (symmetry; apply Z.ltb_ge; unfold HEADER_BYTES; lia).
  replace (HEADER_BYTES <=? s_length sd) with true by (symmetry; apply Z.leb_le; unfold HEADER_BYTES; lia).
  rewrite !sublist_sublist by lia. rewrite checksum_sum.
  replace (4 + s_offset sd) with (s_offset sd + 4) by lia.
  replace (8 + s_offset sd) with (s_offset sd + 4 + 4) by lia.
  replace (0 + s_offset sd) with (s_offset sd) by lia.
  replace (s_length sd + s_offset sd) with (s_offset sd + s_length sd) by lia.
  unfold sig_at, APIC.
  change (Znth 0 [65; 80; 73; 67]) with 65. change (Znth 1 [65; 80; 73; 67]) with 80.
  change (Znth 2 [65; 80; 73; 67]) with 73. change (Znth 3 [65; 80; 73; 67]) with 67.
  assert (Z0: Znth 0 (sublist (s_offset sd) (Zlength T) T) = Znth (s_offset sd) T)
    by (rewrite Znth_sublist by lia; f_equal; lia).
  assert (Z1: Znth 1 (sublist (s_offset sd) (Zlength T) T) = Znth (s_offset sd + 1) T)
    by (rewrite Znth_sublist by lia; f_equal; lia).
  assert (Z2: Znth 2 (sublist (s_offset sd) (Zlength T) T) = Znth (s_offset sd + 2) T)
    by (rewrite Znth_sublist by lia; f_equal; lia).
  assert (Z3: Znth 3 (sublist (s_offset sd) (Zlength T) T) = Znth (s_offset sd + 3) T)
    by (rewrite Znth_sublist by lia; f_equal; lia).
  rewrite Z0, Z1, Z2, Z3. cbn [andb orb].
  destruct (little (sublist (s_offset sd + 4) (s_offset sd + 4 + 4) T) =? s_length sd);
  destruct (fold_left Z.add (sublist (s_offset sd) (s_offset sd + s_length sd) T) 0 mod 256 =? 0);
  destruct ((Znth (s_offset sd) T =? 65) && (Znth (s_offset sd + 1) T =? 80) && (Znth (s_offset sd + 2) T =? 73) &&
            (Znth (s_offset sd + 3) T =? 67));
  reflexivity.
Qed.

Lemma sublist_cons_Znth: forall {A} {d: Inhabitant A} (l: list A) t n, 0 <= t < n -> n = Zlength l ->
  sublist t n l = Znth t l :: sublist (t + 1) n l.
Proof. intros. subst n. rewrite (sublist_split t (t + 1)) by lia. rewrite sublist_len_1 by lia. reflexivity. Qed.

(* madt_verdict(m, &madt) on the copy records ss, the table arena T (of a 32-bit capacity). *)
Definition madt_verdict_spec' :=
  DECLARE _madt_verdict
  WITH q: val, te: val, T: list Z, N: Z, ss: list sdt, offs: list Z, lens: list Z, mp: val, mold: val
  PRE [ tptr t_law, tptr tuint ]
    PROP (Zlength T = N; N <= Int.max_unsigned; Forall byte_ok T; Zlength offs = MAX_ENTRIES;
          Zlength lens = MAX_ENTRIES; Zlength ss <= MAX_ENTRIES;
          forall t, 0 <= t < Zlength ss -> s_offset (Znth t ss) = Znth t offs /\ s_length (Znth t ss) = Znth t lens /\
            HEADER_BYTES <= Znth t lens <= MAX_SDT_BYTES /\ 0 <= Znth t offs /\ Znth t offs + Znth t lens <= N)
    PARAMS (q; mp)
    SEP (field_at Ews t_law (DOT _count) (vi (Zlength ss)) q; field_at Ews t_law (DOT _tables_expect) te q;
         field_at Ews t_law (DOT _offsets) (map vi offs) q; field_at Ews t_law (DOT _lengths) (map vi lens) q;
         data_at Ews (tarray tuchar N) (bytes_val T) te; data_at Tsh tuint mold mp)
  POST [ tuint ]
    EX mv: val,
    PROP (match select_from T ss 0 None with inr i => mv = vi i | inl _ => True end)
    RETURN (vi (stat (select_from T ss 0 None)))
    SEP (field_at Ews t_law (DOT _count) (vi (Zlength ss)) q; field_at Ews t_law (DOT _tables_expect) te q;
         field_at Ews t_law (DOT _offsets) (map vi offs) q; field_at Ews t_law (DOT _lengths) (map vi lens) q;
         data_at Ews (tarray tuchar N) (bytes_val T) te; data_at Tsh tuint mv mp).

Lemma body_madt_verdict : semax_body nil [little_spec; byte_sum_spec; signature_spec] f_madt_verdict madt_verdict_spec'.
Proof.
  start_function.
  rename H into LT, H0 into NB, H1 into FT, H2 into LO, H3 into LL, H4 into LS, H5 into SS.
  unfold MAX_ENTRIES in LO, LL, LS.
  assert_PROP (isptr te) as Pte by entailer!.
  forward. forward.
  forward_loop
    (EX t: Z, EX sel: option Z, EX mv: val,
     PROP (0 <= t <= Zlength ss; select_from T ss 0 None = select_from T (sublist t (Zlength ss) ss) t sel;
           match sel with Some i => mv = vi i | None => mv = mold end)
     LOCAL (temp _t (vi t); temp _found (vi (if sel then 1 else 0)); temp _m q; temp _madt mp)
     SEP (field_at Ews t_law (DOT _count) (vi (Zlength ss)) q; field_at Ews t_law (DOT _tables_expect) te q;
          field_at Ews t_law (DOT _offsets) (map vi offs) q; field_at Ews t_law (DOT _lengths) (map vi lens) q;
          data_at Ews (tarray tuchar N) (bytes_val T) te; data_at Tsh tuint mv mp))%assert
    continue:
    (EX t: Z, EX sel: option Z, EX mv: val,
     PROP (0 <= t < Zlength ss;
           select_from T ss 0 None = select_from T (sublist (t + 1) (Zlength ss) ss) (t + 1) sel;
           match sel with Some i => mv = vi i | None => mv = mold end)
     LOCAL (temp _t (vi t); temp _found (vi (if sel then 1 else 0)); temp _m q; temp _madt mp)
     SEP (field_at Ews t_law (DOT _count) (vi (Zlength ss)) q; field_at Ews t_law (DOT _tables_expect) te q;
          field_at Ews t_law (DOT _offsets) (map vi offs) q; field_at Ews t_law (DOT _lengths) (map vi lens) q;
          data_at Ews (tarray tuchar N) (bytes_val T) te; data_at Tsh tuint mv mp))%assert
    break:
    (EX sel: option Z, EX mv: val,
     PROP (select_from T ss 0 None = select_from T nil (Zlength ss) sel;
           match sel with Some i => mv = vi i | None => mv = mold end)
     LOCAL (temp _found (vi (if sel then 1 else 0)); temp _m q; temp _madt mp)
     SEP (field_at Ews t_law (DOT _count) (vi (Zlength ss)) q; field_at Ews t_law (DOT _tables_expect) te q;
          field_at Ews t_law (DOT _offsets) (map vi offs) q; field_at Ews t_law (DOT _lengths) (map vi lens) q;
          data_at Ews (tarray tuchar N) (bytes_val T) te; data_at Tsh tuint mv mp))%assert.
  - Exists 0 (@None Z) mold. entailer!. rewrite sublist_same by lia. reflexivity.
  - Intros t sel mv. unfold vi.
    forward.
    forward_if.
    2: { forward. Exists sel mv. entailer!. wordp.
         replace t with (Zlength ss) in * by lia. rewrite sublist_nil in *. auto. }
    wordp.
    destruct (SS t ltac:(lia)) as (E1 & E2 & E3 & E4 & E5). unfold HEADER_BYTES, MAX_SDT_BYTES in E3.
    rewrite <- E1, <- E2 in *.
    set (sd := Znth t ss) in *.
    assert (Ro: 0 <= s_offset sd <= Int.max_unsigned) by rep_lia.
    assert (Rl: 0 <= s_length sd <= Int.max_unsigned) by (unfold MAX_SDT_BYTES in *; rep_lia).
    forward. forward. rewrite <- ?E1. forward.
    forward. rewrite <- ?E2.
    rewrite (sublist_cons_Znth ss t (Zlength ss)) in H0 by lia. fold sd in H0.
    rewrite select_step in H0 by (unfold HEADER_BYTES; lia).
    forward_call (Ews, offset_val 4 (offset_val (s_offset sd) te), te, T, N, s_offset sd + 4, 4).
    assert (Lr: 0 <= little (sublist (s_offset sd + 4) (s_offset sd + 4 + 4) T) <= Int64.max_unsigned).
    { pose proof (little_u64 (sublist (s_offset sd + 4) (s_offset sd + 4 + 4) T)
        ltac:(apply Forall_sublist; auto) ltac:(rewrite Zlength_sublist by lia; lia)) as U. exact U. }
    forward_if.
    { forward. Exists mv. entailer!. wordp. rewrite H0.
      match goal with E: little _ <> s_length sd |- _ => rewrite (proj2 (Z.eqb_neq _ _) E) end.
      simpl. destruct sel; auto. }
    wordp.
    match goal with E: little _ = s_length sd |- _ => rewrite (proj2 (Z.eqb_eq _ _) E) in H0 end.
    cbn [negb] in H0. cbv iota in H0.
    forward_call (Ews, offset_val (s_offset sd) te, te, T, N, s_offset sd, s_length sd).
    set (sum := fold_left Z.add (sublist (s_offset sd) (s_offset sd + s_length sd) T) 0) in *.
    assert (Rs: 0 <= sum <= 255 * s_length sd).
    { pose proof (sum_bound (sublist (s_offset sd) (s_offset sd + s_length sd) T) ltac:(apply Forall_sublist; auto)).
      match goal with E: 0 <= fold_left _ _ _ <= _ |- _ => rewrite Zlength_sublist in E by lia end. unfold sum. lia. }
    clearbody sum.
    pose proof (Z.mod_pos_bound sum 256 ltac:(lia)) as Rm.
    forward_if.
    { forward. Exists mv. entailer!.
      try (match goal with E: context [Int.modu] |- _ => unfold Int.modu in E; rewrite !Int.unsigned_repr in E by rep_lia end).
      wordp. rewrite H0.
      match goal with E: sum mod 256 <> 0 |- _ => rewrite (proj2 (Z.eqb_neq _ _) E) end.
      simpl. destruct sel; auto. }
    try (match goal with E: context [Int.modu] |- _ => unfold Int.modu in E; rewrite !Int.unsigned_repr in E by rep_lia end).
    wordp.
    match goal with E: sum mod 256 = 0 |- _ => rewrite (proj2 (Z.eqb_eq _ _) E) in H0 end.
    cbn [negb] in H0. cbv iota in H0.
    forward_call (Ews, offset_val (s_offset sd) te, te, T, N, s_offset sd, 65, 80, 73, 67).
    { unfold byte_ok. repeat split; auto; try lia; rep_lia. }
    forward_if.
    + (* the APIC signature *)
      destruct (sig_at T (s_offset sd) [65; 80; 73; 67]) eqn:Sg; [ | exfalso; wordp; lia ].
      destruct sel as [i | ].
      * forward_if (PROP (False) LOCAL () SEP ()).
        { forward. Exists (vi i). entailer!. rewrite H0. repeat split; auto. }
        { exfalso. wordp. lia. }
      * forward_if (PROP () LOCAL (temp _t (Vint (Int.repr t)); temp _found (Vint (Int.repr 0)); temp _m q; temp _madt mp)
                   SEP (field_at Ews t_law (DOT _count) (vi (Zlength ss)) q; field_at Ews t_law (DOT _tables_expect) te q;
                        field_at Ews t_law (DOT _offsets) (map vi offs) q; field_at Ews t_law (DOT _lengths) (map vi lens) q;
                        data_at Ews (tarray tuchar N) (bytes_val T) te; data_at Tsh tuint mold mp)).
        { exfalso. wordp. lia. }
        { forward. entailer!. }
        forward. forward.
        Exists t (Some t) (vi t). entailer!.
    + (* another table *)
      forward.
      destruct (sig_at T (s_offset sd) [65; 80; 73; 67]) eqn:Sg; [ exfalso; wordp; lia | ].
      Exists t sel mv. entailer!.
  - Intros t sel mv. forward. Exists (t + 1) sel mv. entailer!.
  - Intros sel mv.
    forward_if (temp _t'4 (Vint (Int.repr (if sel then 0 else 32)))).
    { forward. destruct sel; [ entailer! | exfalso; wordp; lia ]. }
    { forward. destruct sel; [ exfalso; wordp; lia | entailer! ]. }
    forward. Exists mv. entailer!.
    rewrite H. destruct sel; simpl; split; auto.
Qed.
