(* The bodies of acpi_signature_matches (four guarded byte comparisons) and acpi_validate_copied_sdt. *)
Require Import VST.floyd.proofauto.
Require Import LeanosAcpi.acpi.code.
Require Import LeanosAcpi.proof.Defs.
Require Import LeanosAcpi.proof.AcpiSpecs.
Require Import LeanosAcpi.proof.InternalSpecs.
Require Import LeanosAcpi.proof.PipeLemmas.
#[local] Existing Instance AcpiSpecs.CS.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* One more character of the signature: in the branch where the first k agreed, read byte k and character k. *)
Lemma body_acpi_signature_matches (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_acpi_signature_matches signature_matches_spec.
Proof.
  start_function.
  assert (L4: length sig = 4%nat) by (rewrite Zlength_correct in H2; lia).
  destruct sig as [ | c0 [ | c1 [ | c2 [ | c3 [ | ? ?]]]]]; try discriminate L4. clear L4.
  inversion H3 as [ | ? ? C0 H3a]; inversion H3a as [ | ? ? C1 H3b]; inversion H3b as [ | ? ? C2 H3c];
    inversion H3c as [ | ? ? C3 _]; subst.
  unfold literal, lit_val. simpl map.
  unfold u32_ok in H.
  forward.
  forward_if (temp _t'1 (Vint (bint ((36 <=? len) && (Znth 0 bs =? c0))))).
  { assert (L: 4 <= Zlength bs) by (apply H0; unfold HEADER_BYTES; lia).
    forward. forward.
    { entailer!. rewrite Znth_bytes_val by lia. apply tc_byte, byte_at; auto; lia. }
    rewrite Znth_bytes_val by lia.
    forward.
    { entailer!; rep_lia. }
    rewrite Znth5_0.
    forward.
    entailer!. rewrite eq_byte_char by (auto; apply byte_at; auto; lia).
    rewrite (proj2 (Z.leb_le 36 len)) by lia. reflexivity. }
  { forward. entailer!. rewrite (proj2 (Z.leb_gt 36 len)) by lia. reflexivity. }
  forward_if (temp _t'2 (Vint (bint ((36 <=? len) && (Znth 0 bs =? c0) && (Znth 1 bs =? c1))))).
  { bfix. pose proof H4 as L36. apply andb_prop in L36 as [L36 _]. apply Z.leb_le in L36.
    assert (L: 4 <= Zlength bs) by (apply H0; unfold HEADER_BYTES; lia).
    forward. forward.
    { entailer!. rewrite Znth_bytes_val by lia. apply tc_byte, byte_at; auto; lia. }
    rewrite Znth_bytes_val by lia.
    forward.
    { entailer!; rep_lia. }
    rewrite Znth5_1.
    forward.
    entailer!. rewrite eq_byte_char by (auto; apply byte_at; auto; lia). rewrite H4. reflexivity. }
  { forward. entailer!. bfix. rewrite H4. reflexivity. }
  forward_if (temp _t'3 (Vint (bint ((36 <=? len) && (Znth 0 bs =? c0) && (Znth 1 bs =? c1) && (Znth 2 bs =? c2))))).
  { bfix. pose proof H4 as L36. apply andb_prop in L36 as [L36 _]. apply andb_prop in L36 as [L36 _].
    apply Z.leb_le in L36.
    assert (L: 4 <= Zlength bs) by (apply H0; unfold HEADER_BYTES; lia).
    forward. forward.
    { entailer!. rewrite Znth_bytes_val by lia. apply tc_byte, byte_at; auto; lia. }
    rewrite Znth_bytes_val by lia.
    forward.
    { entailer!; rep_lia. }
    rewrite Znth5_2.
    forward.
    entailer!. rewrite eq_byte_char by (auto; apply byte_at; auto; lia). rewrite H4. reflexivity. }
  { forward. entailer!. bfix. rewrite H4. reflexivity. }
  forward_if (temp _t'4 (Vint (bint ((36 <=? len) && (Znth 0 bs =? c0) && (Znth 1 bs =? c1) && (Znth 2 bs =? c2)
                                     && (Znth 3 bs =? c3))))).
  { bfix. pose proof H4 as L36. apply andb_prop in L36 as [L36 _]. apply andb_prop in L36 as [L36 _].
    apply andb_prop in L36 as [L36 _]. apply Z.leb_le in L36.
    assert (L: 4 <= Zlength bs) by (apply H0; unfold HEADER_BYTES; lia).
    forward. forward.
    { entailer!. rewrite Znth_bytes_val by lia. apply tc_byte, byte_at; auto; lia. }
    rewrite Znth_bytes_val by lia.
    forward.
    { entailer!; rep_lia. }
    rewrite Znth5_3.
    forward.
    entailer!. rewrite eq_byte_char by (auto; apply byte_at; auto; lia). rewrite H4. reflexivity. }
  { forward. entailer!. bfix. rewrite H4. reflexivity. }
  forward.
Qed.

(* acpi_validate_copied_sdt: the envelope (a non-NULL table, its length, its declared length, its signature), then
   the checksum loop. *)
Definition envelope (len: Z) (bs: list Z) (sig: option (list Z)) : bool :=
  (len <? HEADER_BYTES) || negb (little (sublist 4 8 bs) =? len) ||
  (match sig with Some s => negb (signature_matches len bs s) | None => false end).

Lemma validate_envelope: forall len bs sig, validate len bs sig =
  if envelope len bs sig then S_SDT_ENVELOPE else if negb (checksum (sublist 0 len bs) =? 0) then S_SDT_CHECKSUM else S_OK.
Proof. reflexivity. Qed.

Lemma envelope_false_len: forall len bs sig, envelope len bs sig = false -> HEADER_BYTES <= len.
Proof. unfold envelope. intros. destruct (Z.ltb_spec len HEADER_BYTES); [ discriminate | lia ]. Qed.

Lemma body_acpi_validate_copied_sdt (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_acpi_validate_copied_sdt validate_spec.
Proof.
  start_function.
  unfold u32_ok in H.
  assert_PROP (isptr bp) as Pbp by entailer!.
  assert_PROP (match sig with Some _ => isptr sp | None => True end) as Psp
    by (destruct sig; unfold literal; entailer!).
  forward.
  forward_if (temp _t'1 (Vint (bint (len <? HEADER_BYTES)))).
  { subst bp. contradiction. }
  { forward. forward. entailer!. rewrite ?zlt_ltb, ?bool2val_bint. reflexivity. }
  forward_if (temp _t'2 (Vint (bint ((len <? HEADER_BYTES) || negb (little (sublist 4 8 bs) =? len))))).
  { forward. entailer!. bfix. rewrite H4. reflexivity. }
  { bfix. apply Z.ltb_ge in H4. unfold HEADER_BYTES in *. specialize (H1 ltac:(lia)).
    assert (B: forall i, 0 <= i < Zlength bs -> 0 <= Znth i bs <= 255) by (intros; apply byte_at; auto).
    do 4 (forward; forward; [ entailer!; rewrite Znth_bytes_val by lia; apply tc_byte, B; lia | ];
          rewrite Znth_bytes_val by lia).
    forward. forward.
    entailer!.
    rewrite length32, eq32_repr by (auto; try apply length32_u32; auto; unfold u32_ok; lia).
    rewrite (proj2 (Z.ltb_ge len 36)) by lia. rewrite bool2val_bint. reflexivity. }
  forward_if (temp _t'3 (Vint (bint (envelope len bs sig)))).
  { forward. entailer!. bfix. unfold envelope. rewrite H4. reflexivity. }
  { bfix. apply orb_false_iff in H4 as [L36 LE]. apply Z.ltb_ge in L36. apply negb_false_iff in LE.
    forward_if (temp _t'3 (Vint (bint (envelope len bs sig)))).
    { destruct sig as [s | ]; [ unfold literal; entailer! | subst sp; entailer! ]. }
    { destruct sig as [s | ]; [ | contradiction ].
      destruct H3 as [L4 Hs].
      forward_call (tsh, tp, ta, len, tn, bp, bsh, bs, sp, s).
      { specialize (H1 L36). unfold HEADER_BYTES in *. lia. }
      forward. forward. entailer!.
      fold (bint (signature_matches len bs s)). rewrite bint_negb, negb_involutive, bool2val_bint.
      unfold envelope. rewrite (proj2 (Z.ltb_ge len HEADER_BYTES)) by lia. rewrite LE. reflexivity. }
    { destruct sig as [s | ]; [ subst sp; contradiction | ].
      forward. entailer!. unfold envelope. rewrite (proj2 (Z.ltb_ge len HEADER_BYTES)) by lia. rewrite LE.
      reflexivity. } }
  forward_if.
  { forward. entailer!. bfix. rewrite validate_envelope, H4. reflexivity. }
  bfix. pose proof (envelope_false_len _ _ _ H4) as L36. specialize (H1 L36). unfold HEADER_BYTES in L36.
  forward. forward.
  forward_loop (EX k: Z,
    PROP (0 <= k <= len)
    LOCAL (temp _checksum (vi (checksum (sublist 0 k bs))); temp _byte (vi k); temp _table tp)
    SEP (data_at tsh t_sdt (ta, (bp, (vi len, tn))) tp;
         data_at bsh (tarray tuchar (Zlength bs)) (bytes_val bs) bp;
         match sig with Some s => literal s sp | None => emp end))%assert
  continue: (EX k: Z,
    PROP (0 <= k < len)
    LOCAL (temp _checksum (vi (checksum (sublist 0 (k + 1) bs))); temp _byte (vi k); temp _table tp)
    SEP (data_at tsh t_sdt (ta, (bp, (vi len, tn))) tp;
         data_at bsh (tarray tuchar (Zlength bs)) (bytes_val bs) bp;
         match sig with Some s => literal s sp | None => emp end))%assert
  break: (
    PROP ()
    LOCAL (temp _checksum (vi (checksum (sublist 0 len bs))); temp _table tp)
    SEP (data_at tsh t_sdt (ta, (bp, (vi len, tn))) tp;
         data_at bsh (tarray tuchar (Zlength bs)) (bytes_val bs) bp;
         match sig with Some s => literal s sp | None => emp end)).
  { Exists 0. entailer!. }
  { Intros k. forward.
    forward_if.
    { forward. forward.
      { entailer!. rewrite Znth_bytes_val by lia. apply tc_byte, byte_at; auto; lia. }
      rewrite Znth_bytes_val by lia.
      forward. Exists k. entailer!. apply checksum_next; auto; lia. }
    { forward. entailer!. assert (k = len) by lia. subst. reflexivity. } }
  { Intros k. forward. Exists (k + 1). entailer!. }
  pose proof (checksum_range (sublist 0 len bs)) as CR.
  forward_if.
  { assert (CK: (checksum (sublist 0 len bs) =? 0) = false) by (apply Z.eqb_neq; auto).
    forward. entailer!. rewrite validate_envelope, H4, CK. reflexivity. }
  assert (CK: (checksum (sublist 0 len bs) =? 0) = true) by (apply Z.eqb_eq; auto).
  forward. entailer!. rewrite validate_envelope, H4, CK. reflexivity.
Qed.
