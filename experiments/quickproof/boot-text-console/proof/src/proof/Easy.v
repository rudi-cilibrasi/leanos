(* Bodies of boot_text_u32, boot_text_disable and the three wrappers of patch/console_unit.c. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import LeanosConsole.console.code.
Require Import LeanosConsole.proof.Defs.
Require Import LeanosConsole.proof.ConsoleSpecs.
#[local] Existing Instance ConsoleSpecs.CS.

Lemma Znth_bytes: forall i bs, 0 <= i < Zlength bs -> Znth i (bytes bs) = Vint (Int.repr (Znth i bs)).
Proof. intros. unfold bytes. rewrite Znth_map by lia. reflexivity. Qed.

Lemma byte_of: forall bs i, bytes_ok bs -> 0 <= i < Zlength bs -> 0 <= Znth i bs <= Byte.max_unsigned.
Proof. intros bs i H Hi. exact (proj1 (Forall_Znth bs _) H i Hi). Qed.

Lemma u8_addr: forall base n i, field_compatible (tarray tuchar n) [] base -> 0 <= i < n ->
  field_address (tarray tuchar n) [ArraySubsc i] base = offset_val i base.
Proof.
  intros. rewrite field_address_offset.
  - simpl. f_equal. lia.
  - apply field_compatible_cons. simpl. split; [ lia | auto ].
Qed.

Lemma lor_shift: forall a b n, 0 <= n -> 0 <= a < 2 ^ n -> 0 <= b -> Z.lor a (Z.shiftl b n) = a + b * 2 ^ n.
Proof.
  intros a b n Hn Ha Hb. rewrite Z.shiftl_mul_pow2 by lia.
  assert (Hand: Z.land a (b * 2 ^ n) = 0).
  { apply Z.bits_inj_0. intros i. rewrite Z.land_spec. destruct (zlt i n).
    - destruct (zlt i 0); [ rewrite Z.testbit_neg_r by lia; reflexivity | ].
      rewrite <- Z.shiftl_mul_pow2 by lia. rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
    - rewrite <- (Z.mod_small a (2 ^ n)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
  rewrite <- Z.lxor_lor by exact Hand. rewrite <- Z.add_nocarry_lxor by exact Hand. reflexivity.
Qed.

Lemma lor_mul: forall a b n, 0 <= n -> 0 <= a < 2 ^ n -> 0 <= b -> Z.lor a (b * 2 ^ n) = a + b * 2 ^ n.
Proof. intros. pose proof (lor_shift a b n H H0 H1) as E. rewrite Z.shiftl_mul_pow2 in E by lia. exact E. Qed.

Lemma le32_int: forall b0 b1 b2 b3,
  0 <= b0 <= 255 -> 0 <= b1 <= 255 -> 0 <= b2 <= 255 -> 0 <= b3 <= 255 ->
  Int.or (Int.or (Int.or (Int.repr b0) (Int.shl (Int.repr b1) (Int.repr 8)))
                 (Int.shl (Int.repr b2) (Int.repr 16))) (Int.shl (Int.repr b3) (Int.repr 24))
  = Int.repr (b0 + b1 * 256 + b2 * 65536 + b3 * 16777216).
Proof.
  intros.
  assert (S8: Int.shl (Int.repr b1) (Int.repr 8) = Int.repr (b1 * 256)).
  { unfold Int.shl. rewrite !Int.unsigned_repr by rep_lia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. }
  assert (S16: Int.shl (Int.repr b2) (Int.repr 16) = Int.repr (b2 * 65536)).
  { unfold Int.shl. rewrite !Int.unsigned_repr by rep_lia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. }
  assert (S24: Int.shl (Int.repr b3) (Int.repr 24) = Int.repr (b3 * 16777216)).
  { unfold Int.shl. rewrite !Int.unsigned_repr by rep_lia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. }
  pose proof (lor_mul b0 b1 8 ltac:(lia) ltac:(simpl; lia) ltac:(lia)) as L1. change (2 ^ 8) with 256 in L1.
  pose proof (lor_mul (b0 + b1 * 256) b2 16 ltac:(lia) ltac:(simpl; lia) ltac:(lia)) as L2. change (2 ^ 16) with 65536 in L2.
  pose proof (lor_mul (b0 + b1 * 256 + b2 * 65536) b3 24 ltac:(lia) ltac:(simpl; lia) ltac:(lia)) as L3.
  change (2 ^ 24) with 16777216 in L3.
  rewrite S8, S16, S24. unfold Int.or.
  rewrite (Int.unsigned_repr b0) by rep_lia. rewrite (Int.unsigned_repr (b1 * 256)) by rep_lia.
  rewrite L1. rewrite (Int.unsigned_repr (b0 + b1 * 256)) by rep_lia.
  rewrite (Int.unsigned_repr (b2 * 65536)) by rep_lia. rewrite L2.
  rewrite (Int.unsigned_repr (b0 + b1 * 256 + b2 * 65536)) by rep_lia.
  rewrite (Int.unsigned_repr (b3 * 16777216)) by rep_lia. rewrite L3. reflexivity.
Qed.

Ltac u8_load i :=
  match goal with
  | |- context [Sset _ (Ederef (Ebinop Oadd (Etempvar _p _) (Econst_int (Int.repr i) _) _) _)] =>
      assert_PROP (force_val (sem_add_ptr_int tuchar Signed (offset_val _ _) (Vint (Int.repr i))) =
                   field_address (tarray tuchar (Zlength _)) [ArraySubsc (_ + i)] _)
  end.

Ltac byte_tc :=
  entailer!; rewrite Znth_bytes by lia; simpl; rewrite ?Int.unsigned_repr by rep_lia; rep_lia.

Lemma body_boot_text_u32: semax_body Vprog Gprog f_boot_text_u32 boot_text_u32_spec.
Proof.
  start_function.
  assert_PROP (field_compatible (tarray tuchar (Zlength bs)) [] base) as FC by entailer!.
  assert (B0 := byte_of bs k H1 ltac:(lia)).
  assert (B1 := byte_of bs (k + 1) H1 ltac:(lia)).
  assert (B2 := byte_of bs (k + 2) H1 ltac:(lia)).
  assert (B3 := byte_of bs (k + 3) H1 ltac:(lia)).
  assert_PROP (force_val (sem_add_ptr_int tuchar Signed (offset_val k base) (Vint (Int.repr 0))) =
               field_address (tarray tuchar (Zlength bs)) [ArraySubsc (k + 0)] base) as A0.
  { entailer!. rewrite u8_addr by (auto; lia). simpl. rewrite ?offset_offset_val. reflexivity || (f_equal; lia). }
  forward; [ byte_tc | ].
  assert_PROP (force_val (sem_add_ptr_int tuchar Signed (offset_val k base) (Vint (Int.repr 1))) =
               field_address (tarray tuchar (Zlength bs)) [ArraySubsc (k + 1)] base) as A1.
  { entailer!. rewrite u8_addr by (auto; lia). simpl. rewrite ?offset_offset_val. reflexivity || (f_equal; lia). }
  forward; [ byte_tc | ].
  assert_PROP (force_val (sem_add_ptr_int tuchar Signed (offset_val k base) (Vint (Int.repr 2))) =
               field_address (tarray tuchar (Zlength bs)) [ArraySubsc (k + 2)] base) as A2.
  { entailer!. rewrite u8_addr by (auto; lia). simpl. rewrite ?offset_offset_val. reflexivity || (f_equal; lia). }
  forward; [ byte_tc | ].
  assert_PROP (force_val (sem_add_ptr_int tuchar Signed (offset_val k base) (Vint (Int.repr 3))) =
               field_address (tarray tuchar (Zlength bs)) [ArraySubsc (k + 3)] base) as A3.
  { entailer!. rewrite u8_addr by (auto; lia). simpl. rewrite ?offset_offset_val. reflexivity || (f_equal; lia). }
  forward; [ byte_tc | ].
  forward.
  rewrite !Znth_bytes by lia. replace (k + 0) with k by lia.
  entailer!. simpl. rewrite le32_int by rep_lia. reflexivity.
Qed.

Lemma body_boot_text_disable: semax_body Vprog Gprog f_boot_text_disable boot_text_disable_spec.
Proof.
  start_function. forward. entailer!.
Qed.

Lemma body_console_parse: semax_body Vprog Gprog f_console_parse console_parse_spec.
Proof.
  start_function.
  forward_call (info, sh, bs, out).
  Intros g. forward. Exists g. entailer!.
Qed.

Lemma body_console_enable: semax_body Vprog Gprog f_console_enable console_enable_spec.
Proof.
  start_function.
  forward_call (c, gp, g, w, sh, cs).
  Intros cs'. forward. Exists cs'. entailer!.
Qed.

Lemma body_console_putc: semax_body Vprog Gprog f_console_putc console_putc_spec.
Proof.
  start_function.
  forward_call (c, w, sh, stride, width, height, row, column, cs, ch).
  Intros vret. destruct vret as [[row' column'] cs']. simpl fst in *; simpl snd in *.
  Exists row' column' cs'. entailer!.
Qed.
