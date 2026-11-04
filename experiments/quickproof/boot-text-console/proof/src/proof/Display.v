(* Bodies of boot_text_enable, boot_text_line and boot_text_putc. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import LeanosConsole.console.code.
Require Import LeanosConsole.proof.Defs.
Require Import LeanosConsole.proof.ConsoleSpecs.
Require Import LeanosConsole.proof.Easy.
#[local] Existing Instance ConsoleSpecs.CS.

Lemma or1792: forall s, 0 <= s < 256 -> Int.or (Int.repr 1792) (Int.repr s) = Int.repr (1792 + s).
Proof.
  intros. unfold Int.or. rewrite !Int.unsigned_repr by rep_lia.
  rewrite Z.lor_comm. pose proof (lor_mul s 7 8 ltac:(lia) ltac:(simpl; lia) ltac:(lia)) as L.
  change (7 * 2 ^ 8) with 1792 in L. rewrite L. f_equal. lia.
Qed.

Lemma ze16: forall x, 0 <= x < 65536 -> Int.zero_ext 16 (Int.repr x) = Int.repr x.
Proof.
  intros. unfold Int.zero_ext. rewrite Zbits.Zzero_ext_mod by lia.
  rewrite Int.unsigned_repr by rep_lia. rewrite Z.mod_small; [ reflexivity | ].
  split; [ lia | ]. eapply Z.lt_le_trans; [ apply H | ]. vm_compute. intro X; discriminate X.
Qed.

Lemma u16s_upd: forall i cs v, 0 <= i < Zlength cs ->
  upd_Znth i (u16s cs) (Vint (Int.repr v)) = u16s (upd_Znth i cs v).
Proof.
  intros. unfold u16s.
  rewrite (upd_Znth_map (fun v0 => Vint (Int.repr v0)) i cs v). reflexivity.
Qed.

Lemma shown_range: forall ch, 0 <= ch <= 255 -> 32 <= shown ch <= 126.
Proof. intros. unfold shown. destruct (ch <? 32) eqn:A; destruct (126 <? ch) eqn:B; simpl;
  rewrite ?Z.ltb_lt, ?Z.ltb_ge in *; lia. Qed.

(* The state after the cursor update of putc, before busy is cleared. *)
Definition putc_mid (c w: val) (sh: share) (stride width height row column ch: Z) : environ -> mpred :=
  EX row': Z, EX column': Z, EX cs': list Z,
  PROP (con_ok stride width height row' column'; Zlength cs' = (height * stride)%Z; u16_ok cs';
        (ch = 13 -> row' = row /\ column' = 0)%Z;
        (ch = 10 -> row' = (if row + 1 <? height then row + 1 else height - 1) /\ column' = 0)%Z;
        (ch <> 13 -> ch <> 10 ->
          1 <= column' /\ Znth (row' * stride + column' - 1) cs' = 1792 + shown ch)%Z)
  LOCAL (temp _c c)
  SEP (data_at Tsh t_con (con_val w stride width height row' column' 1 1) c;
       data_at sh (tarray tushort (height * stride)) (u16s cs') w).

Ltac absurd_branch :=
  match goal with
  | H: Int.repr 1 = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact H
  | H: ?x <> ?x |- _ => exfalso; apply H; reflexivity
  | H: Int.zero <> Int.zero |- _ => exfalso; apply H; reflexivity
  end.

Lemma body_boot_text_putc: semax_body Vprog Gprog f_boot_text_putc boot_text_putc_spec.
Proof.
  start_function.
  destruct H as (Hw & Hs & Hh & Hr & Hc).
  unfold con_val.
  forward.
  forward_if (PROP () LOCAL (temp _t'1 (Vint Int.zero); temp _c c; temp _ch (Vint (Int.repr ch)))
              SEP (data_at Tsh t_con (con_val w stride width height row column 1 0) c;
                   data_at sh (tarray tushort (height * stride)) (u16s cs) w)).
  { absurd_branch. }
  { forward. forward. entailer!. }
  unfold con_val.
  forward_if; [ absurd_branch | ].
  forward.
  forward_if (putc_mid c w sh stride width height row column ch).
  { (* CR *)
    assert (ch = 13) by (apply repr_inj_unsigned in H; rep_lia). subst ch.
    forward. unfold putc_mid. Exists row 0 cs. unfold con_val. entailer!.
    split; [ repeat split; lia | split; intros; lia ]. }
  { assert (ch <> 13) by (intro; subst; contradiction).
    forward_if (putc_mid c w sh stride width height row column ch).
    { (* LF *)
      subst ch.
      forward_call (c, w, sh, stride, width, height, row, column, 1, 1, cs).
      { repeat split; lia. }
      Intros cs'. unfold putc_mid.
      Exists (if row + 1 <? height then row + 1 else height - 1) 0 cs'. entailer!.
      destruct (row + 1 <? height) eqn:E; [ apply Z.ltb_lt in E | apply Z.ltb_ge in E ];
        repeat split; lia. }
    { assert (ch <> 10) by (intro; subst; contradiction).
      forward. forward.
      forward_if (EX row1: Z, EX col1: Z, EX cs1: list Z,
                  PROP (con_ok stride width height row1 col1; col1 < width;
                        Zlength cs1 = (height * stride)%Z; u16_ok cs1)
                  LOCAL (temp _t'1 (Vint Int.zero); temp _c c; temp _ch (Vint (Int.repr ch)))
                  SEP (data_at Tsh t_con (con_val w stride width height row1 col1 1 1) c;
                       data_at sh (tarray tushort (height * stride)) (u16s cs1) w)).
      { (* wrap *)
        forward_call (c, w, sh, stride, width, height, row, column, 1, 1, cs).
        { repeat split; lia. }
        Intros cs'.
        Exists (if row + 1 <? height then row + 1 else height - 1) 0 cs'. entailer!.
        destruct (row + 1 <? height) eqn:E; [ apply Z.ltb_lt in E | apply Z.ltb_ge in E ];
          repeat split; lia. }
      { forward. Exists row column cs. unfold con_val. entailer!. repeat split; lia. }
      Intros row1 col1 cs1.
      match goal with Hk: con_ok _ _ _ _ _ |- _ => destruct Hk as (_ & _ & _ & Hr1 & Hc1) end.
      forward_if (PROP ()
                  LOCAL (temp _t'2 (Vint (Int.repr (if ((ch <? 32) || (126 <? ch))%bool then 1 else 0)));
                         temp _t'1 (Vint Int.zero); temp _c c; temp _ch (Vint (Int.repr ch)))
                  SEP (data_at Tsh t_con (con_val w stride width height row1 col1 1 1) c;
                       data_at sh (tarray tushort (height * stride)) (u16s cs1) w)).
      { forward. entailer!. rewrite (proj2 (Z.ltb_lt ch 32)) by lia. reflexivity. }
      { forward. entailer!. rewrite (proj2 (Z.ltb_ge ch 32)) by lia. simpl orb.
        unfold bool2val. destruct (zlt 126 ch).
        - rewrite (proj2 (Z.ltb_lt 126 ch)) by lia. reflexivity.
        - rewrite (proj2 (Z.ltb_ge 126 ch)) by lia. reflexivity. }
      forward_if (PROP ()
                  LOCAL (temp _t'1 (Vint Int.zero); temp _c c; temp _ch (Vint (Int.repr (shown ch))))
                  SEP (data_at Tsh t_con (con_val w stride width height row1 col1 1 1) c;
                       data_at sh (tarray tushort (height * stride)) (u16s cs1) w)).
      { forward. entailer!. unfold shown.
        destruct ((ch <? 32) || (126 <? ch))%bool; [ reflexivity | absurd_branch ]. }
      { forward. entailer!. unfold shown.
        destruct ((ch <? 32) || (126 <? ch))%bool; [ absurd_branch | reflexivity ]. }
      pose proof (shown_range ch ltac:(rep_lia)) as Hsh.
      assert (Hidx: 0 <= row1 * stride + col1 < height * stride).
      { split; [ nia | ]. assert (row1 + 1 <= height) by lia.
        assert ((row1 + 1) * stride <= height * stride) by (apply Z.mul_le_mono_nonneg_r; lia). nia. }
      assert (Hhs: height * stride <= 16384) by (apply (Z.le_trans _ (64 * 256)); [ apply Z.mul_le_mono_nonneg; lia | lia ]).
      unfold con_val.
      forward. forward. forward. forward. forward.
      forward.
      rewrite or1792 by lia. rewrite !ze16 by lia. rewrite add_repr.
      rewrite u16s_upd by lia.
      unfold putc_mid.
      Exists row1 (col1 + 1) (upd_Znth (row1 * stride + col1) cs1 (1792 + shown ch)).
      unfold con_val. entailer!.
      split; [ repeat split; lia | ].
      split; [ rewrite upd_Znth_Zlength; lia | ].
      split; [ apply Forall_upd_Znth; [ exact H10 | lia ] | ].
      intros _ _. split; [ lia | ].
      replace (row1 * stride + (col1 + 1) - 1) with (row1 * stride + col1) by lia.
      apply upd_Znth_same. lia. }
  }
  unfold putc_mid. Intros row' column' cs'.
  unfold con_val. forward.
  Exists row' column' cs'. unfold con_val. entailer!.
Qed.
