(* Body of boot_text_parse: it computes Defs.parse_model. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import LeanosConsole.console.code.
Require Import LeanosConsole.proof.Defs.
Require Import LeanosConsole.proof.ConsoleSpecs.
Require Import LeanosConsole.proof.Easy.
Require LeanosConsole.proof.ModelProof.
#[local] Existing Instance ConsoleSpecs.CS.

Definition zero_geo := mkgeo 0 0 0 0 0 0.
Definition out_geo (s: option geo) : geo := match s with Some g => g | None => zero_geo end.

Ltac to_z :=
  repeat match goal with
  | H: Int.repr (Z.b2z ?c) = Int.zero |- _ =>
      let E := fresh "E" in
      destruct c eqn:E; [ simpl in H; exfalso; apply Int.one_not_zero; exact H | clear H ]
  | H: Int.repr (Z.b2z ?c) <> Int.zero |- _ =>
      let E := fresh "E" in
      destruct c eqn:E; [ clear H | simpl in H; exfalso; apply H; reflexivity ]
  | H: orb _ _ = true |- _ => apply orb_prop in H; destruct H
  | H: orb _ _ = false |- _ => apply orb_false_elim in H; destruct H
  | H: negb ?c = true |- _ => apply negb_true_iff in H
  | H: negb ?c = false |- _ => apply negb_false_iff in H
  | H: (_ <? _) = true |- _ => apply Z.ltb_lt in H
  | H: (_ <? _) = false |- _ => apply Z.ltb_ge in H
  | H: (_ =? _) = true |- _ => apply Z.eqb_eq in H
  | H: (_ =? _) = false |- _ => apply Z.eqb_neq in H
  end.

Ltac bcase :=
  repeat match goal with
  | |- context [?a <? ?b] => destruct (Z.ltb_spec a b)
  | |- context [?a =? ?b] => destruct (Z.eqb_spec a b)
  | |- context [zlt ?a ?b] => destruct (zlt a b)
  | |- context [zeq ?a ?b] => destruct (zeq a b)
  end; simpl; try lia; auto.

Lemma and7: forall t, 0 <= t <= Int.max_unsigned -> Int.and (Int.repr t) (Int.repr 7) = Int.repr (t mod 8).
Proof.
  intros. unfold Int.and. rewrite !Int.unsigned_repr by rep_lia.
  change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity.
Qed.

Ltac bt name := match goal with H: Int.repr (Z.b2z ?c) <> Int.zero |- _ =>
  assert (name: c = true) by (destruct c; [ reflexivity | exfalso; apply H; reflexivity ]); clear H end.
Ltac bf name := match goal with H: Int.repr (Z.b2z ?c) = Int.zero |- _ =>
  assert (name: c = false) by (destruct c; [ exfalso; apply Int.one_not_zero; exact H | reflexivity ]); clear H end.

(* (size + 7u) & ~7u, checked in Z for every size the loop can see. *)
Lemma not7: Int.unsigned (Int.not (Int.repr 7)) = 4294967288.
Proof. reflexivity. Qed.
Definition r8_ok (s: Z) : bool := Z.eqb (Z.land (s + 7) 4294967288) (round8 s).
Fixpoint r8_upto (k: nat) (z: Z) : bool :=
  match k with O => true | S k' => (r8_ok z && r8_upto k' (z + 1))%bool end.
Lemma r8_upto_spec: forall k z, r8_upto k z = true -> forall s, z <= s < z + Z.of_nat k -> r8_ok s = true.
Proof.
  induction k; intros z H s Hs; simpl in *; [ lia | ].
  apply andb_prop in H. destruct H as [H1 H2].
  destruct (zeq s z); [ subst; exact H1 | apply (IHk (z + 1)); [ exact H2 | lia ] ].
Qed.
Lemma r8_all: r8_upto (Z.to_nat 65537) 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma round8_int: forall s, 0 <= s <= 65536 ->
  Int.and (Int.add (Int.repr s) (Int.repr 7)) (Int.not (Int.repr 7)) = Int.repr (round8 s).
Proof.
  intros. unfold Int.and at 1. rewrite not7. unfold Int.add.
  rewrite (Int.unsigned_repr s) by rep_lia. rewrite (Int.unsigned_repr 7) by rep_lia.
  rewrite Int.unsigned_repr by rep_lia.
  f_equal. apply Z.eqb_eq. apply (r8_upto_spec _ _ r8_all). lia.
Qed.
Lemma round8_bounds: forall s, 0 <= s -> s <= round8 s <= s + 7.
Proof. intros. unfold round8. pose proof (Z.div_mod (s + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (s + 7) 8 ltac:(lia)). lia. Qed.

Ltac use_bool :=
  match goal with
  | Hc: ?b = true |- context [?b] => rewrite Hc
  | Hc: ?b = false |- context [?b] => rewrite Hc
  end; reflexivity.

Lemma zero_geo_wf: geo_wf zero_geo.
Proof. unfold geo_wf, zero_geo; simpl; rep_lia. Qed.

Ltac finish_none HN :=
  unfold parse_result; rewrite ?HN;
  repeat match goal with
  | |- _ /\ _ => split
  | |- forall g', _ = Some g' -> _ => let Hs := fresh in intros ? Hs; rewrite HN in Hs; discriminate
  | |- geo_wf zero_geo => apply zero_geo_wf
  | |- geo_wf _ => assumption
  end; try reflexivity.

Lemma parse_model_short: forall bs n, n < 16 -> parse_model bs n = None.
Proof. intros. unfold parse_model. rewrite (proj2 (Z.ltb_lt n 16)) by lia. reflexivity. Qed.

Lemma parse_model_long: forall bs n, 16 <= n ->
  parse_model bs n =
  if ((le32 bs 0 <? 16) || (n <? le32 bs 0) || (65536 <? le32 bs 0) || negb (le32 bs 0 mod 8 =? 0) ||
      negb (le32 bs 4 =? 0))%bool
  then None else walk (Z.to_nat (le32 bs 0)) bs (le32 bs 0) 8 None.
Proof. intros. unfold parse_model. rewrite (proj2 (Z.ltb_ge n 16)) by lia. reflexivity. Qed.

Lemma none_post: forall bs g, geo_wf g -> parse_model bs (Zlength bs) = None ->
  geo_wf g /\ (forall g', parse_model bs (Zlength bs) = Some g' -> g' = g) /\
  Vint (Int.repr 0) = Vint (Int.repr (parse_result bs (Zlength bs))).
Proof. intros bs g W E. unfold parse_result. rewrite E. split; [ exact W | split; [ intros; discriminate | reflexivity ] ]. Qed.

Lemma walk_stop: forall f bs total offset seen, total - 8 < offset -> walk f bs total offset seen = None.
Proof. intros. destruct f; simpl; [ reflexivity | ]. rewrite (proj2 (Z.leb_gt offset (total - 8))) by lia. reflexivity. Qed.

Lemma walk_S_unfold: forall f bs total offset seen, walk (S f) bs total offset seen =
  if offset <=? total - 8 then
    if ((le32 bs (offset + 4) <? 8) || (total - offset <? le32 bs (offset + 4)))%bool then None else
    if total - offset <? round8 (le32 bs (offset + 4)) then None else
    if le32 bs offset =? 0 then
      match seen with
      | Some g => if ((le32 bs (offset + 4) =? 8) && (offset + round8 (le32 bs (offset + 4)) =? total) &&
                      geo_valid g)%bool then Some g else None
      | None => None
      end
    else if le32 bs offset =? 8 then
      match seen with
      | Some _ => None
      | None => if le32 bs (offset + 4) <? 32 then None
                else walk f bs total (offset + round8 (le32 bs (offset + 4))) (Some (geo_at bs offset))
      end
    else walk f bs total (offset + round8 (le32 bs (offset + 4))) seen
  else None.
Proof. reflexivity. Qed.

Lemma Znth_byte_any: forall bs i, bytes_ok bs -> 0 <= Znth i bs <= Byte.max_unsigned.
Proof.
  intros bs i H. destruct (zlt i 0).
  - rewrite Znth_underflow by lia. cbv [default Inhabitant_Z]. rep_lia.
  - destruct (zlt i (Zlength bs)).
    + apply byte_of; auto; lia.
    + rewrite Znth_overflow by lia. cbv [default Inhabitant_Z]. rep_lia.
Qed.

Lemma geo_at_wf: forall bs o, bytes_ok bs -> geo_wf (geo_at bs o).
Proof.
  intros bs o H. unfold geo_wf, geo_at; simpl.
  pose proof (le32_range bs (o + 8) H). pose proof (le32_range bs (o + 12) H).
  pose proof (le32_range bs (o + 16) H). pose proof (le32_range bs (o + 20) H).
  pose proof (le32_range bs (o + 24) H).
  pose proof (Znth_byte_any bs (o + 28) H). pose proof (Znth_byte_any bs (o + 29) H).
  repeat split; rep_lia.
Qed.

Lemma addr64: forall lo hi, 0 <= lo <= Int.max_unsigned -> 0 <= hi <= Int.max_unsigned ->
  Int64.or (Int64.repr lo) (Int64.shl (Int64.repr hi) (Int64.repr 32)) = Int64.repr (lo + hi * 4294967296).
Proof.
  intros. unfold Int64.or, Int64.shl.
  rewrite (Int64.unsigned_repr hi) by rep_lia. rewrite (Int64.unsigned_repr 32) by rep_lia.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 32) with 4294967296.
  rewrite (Int64.unsigned_repr lo) by rep_lia. rewrite (Int64.unsigned_repr (hi * 4294967296)) by rep_lia.
  f_equal. pose proof (lor_mul lo hi 32 ltac:(lia) ltac:(change (2 ^ 32) with 4294967296; rep_lia) ltac:(lia)) as L.
  change (2 ^ 32) with 4294967296 in L. exact L.
Qed.

Ltac absurd_int :=
  exfalso;
  match goal with
  | Hz: Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero; exact Hz
  | Hz: Int.repr 0 <> Int.zero |- _ => apply Hz; reflexivity
  | Hz: Int.one = Int.zero |- _ => apply Int.one_not_zero; exact Hz
  end.

Lemma body_boot_text_parse: semax_body Vprog Gprog f_boot_text_parse boot_text_parse_spec.
Proof.
  start_function.
  forward.
  do 6 forward.
  replace_SEP 1 (data_at Tsh t_geo (geo_val zero_geo) out).
  { entailer!. }
  forward_if.
  { forward. Exists zero_geo. entailer!. apply none_post; [ apply zero_geo_wf | apply parse_model_short; lia ]. }
  assert_PROP (field_compatible (tarray tuchar (Zlength bs)) [] info) as FC by entailer!.
  forward_call (sh, info, bs, 0).
  assert (RT := le32_range bs 0 H0).
  set (T := le32 bs 0) in *.
  forward_if (temp _t'2 (Vint (Int.repr (Z.b2z ((T <? 16) || (Zlength bs <? T))%bool)))).
  { forward. entailer!. bcase. }
  { forward. entailer!. bcase. }
  forward_if (temp _t'3 (Vint (Int.repr (Z.b2z ((T <? 16) || (Zlength bs <? T) || (65536 <? T))%bool)))).
  { forward. entailer!. to_z; bcase. }
  { forward. entailer!. to_z; bcase. }
  forward_if (temp _t'4 (Vint (Int.repr (Z.b2z ((T <? 16) || (Zlength bs <? T) || (65536 <? T) ||
                                                 negb (T mod 8 =? 0))%bool)))).
  { forward. entailer!. to_z; bcase. }
  { forward. entailer!. to_z.
    change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
    assert (Hm: 0 <= T mod 8 < 8) by (apply Z.mod_pos_bound; lia).
    unfold Int.eq. rewrite Int.unsigned_repr by rep_lia. change (Int.unsigned Int.zero) with 0.
    bcase. }
  forward_if (temp _t'5 (Vint (Int.repr (Z.b2z ((T <? 16) || (Zlength bs <? T) || (65536 <? T) ||
                                                 negb (T mod 8 =? 0) || negb (le32 bs 4 =? 0))%bool)))).
  { forward. entailer!. to_z; bcase. }
  { to_z. forward_call (sh, info, bs, 4).
    assert (R4 := le32_range bs 4 H0).
    forward. entailer!. bcase. }
  forward_if.
  { forward. Exists zero_geo. entailer!. apply none_post; [ apply zero_geo_wf | ].
    rewrite parse_model_long by lia. fold T. to_z; bcase. }
  to_z.
  assert (HM: parse_model bs (Zlength bs) = walk (Z.to_nat T) bs T 8 None).
  { rewrite parse_model_long by lia. fold T. bcase. }
  forward. forward.
  forward_while (EX offset: Z, EX seen: option geo, EX f: nat,
    PROP (8 <= offset <= T; (Z.to_nat (T - offset + 8) <= f)%nat;
          walk f bs T offset seen = parse_model bs (Zlength bs); geo_wf (out_geo seen))
    LOCAL (temp _offset (Vint (Int.repr offset)); temp _seen (Vint (Int.repr (if seen then 1 else 0)));
           temp _total (Vint (Int.repr T)); temp _cleared out; temp _info info;
           temp _available (Vint (Int.repr (Zlength bs))); temp _out out)
    SEP (data_at sh (tarray tuchar (Zlength bs)) (bytes bs) info;
         data_at Tsh t_geo (geo_val (out_geo seen)) out)).
  { Exists 8 (@None geo) (Z.to_nat T). entailer!. apply zero_geo_wf. }
  { entailer!. }
  { forward.
    assert_PROP (force_val (sem_binary_operation' Oadd (tptr tuchar) tuint info (Vint (Int.repr offset))) =
                 offset_val offset info) as TAG.
    { entailer!. }
    rewrite TAG. clear TAG.
    forward_call (sh, info, bs, offset).
    forward_call (sh, info, bs, offset + 4).
    assert (RTY := le32_range bs offset H0). assert (RSZ := le32_range bs (offset + 4) H0).
    destruct f as [ | f']; [ exfalso; lia | ].
    rewrite walk_S_unfold, (proj2 (Z.leb_le offset (T - 8))) in H9 by lia.
    forward_if (temp _t'9 (Vint (Int.repr (Z.b2z ((le32 bs (offset + 4) <? 8) ||
                                                   (T - offset <? le32 bs (offset + 4)))%bool)))).
    { forward. entailer!. bcase. }
    { forward. entailer!. bcase. }
    forward_if.
    { match goal with Hc: orb _ _ = true |- _ => rewrite Hc in H9 end.
      forward. Exists (out_geo seen). entailer!. finish_none (eq_sym H9). }
    match goal with Hc: orb _ _ = false |- _ => rewrite Hc in H9; pose proof Hc as B' end. to_z.
    forward.
    rewrite round8_int by lia.
    set (SZ := le32 bs (offset + 4)) in *. set (TY := le32 bs offset) in *. clearbody SZ TY.
    assert (R8 := round8_bounds SZ ltac:(lia)).
    forward_if.
    { assert (HN: parse_model bs (Zlength bs) = None).
      { rewrite <- H9. rewrite (proj2 (Z.ltb_lt (T - offset) (round8 SZ))) by lia. reflexivity. }
      forward. Exists (out_geo seen). entailer!. finish_none HN. }
    rewrite (proj2 (Z.ltb_ge (T - offset) (round8 SZ))) in H9 by lia.
    forward_if.
    { (* the end tag *)
      rewrite (proj2 (Z.eqb_eq TY 0)) in H9 by lia.
      destruct seen as [g | ]; simpl out_geo in *.
      - forward_if (temp _t'10 (Vint (Int.repr (Z.b2z (negb (SZ =? 8) || negb (offset + round8 SZ =? T))%bool)))).
        { forward. entailer!. bcase. }
        { forward. entailer!. bcase. }
        forward_if (temp _t'11 (Vint (Int.repr (Z.b2z (negb (SZ =? 8) || negb (offset + round8 SZ =? T))%bool)))).
        { forward. entailer!. use_bool. }
        { forward. entailer!. use_bool. }
        forward_if.
        { assert (HN: parse_model bs (Zlength bs) = None).
          { rewrite <- H9. to_z.
            - rewrite (proj2 (Z.eqb_neq SZ 8)) by lia. reflexivity.
            - rewrite (proj2 (Z.eqb_neq (offset + round8 SZ) T)) by lia. rewrite andb_false_r. reflexivity. }
          forward. Exists g. entailer!. finish_none HN. }
        to_z.
        rewrite (proj2 (Z.eqb_eq SZ 8)), (proj2 (Z.eqb_eq (offset + round8 SZ) T)) in H9 by lia.
        destruct H10 as (W1 & W2 & W3 & W4 & W5 & W6).
        unfold geo_val. apply seq_assoc1.
        do 6 (apply seq_assoc1; forward;
              try solve [ entailer!; simpl; rewrite ?Int.unsigned_repr by rep_lia; rep_lia ]).
        forward_call (g_kind g, g_bits g, g_address g, g_pitch g, g_width g, g_height g).
        forward.
        Exists g. entailer!.
        unfold parse_result. match goal with Hm: _ = parse_model bs (Zlength bs) |- _ => rewrite <- Hm end.
        unfold geo_valid. simpl andb.
        destruct (valid_geo (g_kind g) (g_bits g) (g_address g) (g_pitch g) (g_width g) (g_height g));
          (split; [ unfold geo_wf; repeat split; lia | split; [ intros g' Hs; congruence | reflexivity ] ]).
      - forward_if (temp _t'10 (Vint (Int.repr (Z.b2z (negb (SZ =? 8) || negb (offset + round8 SZ =? T))%bool)))).
        { forward. entailer!. bcase. }
        { forward. entailer!. bcase. }
        forward_if (temp _t'11 (Vint (Int.repr 1))).
        { forward. entailer!. }
        { forward. entailer!. }
        forward_if.
        { forward. Exists zero_geo. entailer!. finish_none (eq_sym H9). }
        exfalso. match goal with Hz: Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero; exact Hz end. }
    rewrite (proj2 (Z.eqb_neq TY 0)) in H9 by lia.
    forward_if (EX seen': option geo,
      PROP (walk f' bs T (offset + round8 SZ) seen' = parse_model bs (Zlength bs); geo_wf (out_geo seen'))
      LOCAL (temp _advance (Vint (Int.repr (round8 SZ))); temp _offset (Vint (Int.repr offset));
             temp _seen (Vint (Int.repr (if seen' then 1 else 0)));
             temp _total (Vint (Int.repr T)); temp _cleared out; temp _info info;
             temp _available (Vint (Int.repr (Zlength bs))); temp _out out)
      SEP (data_at sh (tarray tuchar (Zlength bs)) (bytes bs) info;
           data_at Tsh t_geo (geo_val (out_geo seen')) out)).
    { (* a framebuffer tag *)
      rewrite (proj2 (Z.eqb_eq TY 8)) in H9 by lia.
      destruct seen as [g0 | ]; simpl out_geo in *.
      - forward_if (temp _t'13 (Vint (Int.repr 1))).
        { forward. entailer!. }
        { absurd_int. }
        forward_if; [ | absurd_int ].
        forward. Exists g0. entailer!. finish_none (eq_sym H9).
      - forward_if (temp _t'13 (Vint (Int.repr (Z.b2z (SZ <? 32))))).
        { absurd_int. }
        { forward. entailer!. bcase. }
        forward_if.
        { assert (HN: parse_model bs (Zlength bs) = None).
          { rewrite <- H9. to_z. rewrite (proj2 (Z.ltb_lt SZ 32)) by lia. reflexivity. }
          forward. Exists zero_geo. entailer!. finish_none HN. }
        to_z. rewrite (proj2 (Z.ltb_ge SZ 32)) in H9 by lia.
        forward.
        forward_call (sh, info, bs, offset + 8).
        forward_call (sh, info, bs, offset + 12).
        assert (R8a := le32_range bs (offset + 8) H0). assert (R12 := le32_range bs (offset + 12) H0).
        unfold geo_val, zero_geo; simpl g_address; simpl g_pitch; simpl g_width; simpl g_height;
          simpl g_kind; simpl g_bits.
        forward.
        forward_call (sh, info, bs, offset + 16). forward.
        forward_call (sh, info, bs, offset + 20). forward.
        forward_call (sh, info, bs, offset + 24). forward.
        assert (B28 := byte_of bs (offset + 28) H0 ltac:(lia)).
        assert (B29 := byte_of bs (offset + 29) H0 ltac:(lia)).
        assert_PROP (force_val (sem_add_ptr_int tuchar Signed (offset_val offset info) (Vint (Int.repr 28))) =
                     field_address (tarray tuchar (Zlength bs)) (SUB (offset + 28)) info) as A28.
        { entailer!. rewrite u8_addr by (auto; lia). simpl. rewrite ?offset_offset_val.
          reflexivity || (f_equal; lia). }
        forward; [ byte_tc | ].
        forward.
        assert_PROP (force_val (sem_add_ptr_int tuchar Signed (offset_val offset info) (Vint (Int.repr 29))) =
                     field_address (tarray tuchar (Zlength bs)) (SUB (offset + 29)) info) as A29.
        { entailer!. rewrite u8_addr by (auto; lia). simpl. rewrite ?offset_offset_val.
          reflexivity || (f_equal; lia). }
        forward; [ byte_tc | ].
        forward.
        Exists (Some (geo_at bs offset)). entailer!.
        + simpl out_geo. apply geo_at_wf. exact H0.
        + apply derives_refl'. f_equal. simpl out_geo. unfold geo_val, geo_at; simpl.
          rewrite addr64 by rep_lia. rewrite !Znth_bytes by lia. reflexivity. }
    { forward. Exists seen. entailer!. rewrite (proj2 (Z.eqb_neq TY 8)) in H9 by lia. exact H9. }
    Intros seen'. forward.
    Exists (offset + round8 SZ, seen', f'). entailer!. split; [ lia | lia ]. }
  forward. Exists (out_geo seen). entailer!. apply none_post; [ exact H10 | ].
  rewrite <- H9. apply walk_stop. lia.
Qed.
