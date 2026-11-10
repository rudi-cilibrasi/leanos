(* wifi_image_header from the version-2/3 test on: the length test, the target's fields and its checks, the
   header length 32, then the version-2 return or the version-3 part (HdV3). *)
Require Import VST.floyd.proofauto.
Require Import LeanosDeviceProgramImage.device_program.code.
Require Import LeanosDeviceProgramImage.proof.Specs.
Require Import LeanosDeviceProgramImage.proof.BodyLookup.
Require Import LeanosDeviceProgramImage.proof.BodyPolicy.
Require Import LeanosDeviceProgramImage.proof.BodyAdmit.
Require Import LeanosDeviceProgramImage.proof.HdDefs.
Require Import LeanosDeviceProgramImage.proof.HdArith.
Require Import LeanosDeviceProgramImage.proof.HdV3.
#[local] Existing Instance Specs.CS.
Local Open Scope Z_scope.

Lemma hd_target {Espec: OracleKind} sh image bs tsh tp psh pp P0 hsh hp:
  readable_share sh -> writable_share tsh -> writable_share psh -> writable_share hsh ->
  image_ok bs -> policy_wf P0 ->
  field_compatible t_policy [] pp -> field_compatible (tarray tuchar (Zlength bs)) [] image ->
  16 <= Zlength bs -> le32 bs 0 = MAGIC -> le32 bs 4 <> 1 ->
  forall Delta R c, Delta = Delta_hd -> R = Post_hd sh image bs tsh tp psh pp P0 hsh hp -> c = s_target ->
  semax Delta
    (PROP ()
     LOCAL (temp _version (Vint (Int.repr (le32 bs 4))); temp _image image;
            temp _image_len (Vint (Int.repr (Zlength bs))); temp _t tp; temp _pol pp; temp _header_len hp)
     SEP (data_at sh (tarray tuchar (Zlength bs)) (bytes_val bs) image;
          data_at tsh t_target (default_val t_target) tp;
          field_at psh t_policy (DOT _present) (Vint (Int.repr 0)) pp;
          field_at psh t_policy (DOT _dma) (Vint (Int.repr 0)) pp;
          field_at psh t_policy (DOT _window) (Vint (Int.repr 0)) pp;
          spacer psh 12 16 pp;
          field_at psh t_policy (DOT _cfg_read) (Vlong (Int64.repr 0)) pp;
          field_at psh t_policy (DOT _cfg_write) (Vlong (Int64.repr 0)) pp;
          field_at psh t_policy (DOT _cmd_clear) (Vint (Int.repr 0)) pp;
          field_at psh t_policy (DOT _cmd_set) (Vint (Int.repr 0)) pp;
          field_at psh t_policy (DOT _sink_count) (Vint (Int.repr 0)) pp;
          field_at psh t_policy (DOT _sinks) (words_val (pl_sinks P0)) pp;
          field_at psh t_policy (DOT _desc_count) (Vint (Int.repr 0)) pp;
          data_at psh (tarray t_desc 16) (map desc_val (pl_descs P0)) (offset_val 80 pp);
          data_at hsh tuint (default_val tuint) hp))
    c R.
Proof.
  intros SH TSH PSH HSH IOK PW FCp FCi L16 M0 V1 Delta R c -> -> ->.
  unfold s_target, Post_hd, Delta_hd. start_tail.
  pose proof IOK as (LB & U8).
  assert (W: forall k, u32_ok (le32 bs k)) by (intros; apply le32_range; auto).
  assert (Wr: forall k, 0 <= le32 bs k <= Int.max_unsigned) by (intros; apply W).
  assert (PI: isptr image) by (destruct FCi; auto).
  pose proof (Wr 4) as Wv. pose proof (Wr 16) as W16. pose proof (Wr 20) as W20. pose proof (Wr 24) as W24.
  pose proof (Wr 28) as W28.
  fif_t _t'4 (Vint (Int.repr (Z.b2z (negb (le32 bs 4 =? 2) && negb (le32 bs 4 =? 3))%bool))).
  { forward. entailer!. repr_facts Wr; bjoin. }
  { forward. entailer!. repr_facts Wr; bjoin. }
  fif_t _t'5 (Vint (Int.repr (Z.b2z ((negb (le32 bs 4 =? 2) && negb (le32 bs 4 =? 3)) ||
                                       (Zlength bs <? (if le32 bs 4 =? 3 then 68 else 32)))%bool))).
  { forward. entailer!. repr_facts Wr; bjoin. }
  { fif_t _t'6 (Vint (Int.repr (if le32 bs 4 =? 3 then 68 else 32))).
    { forward. entailer!. repr_facts Wr; bjoin. }
    { forward. entailer!. repr_facts Wr; bjoin. }
    forward. entailer!. destruct (le32 bs 4 =? 3); repr_facts Wr; bjoin. }
  forward_if.
  { assert (D: decode bs = None) by dec_solve. hd_bad D. }
  rename H into C2. apply orb_false_iff in C2 as [C2a C2b]. apply Z.ltb_ge in C2b.
  assert (V23: le32 bs 4 = 2 \/ le32 bs 4 = 3)
    by (destruct (Z.eqb_spec (le32 bs 4) 2), (Z.eqb_spec (le32 bs 4) 3); cbn in C2a; try discriminate; lia).
  assert (L32: 32 <= Zlength bs) by (destruct (le32 bs 4 =? 3); lia).
  forward_call (sh, image, bs, 16).
  do 3 forward.
  forward_call (sh, image, bs, 20). 
  forward.
  forward_call (sh, image, bs, 24). 
  forward.
  forward_call (sh, image, bs, 28).
  rewrite !shru_and by (first [ apply Wr | lia ]). rewrite and_repr.
  fif_t _t'11 (Vint (Int.repr (bar_of (le32 bs 28)))).
  { repr_facts Wr. forward_call (sh, image, bs, 28). forward. entailer!.
    unfold bar_of. rewrite (proj2 (Z.eqb_neq _ _)) by auto. reflexivity. }
  { repr_facts Wr. forward. entailer!. unfold bar_of. rewrite R. reflexivity. }
  forward.
  pose proof (bar_of_range (le32 bs 28) (Wr 28)) as BR.
  forward.
  fif_t _t'13 (Vint (Int.repr (Z.b2z ((bar_of (le32 bs 28) <? 16) || (36 <? bar_of (le32 bs 28)))%bool))).
  { forward. entailer!. repr_facts Wr; bjoin. }
  { forward. forward. entailer!. repr_facts Wr; bjoin. }
  fif_t _t'14 (Vint (Int.repr (Z.b2z ((bar_of (le32 bs 28) <? 16) || (36 <? bar_of (le32 bs 28)) ||
                                       negb (bar_of (le32 bs 28) mod 4 =? 0))%bool))).
  { forward. entailer!. repr_facts Wr; bjoin. }
  { forward. forward. entailer!.
    rewrite ifeq_b2z by (apply land_u32; lia). rewrite land3 by lia. repr_facts Wr; bjoin. }
  forward_if.
  { assert (TK: target_ok bs = false)
      by (unfold target_ok; rewrite bar_ok_neg, H; cbn [negb]; rewrite andb_false_r; reflexivity).
    assert (D: decode bs = None) by dec_solve. hd_bad D. }
  rename H into BK.
  forward.
  fif_t _t'15 (Vint (Int.repr (Z.b2z ((le32 bs 24 =? 0) || (65536 <? le32 bs 24))%bool))).
  { forward. entailer!. repr_facts Wr; bjoin. }
  { forward. forward. entailer!. repr_facts Wr; bjoin. }
  fif_t _t'16 (Vint (Int.repr (Z.b2z ((le32 bs 24 =? 0) || (65536 <? le32 bs 24) ||
                                       negb (le32 bs 24 mod 512 =? 0))%bool))).
  { forward. entailer!. repr_facts Wr; bjoin. }
  { forward. forward. entailer!.
    rewrite ifeq_b2z by (apply land_u32; [ apply Wr | lia ]). rewrite land511 by (apply Wr). repr_facts Wr; bjoin. }
  fif_t _t'17 (Vint (Int.repr (Z.b2z ((le32 bs 24 =? 0) || (65536 <? le32 bs 24) ||
                                       negb (le32 bs 24 mod 512 =? 0) || negb (bdf_ok (le32 bs 16)))%bool))).
  { forward. entailer!. repr_facts Wr; bjoin. }
  { forward. entailer!.
    rewrite not_bdf_mask, and_repr, ifeq_b2z by (apply land_u32; [ apply Wr | unfold BDF_OUTSIDE; lia ]).
    unfold bdf_ok. repr_facts Wr; bjoin. }
  forward_if.
  { assert (TK: target_ok bs = false).
    { unfold target_ok. rewrite window_ok_neg. revert H.
      generalize (bdf_ok (le32 bs 16)) (bar_ok (bar_of (le32 bs 28)))
        ((le32 bs 24 =? 0) || (65536 <? le32 bs 24) || negb (le32 bs 24 mod 512 =? 0))%bool.
      intros b1 b2 b3 HH. destruct b1, b2, b3; cbn in *; congruence. }
    assert (D: decode bs = None) by dec_solve. hd_bad D. }
  rename H into WK.
  assert (TK: target_ok bs = true).
  { unfold target_ok. rewrite window_ok_neg, bar_ok_neg. revert BK WK.
    generalize (bdf_ok (le32 bs 16))
      ((bar_of (le32 bs 28) <? 16) || (36 <? bar_of (le32 bs 28)) || negb (bar_of (le32 bs 28) mod 4 =? 0))%bool
      ((le32 bs 24 =? 0) || (65536 <? le32 bs 24) || negb (le32 bs 24 mod 512 =? 0))%bool.
    intros b1 b2 b3 HB HW. destruct b1, b2, b3; cbn in *; congruence. }
  forward.
  apply semax_if_seq. forward_if.
  { assert (V3: le32 bs 4 = 3) by (repr_facts Wr; assumption).
    assert (L68: 68 <= Zlength bs) by (rewrite V3 in C2b; cbn in C2b; lia).
    eapply semax_pre; [ | apply (hd_v3 sh image bs tsh tp psh pp P0 hsh hp); first [ reflexivity | assumption | lia ] ].
    entailer!. }
  { assert (D: decode bs = Some (target_of bs, no_policy, 32)) by dec_solve.
    hd_ret.
    unfold header_post, header_status. rewrite D. rewrite pol_store_none by auto.
    split; [ repeat split; reflexivity | reflexivity ]. }
Qed.
