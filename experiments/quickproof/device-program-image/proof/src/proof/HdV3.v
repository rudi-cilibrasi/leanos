(* wifi_image_header's version-3 part: the flags and the policy's scalars, their checks, then the sink loop and
   the descriptor map (HdSinks). *)
Require Import VST.floyd.proofauto.
Require Import LeanosDeviceProgramImage.device_program.code.
Require Import LeanosDeviceProgramImage.proof.Specs.
Require Import LeanosDeviceProgramImage.proof.BodyLookup.
Require Import LeanosDeviceProgramImage.proof.BodyPolicy.
Require Import LeanosDeviceProgramImage.proof.BodyAdmit.
Require Import LeanosDeviceProgramImage.proof.HdDefs.
Require Import LeanosDeviceProgramImage.proof.HdArith.
Require Import LeanosDeviceProgramImage.proof.HdSinks.
#[local] Existing Instance Specs.CS.
Local Open Scope Z_scope.

Lemma hd_v3 {Espec: OracleKind} sh image bs tsh tp psh pp P0 hsh hp:
  readable_share sh -> writable_share tsh -> writable_share psh -> writable_share hsh ->
  image_ok bs -> policy_wf P0 ->
  field_compatible t_policy [] pp -> field_compatible (tarray tuchar (Zlength bs)) [] image ->
  le32 bs 0 = MAGIC -> le32 bs 4 = 3 -> 68 <= Zlength bs -> target_ok bs = true ->
  forall Delta R c, Delta = Delta_hd -> R = Post_hd sh image bs tsh tp psh pp P0 hsh hp -> c = Ssequence s_v3 ret0 ->
  semax Delta
    (PROP ()
     LOCAL (temp _image image; temp _image_len (Vint (Int.repr (Zlength bs))); temp _t tp; temp _pol pp;
            temp _header_len hp)
     SEP (data_at sh (tarray tuchar (Zlength bs)) (bytes_val bs) image;
          data_at tsh t_target (target_val (target_of bs)) tp;
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
          data_at hsh tuint (Vint (Int.repr 32)) hp))
    c R.
Proof.
  intros SH TSH PSH HSH IOK PW FCp FCi M0 V3 L68 TK Delta R c -> -> ->.
  unfold s_v3, Post_hd, Delta_hd. start_tail.
  pose proof IOK as (LB & U8).
  assert (W: forall k, u32_ok (le32 bs k)) by (intros; apply le32_range; auto).
  assert (Wr: forall k, 0 <= le32 bs k <= Int.max_unsigned) by (intros; apply W).
  assert (PI: isptr image) by (destruct FCi; auto).
  pose proof (Wr 24) as W24. pose proof (Wr 32) as W32. pose proof (Wr 36) as W36. pose proof (Wr 64) as W64.
  forward_call (sh, image, bs, 32).
  forward. forward.
  forward_call (sh, image, bs, 36). forward.
  forward_call (sh, image, bs, 40). forward_call (sh, image, bs, 44). forward.
  forward_call (sh, image, bs, 48). forward_call (sh, image, bs, 52). forward.
  forward_call (sh, image, bs, 56). forward.
  forward_call (sh, image, bs, 60). forward.
  rewrite and_repr, (cfg_val bs 40 44), (cfg_val bs 48 52) by (auto; lia).
  fif_t _t'26 (Vint (Int.repr (le32 bs 64))).
  { forward_call (sh, image, bs, 64). forward. entailer!. }
  { exfalso. repr_facts Wr. rewrite ?Int.unsigned_repr in H by rep_lia. lia. }
  forward.
  fif_t _t'28 (Vint (Int.repr (Z.b2z ((3 <? le32 bs 32) || (le32 bs 36 <? le32 bs 24))%bool))).
  { rewrite not_3, and_repr in H. change Int.zero with (Int.repr 0) in H.
    assert (R: Z.land (le32 bs 32) 4294967292 <> 0) by (intros E; apply H; rewrite E; reflexivity).
    assert (F3: 3 < le32 bs 32) by (destruct (Z.le_gt_cases (le32 bs 32) 3) as [Le | Gt]; auto;
                                    exfalso; apply R; apply flags_mask; auto).
    forward. entailer!. repr_facts Wr; bjoin. }
  { rewrite not_3, and_repr in H. change Int.zero with (Int.repr 0) in H.
    apply repr_inj_unsigned in H; [ | apply land_u32; [ apply Wr | lia ] | rep_lia ].
    assert (F3: le32 bs 32 <= 3) by (apply flags_mask; auto).
    forward. forward. forward. entailer!. change (tg_window (target_of bs)) with (le32 bs 24). repr_facts Wr; bjoin. }
  fif_t _t'29 (Vint (Int.repr (Z.b2z ((3 <? le32 bs 32) || (le32 bs 36 <? le32 bs 24) || (8 <? le32 bs 64))%bool))).
  { forward. entailer!. repr_facts Wr; bjoin. }
  { forward. forward. entailer!. repr_facts Wr; bjoin. }
  fif_t _t'30 (Vint (Int.repr (Z.b2z ((3 <? le32 bs 32) || (le32 bs 36 <? le32 bs 24) || (8 <? le32 bs 64) ||
                                       (Zlength bs <? 68 + 4 * le32 bs 64))%bool))).
  { forward. entailer!. repr_facts Wr; bjoin. }
  { pose proof H as H'. bprop.
    forward. forward. entailer!. rewrite ?mul_repr, ?add_repr. repr_facts Wr; bjoin. }
  forward_if.
  { assert (D: decode bs = None) by dec_solve. hd_bad D. }
  rename H into CK. bprop.
  eapply semax_pre; [ | apply (hd_sinks sh image bs tsh tp psh pp P0 hsh hp); first [ reflexivity | assumption | lia ] ].
  entailer!.
Qed.
