(* wifi_image_header's sink loop, the header length 68 + 4S, then the version-3 return without a descriptor
   map or the descriptor map (HdDescs). *)
Require Import VST.floyd.proofauto.
Require Import LeanosDeviceProgramImage.device_program.code.
Require Import LeanosDeviceProgramImage.proof.Specs.
Require Import LeanosDeviceProgramImage.proof.BodyLookup.
Require Import LeanosDeviceProgramImage.proof.BodyPolicy.
Require Import LeanosDeviceProgramImage.proof.BodyAdmit.
Require Import LeanosDeviceProgramImage.proof.HdDefs.
Require Import LeanosDeviceProgramImage.proof.HdArith.
Require Import LeanosDeviceProgramImage.proof.HdDescs.
#[local] Existing Instance Specs.CS.
Local Open Scope Z_scope.

Lemma hd_sinks {Espec: OracleKind} sh image bs tsh tp psh pp P0 hsh hp:
  readable_share sh -> writable_share tsh -> writable_share psh -> writable_share hsh ->
  image_ok bs -> policy_wf P0 ->
  field_compatible t_policy [] pp -> field_compatible (tarray tuchar (Zlength bs)) [] image ->
  le32 bs 0 = MAGIC -> le32 bs 4 = 3 -> 68 <= Zlength bs -> target_ok bs = true ->
  le32 bs 32 <= 3 -> le32 bs 24 <= le32 bs 36 -> le32 bs 64 <= 8 -> 68 + 4 * le32 bs 64 <= Zlength bs ->
  forall Delta R c, Delta = Delta_hd -> R = Post_hd sh image bs tsh tp psh pp P0 hsh hp -> c = Ssequence s_sinks ret0 ->
  semax Delta
    (PROP ()
     LOCAL (temp _flags (Vint (Int.repr (le32 bs 32))); temp _image image;
            temp _image_len (Vint (Int.repr (Zlength bs))); temp _t tp; temp _pol pp; temp _header_len hp)
     SEP (data_at sh (tarray tuchar (Zlength bs)) (bytes_val bs) image;
          data_at tsh t_target (target_val (target_of bs)) tp;
          field_at psh t_policy (DOT _present) (Vint (Int.repr 1)) pp;
          field_at psh t_policy (DOT _dma) (Vint (Int.repr (Z.land (le32 bs 32) 1))) pp;
          field_at psh t_policy (DOT _window) (Vint (Int.repr (le32 bs 36))) pp;
          spacer psh 12 16 pp;
          field_at psh t_policy (DOT _cfg_read) (Vlong (Int64.repr (le64 bs 40))) pp;
          field_at psh t_policy (DOT _cfg_write) (Vlong (Int64.repr (le64 bs 48))) pp;
          field_at psh t_policy (DOT _cmd_clear) (Vint (Int.repr (le32 bs 56))) pp;
          field_at psh t_policy (DOT _cmd_set) (Vint (Int.repr (le32 bs 60))) pp;
          field_at psh t_policy (DOT _sink_count) (Vint (Int.repr (le32 bs 64))) pp;
          field_at psh t_policy (DOT _sinks) (words_val (pl_sinks P0)) pp;
          field_at psh t_policy (DOT _desc_count) (Vint (Int.repr 0)) pp;
          data_at psh (tarray t_desc 16) (map desc_val (pl_descs P0)) (offset_val 80 pp);
          data_at hsh tuint (Vint (Int.repr 32)) hp))
    c R.
Proof.
  intros SH TSH PSH HSH IOK PW FCp FCi M0 V3 L68 TK F3 WW S8 LS Delta R c -> -> ->.
  unfold s_sinks, ret0, Post_hd, Delta_hd. start_tail.
  pose proof IOK as (LB & U8).
  assert (W: forall k, u32_ok (le32 bs k)) by (intros; apply le32_range; auto).
  assert (Wr: forall k, 0 <= le32 bs k <= Int.max_unsigned) by (intros; apply W).
  assert (PI: isptr image) by (destruct FCi; auto).
  pose proof (Wr 32) as W32. pose proof (Wr 64) as W64.
  pose proof PW as (_ & _ & _ & _ & _ & _ & _ & _ & Ls & _ & _ & Ld & _). unfold MAX_SINKS, MAX_DESCS in *.
  forward.
  forward_loop (EX i: Z,
      PROP (0 <= i <= le32 bs 64)
      LOCAL (temp _i (Vint (Int.repr i)); temp _flags (Vint (Int.repr (le32 bs 32))); temp _image image;
             temp _image_len (Vint (Int.repr (Zlength bs))); temp _t tp; temp _pol pp; temp _header_len hp)
      SEP (data_at sh (tarray tuchar (Zlength bs)) (bytes_val bs) image;
          data_at tsh t_target (target_val (target_of bs)) tp;
          field_at psh t_policy (DOT _present) (Vint (Int.repr 1)) pp;
          field_at psh t_policy (DOT _dma) (Vint (Int.repr (Z.land (le32 bs 32) 1))) pp;
          field_at psh t_policy (DOT _window) (Vint (Int.repr (le32 bs 36))) pp;
          spacer psh 12 16 pp;
          field_at psh t_policy (DOT _cfg_read) (Vlong (Int64.repr (le64 bs 40))) pp;
          field_at psh t_policy (DOT _cfg_write) (Vlong (Int64.repr (le64 bs 48))) pp;
          field_at psh t_policy (DOT _cmd_clear) (Vint (Int.repr (le32 bs 56))) pp;
          field_at psh t_policy (DOT _cmd_set) (Vint (Int.repr (le32 bs 60))) pp;
          field_at psh t_policy (DOT _sink_count) (Vint (Int.repr (le32 bs 64))) pp;
          field_at psh t_policy (DOT _sinks) (words_val (sinks_at bs i ++ sublist i 8 (pl_sinks P0))) pp;
          field_at psh t_policy (DOT _desc_count) (Vint (Int.repr 0)) pp;
          data_at psh (tarray t_desc 16) (map desc_val (pl_descs P0)) (offset_val 80 pp);
          data_at hsh tuint (Vint (Int.repr 32)) hp))%assert
    break: (PROP ()
      LOCAL (temp _flags (Vint (Int.repr (le32 bs 32))); temp _image image;
             temp _image_len (Vint (Int.repr (Zlength bs))); temp _t tp; temp _pol pp; temp _header_len hp)
      SEP (data_at sh (tarray tuchar (Zlength bs)) (bytes_val bs) image;
          data_at tsh t_target (target_val (target_of bs)) tp;
          field_at psh t_policy (DOT _present) (Vint (Int.repr 1)) pp;
          field_at psh t_policy (DOT _dma) (Vint (Int.repr (Z.land (le32 bs 32) 1))) pp;
          field_at psh t_policy (DOT _window) (Vint (Int.repr (le32 bs 36))) pp;
          spacer psh 12 16 pp;
          field_at psh t_policy (DOT _cfg_read) (Vlong (Int64.repr (le64 bs 40))) pp;
          field_at psh t_policy (DOT _cfg_write) (Vlong (Int64.repr (le64 bs 48))) pp;
          field_at psh t_policy (DOT _cmd_clear) (Vint (Int.repr (le32 bs 56))) pp;
          field_at psh t_policy (DOT _cmd_set) (Vint (Int.repr (le32 bs 60))) pp;
          field_at psh t_policy (DOT _sink_count) (Vint (Int.repr (le32 bs 64))) pp;
          field_at psh t_policy (DOT _sinks)
            (words_val (sinks_at bs (le32 bs 64) ++ sublist (le32 bs 64) 8 (pl_sinks P0))) pp;
          field_at psh t_policy (DOT _desc_count) (Vint (Int.repr 0)) pp;
          data_at psh (tarray t_desc 16) (map desc_val (pl_descs P0)) (offset_val 80 pp);
          data_at hsh tuint (Vint (Int.repr 32)) hp)).
  { Exists 0. change (sinks_at bs 0) with (@nil Z). rewrite app_nil_l, sublist_same by lia. entailer!. }
  { Intros i. rename H into I.
    forward.
    forward_if; [ | forward; assert (i = le32 bs 64) by lia; subst i; entailer! ].
    rename H into Lt.
    forward_call (sh, image, bs, 68 + 4 * i).
    forward. forward.
    Exists (i + 1). entailer!. rewrite sinks_step by lia. apply derives_refl. }
  forward. forward.
  rewrite mul_repr, add_repr.
  apply semax_if_seq. forward_if.
  { rewrite and_repr in H. change Int.zero with (Int.repr 0) in H.
    assert (F2: Z.land (le32 bs 32) 2 <> 0) by (intros E; apply H; rewrite E; reflexivity).
    eapply semax_pre; [ | apply (hd_descs sh image bs tsh tp psh pp P0 hsh hp); first [ reflexivity | assumption | lia ] ].
    entailer!. }
  { rewrite and_repr in H. change Int.zero with (Int.repr 0) in H.
    apply repr_inj_unsigned in H; [ | apply land_u32; [ apply Wr | lia ] | rep_lia ].
    assert (D: decode bs = Some (target_of bs, v3_policy bs (le32 bs 64) 0 nil, 68 + 4 * le32 bs 64))
      by dec_solve.
    hd_ret.
    unfold header_post, header_status. rewrite D. rewrite pol_store_v3 by (auto; lia).
    split; [ repeat split; reflexivity | reflexivity ]. }
Qed.
