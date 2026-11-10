(* wifi_image_header's descriptor map: its count and length tests, then the descriptor loop (HdLoop). *)
Require Import VST.floyd.proofauto.
Require Import LeanosDeviceProgramImage.device_program.code.
Require Import LeanosDeviceProgramImage.proof.Specs.
Require Import LeanosDeviceProgramImage.proof.BodyLookup.
Require Import LeanosDeviceProgramImage.proof.BodyPolicy.
Require Import LeanosDeviceProgramImage.proof.BodyAdmit.
Require Import LeanosDeviceProgramImage.proof.HdDefs.
Require Import LeanosDeviceProgramImage.proof.HdArith.
Require Import LeanosDeviceProgramImage.proof.HdLoop.
#[local] Existing Instance Specs.CS.
Local Open Scope Z_scope.

Lemma hd_descs {Espec: OracleKind} sh image bs tsh tp psh pp P0 hsh hp:
  readable_share sh -> writable_share tsh -> writable_share psh -> writable_share hsh ->
  image_ok bs -> policy_wf P0 ->
  field_compatible t_policy [] pp -> field_compatible (tarray tuchar (Zlength bs)) [] image ->
  le32 bs 0 = MAGIC -> le32 bs 4 = 3 -> 68 <= Zlength bs -> target_ok bs = true ->
  le32 bs 32 <= 3 -> le32 bs 24 <= le32 bs 36 -> le32 bs 64 <= 8 -> 68 + 4 * le32 bs 64 <= Zlength bs ->
  Z.land (le32 bs 32) 2 <> 0 ->
  forall Delta R c, Delta = Delta_hd -> R = Post_hd sh image bs tsh tp psh pp P0 hsh hp -> c = Ssequence s_desc ret0 ->
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
          field_at psh t_policy (DOT _sinks)
            (words_val (sinks_at bs (le32 bs 64) ++ sublist (le32 bs 64) 8 (pl_sinks P0))) pp;
          field_at psh t_policy (DOT _desc_count) (Vint (Int.repr 0)) pp;
          data_at psh (tarray t_desc 16) (map desc_val (pl_descs P0)) (offset_val 80 pp);
          data_at hsh tuint (Vint (Int.repr (68 + 4 * le32 bs 64))) hp))
    c R.
Proof.
  intros SH TSH PSH HSH IOK PW FCp FCi M0 V3 L68 TK F3 WW S8 LS F2 Delta R c -> -> ->.
  unfold s_desc, ret0, Post_hd, Delta_hd. start_tail.
  pose proof IOK as (LB & U8).
  assert (W: forall k, u32_ok (le32 bs k)) by (intros; apply le32_range; auto).
  assert (Wr: forall k, 0 <= le32 bs k <= Int.max_unsigned) by (intros; apply W).
  assert (PI: isptr image) by (destruct FCi; auto).
  pose proof (Wr 32) as W32. pose proof (Wr 64) as W64.
  set (A := 68 + 4 * le32 bs 64) in *.
  pose proof (Wr A) as WA.
  forward.
  forward_if.
  { rewrite ?add_repr in H. rewrite ?Int.unsigned_repr in H by rep_lia.
    assert (D: decode bs = None) by (unfold A in *; dec_solve). hd_bad D. }
  rename H into LA. rewrite ?add_repr in LA. rewrite ?Int.unsigned_repr in LA by rep_lia.
  forward_call (sh, image, bs, A).
  forward.
  forward.
  fif_t _t'33 (Vint (Int.repr (Z.b2z ((16 <? le32 bs A) || (Zlength bs <? A + 4 + 16 * le32 bs A))%bool))).
  { forward. entailer!. repr_facts Wr; bjoin. }
  { forward. forward. entailer!. rewrite ?mul_repr, ?add_repr. repr_facts Wr; bjoin. }
  forward_if.
  { assert (D: decode bs = None) by (unfold A in *; dec_solve). hd_bad D. }
  rename H into CK. bprop.
  eapply semax_pre; [ | apply (hd_loop sh image bs tsh tp psh pp P0 hsh hp); first [ reflexivity | assumption | lia ] ].
  entailer!.
Qed.
