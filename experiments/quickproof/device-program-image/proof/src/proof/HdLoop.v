(* wifi_image_header's descriptor loop: each descriptor written through d = &pol->descs[i] and checked
   (wifi_desc_limit), then the header length A + 4 + 16D and the version-3 return with the map. *)
Require Import VST.floyd.proofauto.
Require Import LeanosDeviceProgramImage.device_program.code.
Require Import LeanosDeviceProgramImage.proof.Specs.
Require Import LeanosDeviceProgramImage.proof.BodyLookup.
Require Import LeanosDeviceProgramImage.proof.BodyPolicy.
Require Import LeanosDeviceProgramImage.proof.BodyAdmit.
Require Import LeanosDeviceProgramImage.proof.HdDefs.
Require Import LeanosDeviceProgramImage.proof.HdArith.
#[local] Existing Instance Specs.CS.
Local Open Scope Z_scope.

Lemma hd_loop {Espec: OracleKind} sh image bs tsh tp psh pp P0 hsh hp:
  readable_share sh -> writable_share tsh -> writable_share psh -> writable_share hsh ->
  image_ok bs -> policy_wf P0 ->
  field_compatible t_policy [] pp -> field_compatible (tarray tuchar (Zlength bs)) [] image ->
  le32 bs 0 = MAGIC -> le32 bs 4 = 3 -> 68 <= Zlength bs -> target_ok bs = true ->
  le32 bs 32 <= 3 -> le32 bs 24 <= le32 bs 36 -> le32 bs 64 <= 8 -> 68 + 4 * le32 bs 64 <= Zlength bs ->
  Z.land (le32 bs 32) 2 <> 0 ->
  68 + 4 * le32 bs 64 + 4 <= Zlength bs -> le32 bs (68 + 4 * le32 bs 64) <= 16 ->
  68 + 4 * le32 bs 64 + 4 + 16 * le32 bs (68 + 4 * le32 bs 64) <= Zlength bs ->
  forall Delta R c, Delta = Delta_hd -> R = Post_hd sh image bs tsh tp psh pp P0 hsh hp -> c = Ssequence s_dloop ret0 ->
  semax Delta
    (PROP ()
     LOCAL (temp _at (Vint (Int.repr (68 + 4 * le32 bs 64)));
            temp _flags (Vint (Int.repr (le32 bs 32))); temp _image image;
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
          field_at psh t_policy (DOT _desc_count) (Vint (Int.repr (le32 bs (68 + 4 * le32 bs 64)))) pp;
          data_at psh (tarray t_desc 16) (map desc_val (pl_descs P0)) (offset_val 80 pp);
          data_at hsh tuint (Vint (Int.repr (68 + 4 * le32 bs 64))) hp))
    c R.
Proof.
  intros SH TSH PSH HSH IOK PW FCp FCi M0 V3 L68 TK F3 WW S8 LS F2 LA D16 LD Delta R c -> -> ->.
  unfold s_dloop, ret0, Post_hd, Delta_hd. start_tail.
  pose proof IOK as (LB & U8).
  assert (W: forall k, u32_ok (le32 bs k)) by (intros; apply le32_range; auto).
  assert (Wr: forall k, 0 <= le32 bs k <= Int.max_unsigned) by (intros; apply W).
  assert (PI: isptr image) by (destruct FCi; auto).
  pose proof (Wr 32) as W32. pose proof (Wr 64) as W64.
  pose proof PW as (_ & _ & _ & _ & _ & _ & _ & _ & Ls & _ & _ & Ld & _). unfold MAX_SINKS, MAX_DESCS in *.
  set (A := 68 + 4 * le32 bs 64) in *.
  pose proof (Wr A) as WA.
  assert (AR: 68 <= A <= 100) by (unfold A; lia).
  assert (FCd: field_compatible (tarray t_desc 16) [] (offset_val 80 pp)) by (apply descs_compatible; auto).
  forward.
  forward_loop (EX i: Z,
      PROP (0 <= i <= le32 bs A; forallb desc_ok (descs_at bs A i) = true)
      LOCAL (temp _i__1 (Vint (Int.repr i)); temp _at (Vint (Int.repr A)); temp _flags (Vint (Int.repr (le32 bs 32))); temp _image image;
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
          field_at psh t_policy (DOT _desc_count) (Vint (Int.repr (le32 bs A))) pp;
          data_at psh (tarray t_desc 16) (map desc_val (descs_at bs A i ++ sublist i 16 (pl_descs P0)))
            (offset_val 80 pp);
          data_at hsh tuint (Vint (Int.repr A)) hp))%assert
    break: (PROP (forallb desc_ok (descs_at bs A (le32 bs A)) = true)
      LOCAL (temp _at (Vint (Int.repr A)); temp _flags (Vint (Int.repr (le32 bs 32))); temp _image image;
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
          field_at psh t_policy (DOT _desc_count) (Vint (Int.repr (le32 bs A))) pp;
          data_at psh (tarray t_desc 16) (map desc_val (descs_at bs A (le32 bs A) ++ sublist (le32 bs A) 16 (pl_descs P0)))
            (offset_val 80 pp);
          data_at hsh tuint (Vint (Int.repr A)) hp)).
  { Exists 0. change (descs_at bs A 0) with (@nil desc). rewrite app_nil_l, (sublist_same 0 16 (pl_descs P0)) by lia. entailer!. }
  { Intros i. rename H into I, H0 into OK.
    forward.
    forward_if; [ | forward; assert (i = le32 bs A) by lia; subst i; entailer! ].
    rename H into Lt.
    forward. forward.
    assert (PP: isptr pp) by (destruct FCp; auto).
    match goal with |- context [temp _d ?v] =>
      assert (Ed: v = offset_val (16 * i) (offset_val 80 pp)) end.
    { destruct pp; try contradiction. simpl. f_equal. f_equal.
      unfold Ptrofs.of_intu, Ptrofs.of_int. rewrite Int.unsigned_repr by rep_lia. apply ptrofs_mul_repr. }
    match goal with |- context [temp _e ?v] =>
      assert (Ee: v = offset_val (A + 4 + 16 * i) image) end.
    { destruct image; try contradiction. simpl. f_equal.
      unfold Ptrofs.of_intu, Ptrofs.of_ints, Ptrofs.of_int. rewrite mul_repr.
      rewrite !Int.unsigned_repr by rep_lia. rewrite Int.signed_repr by rep_lia.
      rewrite !ptrofs_mul_repr, !Ptrofs.add_assoc, !ptrofs_add_repr. f_equal. f_equal. lia. }
    rewrite Ed, Ee. clear Ed Ee.
    set (L := map desc_val (descs_at bs A i ++ sublist i 16 (pl_descs P0))).
    assert (LL: Zlength L = 16) by (unfold L; rewrite Zlength_map, Zlength_app, Zlength_descs_at, Zlength_sublist; lia).
    rewrite (descs_split psh L i (offset_val 80 pp)) by (auto; lia). Intros.
    sep_apply (data_at_data_at_ psh t_desc (Znth i L) (offset_val (16 * i) (offset_val 80 pp))).
    rewrite data_at__eq.
    set (e := A + 4 + 16 * i).
    assert (Le: e + 16 <= Zlength bs) by (unfold e; lia).
    forward_call (sh, image, bs, e). forward.
    forward_call (sh, image, bs, e + 4). forward.
    forward_call (sh, image, bs, e + 8). forward.
    forward_call (sh, image, bs, e + 12). forward.
    set (de := desc_at bs e).
    pose proof (Wr e) as We. pose proof (Wr (e + 8)) as We8.
    assert (TR: ds_trb de = le32 bs e) by reflexivity.
    assert (CN: ds_count de = le32 bs (e + 8)) by reflexivity.
    assert (DW: desc_wf de) by (unfold de, desc_wf, desc_at; cbn [ds_trb ds_start ds_count ds_stride]; repeat split; apply W).
    forward.
    fif_t _t'38 (Vint (Int.repr (Z.b2z ((1 <? le32 bs e) || (le32 bs (e + 8) <? 1))%bool))).
    { forward. entailer!. repr_facts Wr; bjoin. }
    { forward. forward. entailer!. repr_facts Wr; bjoin. }
    fif_t _t'39 (Vint (Int.repr (Z.b2z ((1 <? le32 bs e) || (le32 bs (e + 8) <? 1) ||
                                         (4096 <? le32 bs (e + 8)))%bool))).
    { forward. entailer!. repr_facts Wr; bjoin. }
    { forward. forward. entailer!. repr_facts Wr; bjoin. }
    change (data_at psh t_desc _ (offset_val (16 * i) (offset_val 80 pp)))
      with (data_at psh t_desc (desc_val de) (offset_val (16 * i) (offset_val 80 pp))).
    fif_t _t'40 (Vint (Int.repr (Z.b2z ((1 <? le32 bs e) || (le32 bs (e + 8) <? 1) ||
                                         (4096 <? le32 bs (e + 8)) || (SCRATCH <? desc_limit de))%bool))).
    { forward. entailer!. repr_facts Wr; bjoin. }
    { pose proof H as H'. bprop.
      forward_call (psh, offset_val (16 * i) (offset_val 80 pp), de).
      pose proof (desc_limit_range de DW ltac:(rewrite CN; lia)) as DR.
      forward. entailer!. unfold Int64.cmpu. rewrite ltu64_b2z by rep_lia. unfold SCRATCH. repr_facts Wr; bjoin. }
    forward_if.
    { assert (DK: desc_ok de = false) by (rewrite desc_ok_neg, TR, CN, H; reflexivity).
      assert (NF: forallb desc_ok (descs_at bs A (le32 bs A)) = false).
      { rewrite <- (sublist_same 0 (le32 bs A) (descs_at bs A (le32 bs A))) by (try rewrite Zlength_descs_at; lia).
        apply (forallb_miss _ _ i); [ lia | rewrite Zlength_descs_at; lia | rewrite Znth_descs_at by lia; exact DK ]. }
      sep_apply (descs_join psh L i (desc_val de) (offset_val 80 pp) ltac:(lia) LL FCd).
      assert (D: decode bs = None) by (unfold A in *; dec_solve). hd_bad D. }
    assert (DK: desc_ok de = true) by (rewrite desc_ok_neg, TR, CN, H; reflexivity).
    sep_apply (descs_join psh L i (desc_val de) (offset_val 80 pp) ltac:(lia) LL FCd).
    forward.
    Exists (i + 1). entailer!.
    - rewrite descs_at_snoc, forallb_app by lia. rewrite OK. cbn. rewrite andb_true_r. exact DK.
    - try unfold de; try unfold e; try unfold L. rewrite descs_step by lia. apply derives_refl. }
  Intros. rename H into OKD.
  forward. forward.
  rewrite ?mul_repr, ?add_repr.
  assert (D: decode bs = Some (target_of bs, v3_policy bs (le32 bs 64) (le32 bs A) (descs_at bs A (le32 bs A)),
                               A + 4 + 16 * le32 bs A)) by (unfold A in *; dec_solve).
  hd_ret.
  unfold header_post, header_status. rewrite D. rewrite pol_store_v3d by (auto; lia).
  split; [ repeat split; reflexivity | reflexivity ].
Qed.