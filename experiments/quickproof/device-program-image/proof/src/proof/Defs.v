(* The pure model of hardware/wifi/wifi-exec.h (through the wrapper unit patch/device_program_unit.c) and of the
   law harness/image_exact.c.  No program, no separation logic here.

   One model serves both sides: the C bodies (wifi_le32, wifi_image_header, wifi_start, the admission functions)
   and the law's own reference functions (word_at, read_image, declares_sink, declares_desc, within and the
   inline comparisons of admission_case) compute the same values, so each side is proved against this file and
   the law's checks reduce to equalities of model terms.

   Values are Z.  A uint32_t field is a Z in [0, 2^32), a uint64_t field a Z in [0, 2^64); the well-formedness
   predicates at the end state the ranges.  An image is its list of bytes (Z in [0, 256)), as nondet_bytes
   writes it.

   The model follows the law's first comment clause by clause:
   - le32 bs k          word@k, bytes k..k+3, little-endian;
   - decode bs          the header: None for BAD, or Some (target, policy, header length).  The policy carries
                        exactly its declared sinks (sink count entries) and descriptors (descriptor count
                        entries); `store` lays it over the prior policy object, whose entries past the counts
                        are kept;
   - start bs           wifi_start's verdict: decode, then N = word@8 and B = word@12 must fit;
   - within/service/source   the admission subset tests, as booleans.

   Dead branch of the C.  wifi_image_header reads the sink count as `image_len >= 68 ? word@64 : 0xffffffff`;
   in version 3 the image has already been required to have 68 bytes, so the model reads word@64.  The
   descriptor limit start + stride * (count - 1) + size is computed in 64 bits by the C after count >= 1 was
   checked, so it neither wraps nor underflows: the model computes it in Z.  The law's read_image takes the
   bus as bdf >> 16 where the C takes (bdf >> 16) & 0xff; they agree once bdf_ok holds, which decode requires
   before it returns a target (a phase-2 lemma, src/proof/NOTES.md). *)
Require Import VST.floyd.proofauto.
Local Open Scope Z_scope.
Local Open Scope bool_scope.   (* && and || are andb and orb here *)

(* ---------------------------------------------------------------------- *)
(* Constants of wifi-exec.h.                                              *)
(* ---------------------------------------------------------------------- *)

Definition MAGIC : Z := 1179211596.          (* WIFI_MAGIC 0x4649574c, "LWIF" *)
Definition BAD : Z := 2.                     (* WIFI_BAD_IMAGE *)
Definition SCRATCH : Z := 262144.            (* WIFI_SCRATCH_BYTES *)
Definition MAX_SINKS : Z := 8.               (* WIFI_MAX_SINKS *)
Definition MAX_DESCS : Z := 16.              (* WIFI_MAX_DESCS *)
Definition STACK_DEPTH : Z := 16.            (* WIFI_STACK_DEPTH *)
Definition BCM_ID : Z := 1129518308.         (* 0x435314e4 *)
Definition BDF_OUTSIDE : Z := 4278247672.    (* ~0xff1f07 in 32 bits = 0xff00e0f8: the bits outside bus, dev, fn *)

(* ---------------------------------------------------------------------- *)
(* The records: struct wifi_target, struct wifi_desc, struct wifi_policy. *)
(* ---------------------------------------------------------------------- *)

Record target : Type := mk_target {
  tg_bus: Z; tg_dev: Z; tg_fn: Z; tg_id: Z; tg_window: Z; tg_bar: Z }.

Record desc : Type := mk_desc {
  ds_trb: Z; ds_start: Z; ds_count: Z; ds_stride: Z }.

(* A policy: its scalar fields and its two arrays.  The arrays of a policy object in memory have 8 and 16
   entries (policy_wf); a decoded policy (decode) has exactly pl_sink_count and pl_desc_count entries. *)
Record policy : Type := mk_policy {
  pl_present: Z; pl_dma: Z; pl_window: Z;
  pl_cfg_read: Z; pl_cfg_write: Z;
  pl_cmd_clear: Z; pl_cmd_set: Z;
  pl_sink_count: Z; pl_sinks: list Z;
  pl_desc_count: Z; pl_descs: list desc }.

#[export] Instance Inhabitant_desc : Inhabitant desc := mk_desc 0 0 0 0.

(* The decoded policy laid over the prior policy object P0: the scalars and the first count entries of each
   array are the decoded ones, the entries past the counts are P0's. *)
Definition store (P P0: policy) : policy :=
  mk_policy (pl_present P) (pl_dma P) (pl_window P) (pl_cfg_read P) (pl_cfg_write P)
    (pl_cmd_clear P) (pl_cmd_set P)
    (pl_sink_count P) (pl_sinks P ++ sublist (pl_sink_count P) MAX_SINKS (pl_sinks P0))
    (pl_desc_count P) (pl_descs P ++ sublist (pl_desc_count P) MAX_DESCS (pl_descs P0)).

(* ---------------------------------------------------------------------- *)
(* Words of an image.                                                     *)
(* ---------------------------------------------------------------------- *)

(* word@k: bytes k..k+3, little-endian. *)
Definition le32 (bs: list Z) (k: Z) : Z :=
  Znth k bs + Znth (k + 1) bs * 256 + Znth (k + 2) bs * 65536 + Znth (k + 3) bs * 16777216.

(* A 64-bit bitmap from its low word at k and its high word at k + 4. *)
Definition le64 (bs: list Z) (k: Z) : Z := le32 bs k + le32 bs (k + 4) * 4294967296.

(* ---------------------------------------------------------------------- *)
(* The header (wifi_image_header; the law's read_image).                  *)
(* ---------------------------------------------------------------------- *)

(* The version-1 target: the BCM43224 at 2:0.0, window 0x4000, BAR offset 0x10. *)
Definition bcm_target : target := mk_target 2 0 0 BCM_ID 16384 16.

(* An absent policy: every scalar 0, no entry. *)
Definition no_policy : policy := mk_policy 0 0 0 0 0 0 0 0 nil 0 nil.

(* The BAR offset field word@28: 0x10 when it is 0. *)
Definition bar_of (w: Z) : Z := if w =? 0 then 16 else w.

(* Checks of a version-2/3 target. *)
Definition bdf_ok (bdf: Z) : bool := Z.land bdf BDF_OUTSIDE =? 0.
Definition bar_ok (bar: Z) : bool := (16 <=? bar) && (bar <=? 36) && (bar mod 4 =? 0).
Definition window_ok (w: Z) : bool := negb (w =? 0) && (w <=? 65536) && (w mod 512 =? 0).

Definition target_ok (bs: list Z) : bool :=
  bdf_ok (le32 bs 16) && bar_ok (bar_of (le32 bs 28)) && window_ok (le32 bs 24).

(* The target a version-2/3 image names: bus (bdf >> 16) & 0xff, device (bdf >> 8) & 0x1f, function bdf & 7,
   identity word@20, window word@24, BAR offset bar_of word@28. *)
Definition target_of (bs: list Z) : target :=
  let bdf := le32 bs 16 in
  mk_target (Z.land (Z.shiftr bdf 16) 255) (Z.land (Z.shiftr bdf 8) 31) (Z.land bdf 7)
    (le32 bs 20) (le32 bs 24) (bar_of (le32 bs 28)).

(* Descriptors. *)
Definition desc_at (bs: list Z) (e: Z) : desc :=
  mk_desc (le32 bs e) (le32 bs (e + 4)) (le32 bs (e + 8)) (le32 bs (e + 12)).

Definition desc_size (d: desc) : Z := if ds_trb d =? 0 then 8 else 16.

(* Descriptor.limit, one past the region's last byte (for count >= 1). *)
Definition desc_limit (d: desc) : Z := ds_start d + ds_stride d * (ds_count d - 1) + desc_size d.

Definition desc_ok (d: desc) : bool :=
  (ds_trb d <=? 1) && (1 <=? ds_count d) && (ds_count d <=? 4096) && (desc_limit d <=? SCRATCH).

(* The S sinks word@68, word@72, ... and the D descriptors at A + 4, A + 20, ... *)
Definition sinks_at (bs: list Z) (S: Z) : list Z :=
  map (fun i => le32 bs (68 + 4 * i)) (upto (Z.to_nat S)).
Definition descs_at (bs: list Z) (A D: Z) : list desc :=
  map (fun i => desc_at bs (A + 4 + 16 * i)) (upto (Z.to_nat D)).

(* A version-3 policy with S sinks and the descriptors ds (count D). *)
Definition v3_policy (bs: list Z) (S D: Z) (ds: list desc) : policy :=
  mk_policy 1 (Z.land (le32 bs 32) 1) (le32 bs 36) (le64 bs 40) (le64 bs 48) (le32 bs 56) (le32 bs 60)
    S (sinks_at bs S) D ds.

(* The header: None for BAD; else the target, the policy (its declared entries only) and the header length. *)
Definition decode (bs: list Z) : option (target * policy * Z) :=
  let len := Zlength bs in
  if (len <? 16) || negb (le32 bs 0 =? MAGIC) then None else
  let version := le32 bs 4 in
  if version =? 1 then Some (bcm_target, no_policy, 16) else
  if negb ((version =? 2) || (version =? 3)) then None else
  if len <? (if version =? 3 then 68 else 32) then None else
  if negb (target_ok bs) then None else
  let T := target_of bs in
  if version =? 2 then Some (T, no_policy, 32) else
  let flags := le32 bs 32 in
  let S := le32 bs 64 in
  if (3 <? flags) || (le32 bs 36 <? tg_window T) || (MAX_SINKS <? S) || (len <? 68 + 4 * S) then None else
  if Z.land flags 2 =? 0 then Some (T, v3_policy bs S 0 nil, 68 + 4 * S) else
  let A := 68 + 4 * S in
  if len <? A + 4 then None else
  let D := le32 bs A in
  if (MAX_DESCS <? D) || (len <? A + 4 + 16 * D) then None else
  let ds := descs_at bs A D in
  if negb (forallb desc_ok ds) then None else
  Some (T, v3_policy bs S D ds, A + 4 + 16 * D).

Definition header_status (bs: list Z) : Z := match decode bs with Some _ => 0 | None => BAD end.

(* ---------------------------------------------------------------------- *)
(* wifi_start.                                                            *)
(* ---------------------------------------------------------------------- *)

(* The instruction count N = word@8 and blob length B = word@12 fit the image after the header H. *)
Definition sizes_ok (bs: list Z) (H: Z) : bool :=
  let len := Zlength bs in
  (le32 bs 8 <=? (len - H) / 16) && (le32 bs 12 =? len - H - 16 * le32 bs 8).

(* None for BAD; else target, policy, header length H, N and B. *)
Definition start (bs: list Z) : option (target * policy * Z * Z * Z) :=
  match decode bs with
  | Some (T, P, H) => if sizes_ok bs H then Some (T, P, H, le32 bs 8, le32 bs 12) else None
  | None => None
  end.

Definition start_status (bs: list Z) : Z := match start bs with Some _ => 0 | None => BAD end.

(* struct wifi_vm as wifi_start leaves it: the code and blob pointers (vals), the scalars, the policy object,
   the target, the registers and stack (16 words each), sp, pc and the 64-bit step count. *)
Record vmstate : Type := mk_vm {
  vm_code: val; vm_blob: val; vm_n: Z; vm_blob_len: Z; vm_window: Z;
  vm_pol: policy; vm_target: target;
  vm_r: list Z; vm_stack: list Z; vm_sp: Z; vm_pc: Z; vm_steps: Z }.

(* The state after a successful wifi_start from the prior state V0 (start bs = Some (T, P, H, N, B)): the
   header's target and policy (laid over V0's policy object), the target's window, N, B, the code at image + H
   and the blob at image + H + 16N, registers, sp, pc and steps 0, V0's stack. *)
Definition started (image: val) (V0: vmstate) (T: target) (P: policy) (H N B: Z) : vmstate :=
  mk_vm (offset_val H image) (offset_val (H + 16 * N) image) N B (tg_window T) (store P (vm_pol V0)) T
    (Zrepeat 0 16) (vm_stack V0) 0 0 0.

(* ---------------------------------------------------------------------- *)
(* The admission (wifi_policy_within, wifi_service_admitted,              *)
(* wifi_source_admitted; the law's within and admission_case).            *)
(* ---------------------------------------------------------------------- *)

(* x has no bit outside y, as the C and the law compute it: (x & ~y) == 0 in 32 and in 64 bits. *)
Definition bits_in32 (x y: Z) : bool := Int.eq (Int.and (Int.repr x) (Int.not (Int.repr y))) Int.zero.
Definition bits_in64 (x y: Z) : bool :=
  Int64.eq (Int64.and (Int64.repr x) (Int64.not (Int64.repr y))) Int64.zero.

Definition desc_eqb (a b: desc) : bool :=
  (ds_trb a =? ds_trb b) && (ds_start a =? ds_start b) && (ds_count a =? ds_count b) &&
  (ds_stride a =? ds_stride b).

Definition target_eqb (a b: target) : bool :=
  (tg_bus a =? tg_bus b) && (tg_dev a =? tg_dev b) && (tg_fn a =? tg_fn b) && (tg_id a =? tg_id b) &&
  (tg_window a =? tg_window b) && (tg_bar a =? tg_bar b).

(* The declared entries of a policy object: the first count entries. *)
Definition declared_sinks (P: policy) : list Z := sublist 0 (pl_sink_count P) (pl_sinks P).
Definition declared_descs (P: policy) : list desc := sublist 0 (pl_desc_count P) (pl_descs P).

(* wifi_is_sink and the law's declares_sink; wifi_has_desc and declares_desc. *)
Definition is_sink (P: policy) (off: Z) : bool := existsb (Z.eqb off) (declared_sinks P).
Definition has_desc (P: policy) (d: desc) : bool := existsb (desc_eqb d) (declared_descs P).

(* Within(p, max) of the law comment. *)
Definition within (P M: policy) : bool :=
  forallb (is_sink P) (declared_sinks M) && forallb (has_desc P) (declared_descs M) &&
  (pl_window P <=? pl_window M) && (pl_dma P <=? pl_dma M) &&
  bits_in64 (pl_cfg_read P) (pl_cfg_read M) && bits_in64 (pl_cfg_write P) (pl_cfg_write M) &&
  bits_in32 (pl_cmd_clear P) (pl_cmd_clear M) && bits_in32 (pl_cmd_set P) (pl_cmd_set M).

(* Service(t, p, want, max). *)
Definition service (T: target) (P: policy) (W: target) (M: policy) : bool :=
  target_eqb T W && negb (pl_present P =? 0) && within P M.

(* Source(t, p, max). *)
Definition source (T: target) (P: policy) (M: policy) : bool :=
  (tg_bus T =? 0) && (tg_dev T =? 0) && (tg_fn T =? 0) && (tg_id T =? 4294967295) &&
  (tg_window T =? pl_window M) &&
  negb (pl_present P =? 0) && (pl_sink_count P =? 0) && (pl_desc_count P =? 0) &&
  (pl_window P <=? pl_window M) && (pl_dma P =? 0) && (pl_cfg_read P =? 0) && (pl_cfg_write P =? 0) &&
  (pl_cmd_clear P =? 0) && (pl_cmd_set P =? 0).

(* ---------------------------------------------------------------------- *)
(* Ranges.                                                                *)
(* ---------------------------------------------------------------------- *)

Definition u8_ok (x: Z) : Prop := 0 <= x <= Byte.max_unsigned.
Definition u32_ok (x: Z) : Prop := 0 <= x <= Int.max_unsigned.
Definition u64_ok (x: Z) : Prop := 0 <= x <= Int64.max_unsigned.

(* An image: bytes, and a length that is a uint32_t. *)
Definition image_ok (bs: list Z) : Prop := Zlength bs <= Int.max_unsigned /\ Forall u8_ok bs.

Definition target_wf (T: target) : Prop :=
  u32_ok (tg_bus T) /\ u32_ok (tg_dev T) /\ u32_ok (tg_fn T) /\ u32_ok (tg_id T) /\ u32_ok (tg_window T) /\
  u32_ok (tg_bar T).

Definition desc_wf (d: desc) : Prop :=
  u32_ok (ds_trb d) /\ u32_ok (ds_start d) /\ u32_ok (ds_count d) /\ u32_ok (ds_stride d).

(* A policy object: fields in range, 8 sinks and 16 descriptors. *)
Definition policy_wf (P: policy) : Prop :=
  u32_ok (pl_present P) /\ u32_ok (pl_dma P) /\ u32_ok (pl_window P) /\
  u64_ok (pl_cfg_read P) /\ u64_ok (pl_cfg_write P) /\ u32_ok (pl_cmd_clear P) /\ u32_ok (pl_cmd_set P) /\
  u32_ok (pl_sink_count P) /\ Zlength (pl_sinks P) = MAX_SINKS /\ Forall u32_ok (pl_sinks P) /\
  u32_ok (pl_desc_count P) /\ Zlength (pl_descs P) = MAX_DESCS /\ Forall desc_wf (pl_descs P).

(* A decoded policy (the policy of decode): fields in range, exactly sink count sinks (at most 8) and
   descriptor count descriptors (at most 16). *)
Definition decoded_wf (P: policy) : Prop :=
  u32_ok (pl_present P) /\ u32_ok (pl_dma P) /\ u32_ok (pl_window P) /\
  u64_ok (pl_cfg_read P) /\ u64_ok (pl_cfg_write P) /\ u32_ok (pl_cmd_clear P) /\ u32_ok (pl_cmd_set P) /\
  0 <= pl_sink_count P <= MAX_SINKS /\ Zlength (pl_sinks P) = pl_sink_count P /\ Forall u32_ok (pl_sinks P) /\
  0 <= pl_desc_count P <= MAX_DESCS /\ Zlength (pl_descs P) = pl_desc_count P /\ Forall desc_wf (pl_descs P).

(* A prior executor state: fields in range, 16 registers and 16 stack entries.  The pointers are any values. *)
Definition vm_wf (V: vmstate) : Prop :=
  u32_ok (vm_n V) /\ u32_ok (vm_blob_len V) /\ u32_ok (vm_window V) /\ policy_wf (vm_pol V) /\
  target_wf (vm_target V) /\ Zlength (vm_r V) = 16 /\ Forall u32_ok (vm_r V) /\
  Zlength (vm_stack V) = STACK_DEPTH /\ Forall u32_ok (vm_stack V) /\
  u32_ok (vm_sp V) /\ u32_ok (vm_pc V) /\ u64_ok (vm_steps V).

(* A policy an admission function may read: at most 8 sinks and 16 descriptors. *)
Definition policy_bounded (P: policy) : Prop :=
  policy_wf P /\ pl_sink_count P <= MAX_SINKS /\ pl_desc_count P <= MAX_DESCS.

(* ---------------------------------------------------------------------- *)
(* Basic facts of the model.                                              *)
(* ---------------------------------------------------------------------- *)

Lemma Zlength_sinks_at: forall bs S, 0 <= S -> Zlength (sinks_at bs S) = S.
Proof. intros. unfold sinks_at. rewrite Zlength_map, Zlength_upto. lia. Qed.

Lemma Znth_sinks_at: forall bs S i, 0 <= i < S -> Znth i (sinks_at bs S) = le32 bs (68 + 4 * i).
Proof.
  intros. unfold sinks_at. rewrite Znth_map by (rewrite Zlength_upto; lia).
  rewrite Znth_upto by lia. reflexivity.
Qed.

Lemma Zlength_descs_at: forall bs A D, 0 <= D -> Zlength (descs_at bs A D) = D.
Proof. intros. unfold descs_at. rewrite Zlength_map, Zlength_upto. lia. Qed.

Lemma Znth_descs_at: forall bs A D i, 0 <= i < D -> Znth i (descs_at bs A D) = desc_at bs (A + 4 + 16 * i).
Proof.
  intros. unfold descs_at. rewrite Znth_map by (rewrite Zlength_upto; lia).
  rewrite Znth_upto by lia. reflexivity.
Qed.

Lemma le32_range: forall bs k, Forall u8_ok bs -> u32_ok (le32 bs k).
Proof.
  intros bs k F. unfold le32, u32_ok.
  assert (B: forall j, 0 <= Znth j bs <= 255).
  { intros j. destruct (zlt j 0) as [Lt|Ge].
    - assert (E: Znth j bs = 0) by (rewrite Znth_underflow by lia; reflexivity). lia.
    - destruct (zlt j (Zlength bs)) as [Lt'|Ge'].
      + assert (I: In (Znth j bs) bs) by (apply Znth_In; lia).
        rewrite Forall_forall in F. specialize (F _ I). unfold u8_ok in F. rep_lia.
      + assert (E: Znth j bs = 0) by (rewrite Znth_overflow by lia; reflexivity). lia. }
  pose proof (B k); pose proof (B (k + 1)); pose proof (B (k + 2)); pose proof (B (k + 3)). rep_lia.
Qed.

(* x | y << n for disjoint bit ranges is x + y * 2^n. *)
Lemma lor_shift_add: forall x y n, 0 <= n -> 0 <= x < 2 ^ n -> 0 <= y ->
  Z.lor x (y * 2 ^ n) = x + y * 2 ^ n.
Proof.
  intros x y n N X Y.
  assert (D: Z.land x (y * 2 ^ n) = 0).
  { apply Z.bits_inj'. intros m M. rewrite Z.land_spec, Z.bits_0.
    destruct (zlt m n) as [Lt|Ge].
    - rewrite <- Z.shiftl_mul_pow2 by lia. rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
    - destruct (Z.eq_dec x 0) as [->|NZ]; [ rewrite Z.bits_0; reflexivity | ].
      rewrite (Z.bits_above_log2 x m); [ reflexivity | lia | ].
      apply Z.log2_lt_pow2; [ lia | ].
      eapply Z.lt_le_trans; [ apply X | ]. apply Z.pow_le_mono_r; lia. }
  rewrite <- Z.lxor_lor by exact D. rewrite <- Z.add_nocarry_lxor by exact D. reflexivity.
Qed.

(* The C's and the law's evaluation of word@k: four zero-extended bytes, shifted and or-ed in 32 bits. *)
Lemma le32_or: forall b0 b1 b2 b3, u8_ok b0 -> u8_ok b1 -> u8_ok b2 -> u8_ok b3 ->
  Int.or (Int.or (Int.or (Int.repr b0) (Int.shl (Int.repr b1) (Int.repr 8)))
                 (Int.shl (Int.repr b2) (Int.repr 16)))
         (Int.shl (Int.repr b3) (Int.repr 24)) =
  Int.repr (b0 + b1 * 256 + b2 * 65536 + b3 * 16777216).
Proof.
  intros b0 b1 b2 b3 H0 H1 H2 H3. unfold u8_ok in *.
  assert (SH: forall b n, 0 <= b <= 255 -> 0 <= n <= 24 ->
            Int.shl (Int.repr b) (Int.repr n) = Int.repr (b * 2 ^ n)).
  { intros b n Hb Hn. rewrite Int.shl_mul_two_p. unfold Int.mul.
    rewrite (Int.unsigned_repr n) by rep_lia. rewrite two_p_correct.
    rewrite Int.unsigned_repr by rep_lia.
    rewrite Int.unsigned_repr; [ reflexivity | ].
    assert (2 ^ n <= 2 ^ 24) by (apply Z.pow_le_mono_r; lia).
    assert (0 < 2 ^ n) by (apply Z.pow_pos_nonneg; lia). rep_lia. }
  assert (OR: forall x y, 0 <= x <= Int.max_unsigned -> 0 <= y <= Int.max_unsigned ->
            Int.or (Int.repr x) (Int.repr y) = Int.repr (Z.lor x y)).
  { intros. unfold Int.or. rewrite !Int.unsigned_repr by lia. reflexivity. }
  rewrite (SH b1 8), (SH b2 16), (SH b3 24) by rep_lia.
  assert (P8: 2 ^ 8 = 256) by reflexivity. assert (P16: 2 ^ 16 = 65536) by reflexivity.
  assert (P24: 2 ^ 24 = 16777216) by reflexivity.
  rewrite OR by (rewrite ?P8, ?P16, ?P24; rep_lia).
  rewrite (lor_shift_add b0 b1 8) by (rewrite ?P8, ?P16, ?P24; rep_lia).
  rewrite OR by (rewrite ?P8, ?P16, ?P24; rep_lia).
  rewrite (lor_shift_add _ b2 16) by (rewrite ?P8, ?P16, ?P24; rep_lia).
  rewrite OR by (rewrite ?P8, ?P16, ?P24; rep_lia).
  rewrite (lor_shift_add _ b3 24) by (rewrite ?P8, ?P16, ?P24; rep_lia).
  rewrite P8, P16, P24. reflexivity.
Qed.

(* The C's 64-bit bitmap: lo | (uint64_t)hi << 32; the law's: (uint64_t)hi << 32 | lo. *)
Lemma or64_lo_hi: forall lo hi, u32_ok lo -> u32_ok hi ->
  Int64.or (Int64.repr lo) (Int64.shl (Int64.repr hi) (Int64.repr 32)) = Int64.repr (lo + hi * 4294967296).
Proof.
  intros lo hi L H. unfold u32_ok in *.
  rewrite Int64.shl_mul_two_p. unfold Int64.mul.
  rewrite (Int64.unsigned_repr 32) by rep_lia. change (two_p 32) with 4294967296.
  rewrite (Int64.unsigned_repr hi) by rep_lia. rewrite (Int64.unsigned_repr 4294967296) by rep_lia.
  unfold Int64.or. rewrite (Int64.unsigned_repr lo) by rep_lia.
  rewrite (Int64.unsigned_repr (hi * 4294967296)) by rep_lia.
  change 4294967296 with (2 ^ 32). rewrite lor_shift_add by rep_lia. reflexivity.
Qed.

Lemma or64_hi_lo: forall lo hi, u32_ok lo -> u32_ok hi ->
  Int64.or (Int64.shl (Int64.repr hi) (Int64.repr 32)) (Int64.repr lo) = Int64.repr (lo + hi * 4294967296).
Proof. intros. rewrite Int64.or_commut. apply or64_lo_hi; auto. Qed.

(* ---------------------------------------------------------------------- *)
(* Memory values.                                                         *)
(* ---------------------------------------------------------------------- *)

(* An image's bytes as memory values: exactly what nondet_bytes writes. *)
Notation bytes_val bs := (map (fun b => Vint (Int.repr b)) bs).
Notation words_val ws := (map (fun w => Vint (Int.repr w)) ws) (only parsing).

(* The values of the structs, as the nested pairs reptype computes to (fields in declaration order).  They do not
   mention a compspecs, so the law uses them at its own. *)
Definition target_t : Type := (val * (val * (val * (val * (val * val)))))%type.
Definition desc_t : Type := (val * (val * (val * val)))%type.
Definition policy_t : Type :=
  (val * (val * (val * (val * (val * (val * (val * (val * (list val * (val * list desc_t))))))))))%type.
Definition vm_t : Type :=
  (val * (val * (val * (val * (val * (policy_t * (target_t * (list val * (list val * (val * (val * val)))))))))))%type.

Definition target_val (T: target) : target_t :=
  (Vint (Int.repr (tg_bus T)), (Vint (Int.repr (tg_dev T)), (Vint (Int.repr (tg_fn T)),
   (Vint (Int.repr (tg_id T)), (Vint (Int.repr (tg_window T)), Vint (Int.repr (tg_bar T))))))).

Definition desc_val (d: desc) : desc_t :=
  (Vint (Int.repr (ds_trb d)), (Vint (Int.repr (ds_start d)), (Vint (Int.repr (ds_count d)),
   Vint (Int.repr (ds_stride d))))).

(* struct wifi_policy from its scalars and its two arrays as values (flat arguments). *)
Definition policy_rep (present dma window cfg_read cfg_write cmd_clear cmd_set sink_count: Z)
    (sinks: list val) (desc_count: Z) (descs: list desc_t) : policy_t :=
  (Vint (Int.repr present), (Vint (Int.repr dma), (Vint (Int.repr window),
   (Vlong (Int64.repr cfg_read), (Vlong (Int64.repr cfg_write),
   (Vint (Int.repr cmd_clear), (Vint (Int.repr cmd_set),
   (Vint (Int.repr sink_count), (sinks, (Vint (Int.repr desc_count), descs)))))))))).

Definition policy_val (P: policy) : policy_t :=
  policy_rep (pl_present P) (pl_dma P) (pl_window P) (pl_cfg_read P) (pl_cfg_write P)
    (pl_cmd_clear P) (pl_cmd_set P) (pl_sink_count P) (words_val (pl_sinks P))
    (pl_desc_count P) (map desc_val (pl_descs P)).

(* struct wifi_vm from its fields (flat arguments). *)
Definition vm_rep (code blob: val) (n blob_len window: Z) (pol: policy_t) (tg: target_t)
    (r stack: list val) (sp pc steps: Z) : vm_t :=
  (code, (blob, (Vint (Int.repr n), (Vint (Int.repr blob_len), (Vint (Int.repr window),
   (pol, (tg, (r, (stack, (Vint (Int.repr sp), (Vint (Int.repr pc), Vlong (Int64.repr steps)))))))))))).

Definition vm_val (V: vmstate) : vm_t :=
  vm_rep (vm_code V) (vm_blob V) (vm_n V) (vm_blob_len V) (vm_window V)
    (policy_val (vm_pol V)) (target_val (vm_target V)) (words_val (vm_r V)) (words_val (vm_stack V))
    (vm_sp V) (vm_pc V) (vm_steps V).

(* ---------------------------------------------------------------------- *)
(* Facts of the decode.                                                   *)
(* ---------------------------------------------------------------------- *)

Lemma le64_range: forall bs k, Forall u8_ok bs -> u64_ok (le64 bs k).
Proof.
  intros bs k F. unfold le64, u64_ok.
  pose proof (le32_range bs k F) as A. pose proof (le32_range bs (k + 4) F) as B. unfold u32_ok in *. rep_lia.
Qed.

Lemma land_range: forall x n, 0 <= n -> 0 <= Z.land x (Z.ones n) < 2 ^ n.
Proof. intros. rewrite Z.land_ones by lia. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. Qed.

(* A decoded header: a well-formed target and policy, and a header length from 16 to the image's length. *)
Lemma decode_wf: forall bs T P H, Forall u8_ok bs -> decode bs = Some (T, P, H) ->
  target_wf T /\ decoded_wf P /\ 16 <= H <= Zlength bs.
Proof.
  intros bs T P H F E.
  assert (W: forall k, u32_ok (le32 bs k)) by (intros; apply le32_range; auto).
  assert (W64: forall k, u64_ok (le64 bs k)) by (intros; apply le64_range; auto).
  assert (TW: target_wf (target_of bs)).
  { unfold target_wf, target_of, bar_of; cbn [tg_bus tg_dev tg_fn tg_id tg_window tg_bar].
    pose proof (W 16) as B. unfold u32_ok in *.
    assert (S16: 0 <= Z.shiftr (le32 bs 16) 16) by (apply Z.shiftr_nonneg; lia).
    assert (S8: 0 <= Z.shiftr (le32 bs 16) 8) by (apply Z.shiftr_nonneg; lia).
    pose proof (land_range (Z.shiftr (le32 bs 16) 16) 8 ltac:(lia)).
    pose proof (land_range (Z.shiftr (le32 bs 16) 8) 5 ltac:(lia)).
    pose proof (land_range (le32 bs 16) 3 ltac:(lia)).
    change (Z.ones 8) with 255 in *. change (Z.ones 5) with 31 in *. change (Z.ones 3) with 7 in *.
    change (2 ^ 8) with 256 in *. change (2 ^ 5) with 32 in *. change (2 ^ 3) with 8 in *.
    repeat split; try rep_lia; try apply W.
    all: destruct (le32 bs 28 =? 0); try rep_lia; apply W. }
  assert (NP: decoded_wf no_policy).
  { unfold decoded_wf, no_policy;
      cbn [pl_present pl_dma pl_window pl_cfg_read pl_cfg_write pl_cmd_clear pl_cmd_set pl_sink_count
           pl_sinks pl_desc_count pl_descs].
    unfold u32_ok, u64_ok, MAX_SINKS, MAX_DESCS. repeat split; try rep_lia; try reflexivity; constructor. }
  assert (V3: forall S D ds, 0 <= S <= MAX_SINKS -> 0 <= D <= MAX_DESCS -> Zlength ds = D ->
            Forall desc_wf ds -> decoded_wf (v3_policy bs S D ds)).
  { intros S D ds HS HD HL HF. unfold decoded_wf, v3_policy;
      cbn [pl_present pl_dma pl_window pl_cfg_read pl_cfg_write pl_cmd_clear pl_cmd_set pl_sink_count
           pl_sinks pl_desc_count pl_descs].
    pose proof (W 32) as W32. unfold u32_ok in W32.
    pose proof (land_range (le32 bs 32) 1 ltac:(lia)).
    change (Z.ones 1) with 1 in *. change (2 ^ 1) with 2 in *.
    repeat split; try rep_lia; try apply W; try apply W64; auto.
    - apply Zlength_sinks_at; lia.
    - unfold sinks_at. apply Forall_map, Forall_forall. intros. apply W. }
  unfold decode in E.
  destruct ((Zlength bs <? 16) || negb (le32 bs 0 =? MAGIC)) eqn:C0; [ discriminate | ].
  apply orb_false_iff in C0 as [C0 _]. apply Z.ltb_ge in C0.
  destruct (le32 bs 4 =? 1) eqn:C1.
  { inversion E; subst. split; [ | split; [ exact NP | lia ] ].
    unfold target_wf, bcm_target, BCM_ID; cbn. repeat split; rep_lia. }
  destruct (negb ((le32 bs 4 =? 2) || (le32 bs 4 =? 3))) eqn:C2; [ discriminate | ].
  destruct (Zlength bs <? (if le32 bs 4 =? 3 then 68 else 32)) eqn:C3; [ discriminate | ].
  apply Z.ltb_ge in C3.
  destruct (negb (target_ok bs)) eqn:C4; [ discriminate | ].
  destruct (le32 bs 4 =? 2) eqn:C5.
  { inversion E; subst. split; [ exact TW | split; [ exact NP | ] ].
    rewrite Z.eqb_eq in C5. rewrite C5 in C3. simpl in C3. lia. }
  rewrite orb_false_l, negb_false_iff, Z.eqb_eq in C2. rewrite C2 in C3. simpl in C3.
  pose proof (W 64) as W64'. unfold u32_ok in W64'.
  destruct ((3 <? le32 bs 32) || (le32 bs 36 <? tg_window (target_of bs)) || (MAX_SINKS <? le32 bs 64) ||
            (Zlength bs <? 68 + 4 * le32 bs 64)) eqn:C6; [ discriminate | ].
  repeat rewrite orb_false_iff in C6. destruct C6 as [[[_ _] C6a] C6b].
  apply Z.ltb_ge in C6a. apply Z.ltb_ge in C6b.
  destruct (Z.land (le32 bs 32) 2 =? 0) eqn:C7.
  { inversion E; subst. split; [ exact TW | split; [ apply V3; unfold MAX_SINKS, MAX_DESCS in *; auto; lia | lia ] ]. }
  destruct (Zlength bs <? 68 + 4 * le32 bs 64 + 4) eqn:C8; [ discriminate | ].
  destruct ((MAX_DESCS <? le32 bs (68 + 4 * le32 bs 64)) ||
            (Zlength bs <? 68 + 4 * le32 bs 64 + 4 + 16 * le32 bs (68 + 4 * le32 bs 64))) eqn:C9; [ discriminate | ].
  apply orb_false_iff in C9 as [C9a C9b]. apply Z.ltb_ge in C9a. apply Z.ltb_ge in C9b.
  destruct (negb (forallb desc_ok (descs_at bs (68 + 4 * le32 bs 64) (le32 bs (68 + 4 * le32 bs 64))))) eqn:C10;
    [ discriminate | ].
  pose proof (W (68 + 4 * le32 bs 64)) as WD. unfold u32_ok in WD.
  inversion E; subst. split; [ exact TW | split ].
  - apply V3; unfold MAX_SINKS, MAX_DESCS in *; try lia.
    + apply Zlength_descs_at; lia.
    + unfold descs_at. apply Forall_map, Forall_forall. intros. unfold desc_wf, desc_at; cbn. repeat split; apply W.
  - lia.
Qed.
