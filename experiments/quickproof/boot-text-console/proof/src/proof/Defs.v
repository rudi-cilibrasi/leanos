(* Pure definitions shared by every proof of leanos_console: the Lean selector's predicate, the Multiboot2
   tag walk of boot_text_parse as a function, and the console's well-formedness.  No program here. *)
Require Import VST.floyd.proofauto.

(* LeanOS.BootTextConsole.valid, on the six scalar words of checkRaw.  The conjunction is the same as the
   model's sequence of tests (patch/lean_export_model.c); 2 * width cannot wrap once width <= 160. *)
Definition valid_geo (kind bits address pitch width height: Z) : bool :=
  ((kind =? 2) && (bits =? 16) && (address =? 753664) && (0 <? width) && (width <=? 160) &&
   (0 <? height) && (height <=? 64) && (pitch mod 2 =? 0) && (2 * width <=? pitch) && (pitch <=? 512))%bool.

(* The fields of struct boot_text_geometry. *)
Record geo := mkgeo { g_address: Z; g_pitch: Z; g_width: Z; g_height: Z; g_kind: Z; g_bits: Z }.

Definition geo_valid (g: geo) : bool :=
  valid_geo (g_kind g) (g_bits g) (g_address g) (g_pitch g) (g_width g) (g_height g).

(* Every field holds a value of its C type. *)
Definition geo_wf (g: geo) : Prop :=
  0 <= g_address g <= Int64.max_unsigned /\ 0 <= g_pitch g <= Int.max_unsigned /\
  0 <= g_width g <= Int.max_unsigned /\ 0 <= g_height g <= Int.max_unsigned /\
  0 <= g_kind g <= Byte.max_unsigned /\ 0 <= g_bits g <= Byte.max_unsigned.

(* boot_text_u32: the little-endian 32-bit word at byte k. *)
Definition le32 (bs: list Z) (k: Z) : Z :=
  Znth k bs + Znth (k + 1) bs * 256 + Znth (k + 2) bs * 65536 + Znth (k + 3) bs * 16777216.

(* The geometry boot_text_parse stores from a framebuffer tag at byte o. *)
Definition geo_at (bs: list Z) (o: Z) : geo :=
  mkgeo (le32 bs (o + 8) + le32 bs (o + 12) * 4294967296) (le32 bs (o + 16)) (le32 bs (o + 20))
        (le32 bs (o + 24)) (Znth (o + 29) bs) (Znth (o + 28) bs).

(* (size + 7u) & ~7u for a size that cannot wrap. *)
Definition round8 (s: Z) : Z := (s + 7) / 8 * 8.

(* The loop of boot_text_parse from byte `offset`, with the framebuffer geometry seen so far: Some g is an
   accepted geometry, None a rejection.  Each step advances by at least 8 bytes. *)
Fixpoint walk (fuel: nat) (bs: list Z) (total offset: Z) (seen: option geo) : option geo :=
  match fuel with
  | O => None
  | S f =>
    if offset <=? total - 8 then
      let type := le32 bs offset in
      let size := le32 bs (offset + 4) in
      if ((size <? 8) || (total - offset <? size))%bool then None else
      let adv := round8 size in
      if total - offset <? adv then None else
      if type =? 0 then
        match seen with
        | Some g => if ((size =? 8) && (offset + adv =? total) && geo_valid g)%bool then Some g else None
        | None => None
        end
      else if type =? 8 then
        match seen with
        | Some _ => None
        | None => if size <? 32 then None else walk f bs total (offset + adv) (Some (geo_at bs offset))
        end
      else walk f bs total (offset + adv) seen
    else None
  end.

(* boot_text_parse on the buffer bs with `available` bytes. *)
Definition parse_model (bs: list Z) (available: Z) : option geo :=
  if available <? 16 then None else
  let total := le32 bs 0 in
  if ((total <? 16) || (available <? total) || (65536 <? total) || negb (total mod 8 =? 0) ||
      negb (le32 bs 4 =? 0))%bool
  then None
  else walk (Z.to_nat total) bs total 8 None.

Definition parse_result (bs: list Z) (available: Z) : Z :=
  match parse_model bs available with Some _ => 1 | None => 0 end.

(* The byte boot_text_putc displays for ch (other than CR and LF). *)
Definition shown (ch: Z) : Z := if ((ch <? 32) || (126 <? ch))%bool then 63 else ch.

(* The console state the writer keeps: a cursor inside an accepted surface of `height` rows of `stride` cells. *)
Definition con_ok (stride width height row column: Z) : Prop :=
  0 < width <= stride /\ stride <= 256 /\ 0 < height <= 64 /\ 0 <= row < height /\ 0 <= column <= width.

(* ---------------------------------------------------------------------- *)
(* Facts                                                                  *)
(* ---------------------------------------------------------------------- *)

Lemma walk_some_valid: forall f bs total offset seen g,
  (forall g0, seen = Some g0 -> True) ->
  walk f bs total offset seen = Some g -> geo_valid g = true.
Proof.
  induction f; intros bs total offset seen g _ H; simpl in H; [ discriminate | ].
  destruct (offset <=? total - 8); [ | discriminate ].
  destruct ((le32 bs (offset + 4) <? 8) || (total - offset <? le32 bs (offset + 4)))%bool; [ discriminate | ].
  destruct (total - offset <? round8 (le32 bs (offset + 4))); [ discriminate | ].
  destruct (le32 bs offset =? 0).
  - destruct seen as [g0 | ]; [ | discriminate ].
    destruct ((le32 bs (offset + 4) =? 8) && (offset + round8 (le32 bs (offset + 4)) =? total) && geo_valid g0)%bool
      eqn:E; [ | discriminate ].
    inversion H; subst. apply andb_prop in E. tauto.
  - destruct (le32 bs offset =? 8).
    + destruct seen; [ discriminate | ].
      destruct (le32 bs (offset + 4) <? 32); [ discriminate | ].
      eapply IHf; [ | exact H ]. auto.
    + eapply IHf; [ | exact H ]. auto.
Qed.

Lemma parse_model_valid: forall bs available g,
  parse_model bs available = Some g -> geo_valid g = true.
Proof.
  unfold parse_model; intros.
  destruct (available <? 16); [ discriminate | ].
  match type of H with context [if ?b then _ else _] => destruct b end; [ discriminate | ].
  eapply walk_some_valid; [ | exact H ]. auto.
Qed.

Lemma valid_geo_bounds: forall kind bits address pitch width height,
  valid_geo kind bits address pitch width height = true ->
  kind = 2 /\ bits = 16 /\ address = 753664 /\ 0 < width <= 160 /\ 0 < height <= 64 /\
  pitch mod 2 = 0 /\ 2 * width <= pitch /\ pitch <= 512.
Proof.
  unfold valid_geo; intros.
  repeat match goal with
         | H: andb _ _ = true |- _ => apply andb_prop in H; destruct H
         end.
  repeat match goal with
         | H: (_ =? _) = true |- _ => apply Z.eqb_eq in H
         | H: (_ <? _) = true |- _ => apply Z.ltb_lt in H
         | H: (_ <=? _) = true |- _ => apply Z.leb_le in H
         end.
  repeat split; lia.
Qed.

Lemma geo_valid_con_ok: forall g,
  geo_valid g = true ->
  con_ok (g_pitch g / 2) (g_width g) (g_height g) 0 0 /\ g_pitch g = 2 * (g_pitch g / 2) /\
  g_height g * g_pitch g <= 32768.
Proof.
  intros g H. unfold geo_valid in H. apply valid_geo_bounds in H.
  destruct H as (_ & _ & _ & Hw & Hh & Hm & H2w & Hp).
  assert (Hdiv: g_pitch g = 2 * (g_pitch g / 2) + g_pitch g mod 2) by (apply Z_div_mod_eq_full).
  assert (Hp2: g_pitch g = 2 * (g_pitch g / 2)) by lia.
  assert (Hhp: g_height g * g_pitch g <= 64 * 512).
  { apply Z.mul_le_mono_nonneg; lia. }
  unfold con_ok. split; [ | split ]; [ | exact Hp2 | lia ].
  repeat split; lia.
Qed.

Lemma le32_range: forall bs k,
  Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  0 <= le32 bs k <= Int.max_unsigned.
Proof.
  intros bs k H. unfold le32.
  assert (B: forall i, 0 <= Znth i bs <= 255).
  { intros i. destruct (zlt i 0).
    - rewrite Znth_underflow by lia. cbv [default Inhabitant_Z]. lia.
    - destruct (zlt i (Zlength bs)).
      + assert (Hi: 0 <= i < Zlength bs) by lia.
        pose proof (proj1 (Forall_Znth bs _) H i Hi) as Hb. simpl in Hb. rep_lia.
      + rewrite Znth_overflow by lia. cbv [default Inhabitant_Z]. lia. }
  pose proof (B k); pose proof (B (k + 1)); pose proof (B (k + 2)); pose proof (B (k + 3)).
  rep_lia.
Qed.
