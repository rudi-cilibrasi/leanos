(* Law capabilities_complete: the pure part.  A device that answers every read with success and the word of a
   fixed space W, over a well-formed planted list, makes `walk` (Defs.v) end OK with exactly the planted headers;
   and the bit facts of the harness's planting of the list. *)
Require Import VST.floyd.proofauto.
Require Import LeanosCaps.proof.Defs.
Local Open Scope Z_scope.

(* An answer of the fixed space W: the read succeeded with the word at its offset. *)
Definition served (W: list Z) (a: answer) : Prop :=
  match a with (o, ok, v) => ok = true /\ v = Znth (o / 4) W end.

(* A planted offset: dword-aligned, in [0x40, 0xfc]. *)
Definition at_ok (a: Z) : Prop := 64 <= a <= 252 /\ Z.land a 3 = 0.

(* The published header of offset a in W. *)
Definition cap_of (W: list Z) (a: Z) : Z * Z := (a, Znth (a / 4) W).

(* The headers at the offsets of l, linked in that order and ended by 0, with ids other than 0xff. *)
Fixpoint links (W: list Z) (l: list Z) : Prop :=
  match l with
  | nil => True
  | a :: l' => Z.land (Znth (a / 4) W) 255 <> 255 /\ Z.land (Z.shiftr (Znth (a / 4) W) 8) 255 = hd 0 l' /\
               links W l'
  end.

(* The same, header by header (the harness's loop): header k links to header k + 1, or to 0 for the last. *)
Definition next_of (ats: list Z) (k: Z) : Z := if k + 1 <? Zlength ats then Znth (k + 1) ats else 0.
Definition node_ok (W: list Z) (ats: list Z) (k: Z) : Prop :=
  Z.land (Znth (Znth k ats / 4) W) 255 <> 255 /\
  Z.land (Z.shiftr (Znth (Znth k ats / 4) W) 8) 255 = next_of ats k.

Lemma links_of_nodes: forall W ats, (forall k, 0 <= k < Zlength ats -> node_ok W ats k) -> links W ats.
Proof.
  intros W ats. induction ats as [|a l IH]; intros N; cbn [links]; auto.
  destruct (N 0) as [N1 N2]; [ rewrite Zlength_cons; pose proof (Zlength_nonneg l); lia | ].
  rewrite Znth_0_cons in N1, N2. unfold next_of in N2. rewrite Zlength_cons in N2.
  split; [ exact N1 | split ].
  - rewrite N2. destruct l as [|b l'].
    + reflexivity.
    + rewrite Zlength_cons. pose proof (Zlength_nonneg l').
      destruct (Z.ltb_spec (0 + 1) (Z.succ (Z.succ (Zlength l')))); [ | lia ].
      rewrite Znth_pos_cons by lia. reflexivity.
  - apply IH. intros k Hk. destruct (N (k + 1)) as [M1 M2]; [ rewrite Zlength_cons; lia | ].
    rewrite Znth_pos_cons in M1, M2 by lia. replace (k + 1 - 1) with k in M1, M2 by lia.
    split; [ exact M1 | ]. rewrite M2. unfold next_of. rewrite Zlength_cons.
    destruct (Z.ltb_spec (k + 1 + 1) (Z.succ (Zlength l))), (Z.ltb_spec (k + 1) (Zlength l)); try lia.
    all: rewrite Znth_pos_cons by lia; replace (k + 1 + 1 - 1) with (k + 1) by lia; reflexivity.
Qed.

Lemma existsb_eqb_false: forall a l, ~ In a l -> existsb (Z.eqb a) l = false.
Proof.
  intros a l. induction l as [|b l IH]; intros N; simpl; auto.
  rewrite (proj2 (Z.eqb_neq a b)) by (intro E; subst; apply N; left; reflexivity).
  simpl. apply IH. intro I. apply N. right. exact I.
Qed.

(* The list loop, from the header after pre (read already) to the end. *)
Lemma walk_chain_planted: forall W suf pre fuel ans st off caps,
  NoDup (pre ++ suf) -> Forall at_ok suf -> Zlength (pre ++ suf) <= 48 -> links W suf ->
  (length suf < fuel)%nat -> Forall (served W) ans ->
  walk_chain fuel (hd 0 suf) (Zlength pre) (rev pre) (rev (map (cap_of W) pre)) ans = Some (st, off, caps) ->
  st = S_OK /\ caps = map (cap_of W) (pre ++ suf).
Proof.
  intros W suf. induction suf as [|a suf IH]; intros pre fuel ans st off caps ND AOK LEN LK FU SV E.
  - destruct fuel as [|f]; [ simpl in FU; lia | ].
    simpl in E. rewrite rev_involutive in E.
    destruct ans; [ | discriminate ]. inversion E; subst. rewrite app_nil_r. auto.
  - destruct fuel as [|f]; [ simpl in FU; lia | ].
    inversion AOK as [| ? ? [A1 A2] AOK']; subst.
    destruct LK as [L1 [L2 LK']].
    assert (NI: ~ In a (rev pre)).
    { rewrite <- in_rev. intro I. apply (NoDup_remove_2 pre suf a ND). apply in_or_app. left. exact I. }
    assert (LP: Zlength pre < 48).
    { rewrite Zlength_app, Zlength_cons in LEN. pose proof (Zlength_nonneg suf). lia. }
    cbn [walk_chain hd] in E.
    rewrite (proj2 (Z.eqb_neq a 0)) in E by lia.
    rewrite A2 in E. rewrite (proj2 (Z.ltb_ge a 64)) in E by lia. simpl orb in E.
    rewrite (existsb_eqb_false a (rev pre) NI) in E.
    rewrite (proj2 (Z.eqb_neq (Zlength pre) 48)) in E by lia.
    destruct ans as [|[[o ok] v] rest]; [ discriminate | ].
    apply Forall_cons_iff in SV. destruct SV as [[Ok Ev] SV']. subst.
    destruct (Z.eqb_spec o a); [ subst o | discriminate ].
    change (negb true) with false in E. cbv iota in E.
    rewrite (proj2 (Z.eqb_neq _ 255)) in E by exact L1.
    rewrite L2 in E.
    assert (R1: Zlength pre + 1 = Zlength (pre ++ [a])) by (rewrite Zlength_app; reflexivity).
    assert (R2: a :: rev pre = rev (pre ++ [a])) by (rewrite rev_app_distr; reflexivity).
    assert (R3: (a, Znth (a / 4) W) :: rev (map (cap_of W) pre) = rev (map (cap_of W) (pre ++ [a])))
      by (rewrite map_app, rev_app_distr; reflexivity).
    rewrite R1, R2, R3 in E.
    replace (pre ++ a :: suf) with ((pre ++ [a]) ++ suf) by (rewrite <- app_assoc; reflexivity).
    apply (IH (pre ++ [a]) f rest st off caps); auto.
    + rewrite <- app_assoc. exact ND.
    + rewrite <- app_assoc. exact LEN.
    + simpl in FU. lia.
Qed.

(* One header read: the answer is the word of the initial header, so the check passes. *)
Lemma header_step: forall W o m hs h out, 0 <= o / 4 < 16 -> 16 <= Zlength W -> Forall (served W) h ->
  walk_header ((o, m) :: hs) (sublist 0 16 W) h = Some out ->
  exists h', Forall (served W) h' /\ walk_header hs (sublist 0 16 W) h' = Some out.
Proof.
  intros W o m hs h out Ho LW SV E.
  destruct h as [|[[o' ok] v] h']; [ discriminate | ].
  apply Forall_cons_iff in SV. destruct SV as [[Ok Ev] SV']. subst.
  cbn [walk_header] in E.
  destruct (Z.eqb_spec o' o); [ subst o' | discriminate ].
  change (negb true) with false in E. cbv iota in E.
  rewrite Znth_sublist, Z.add_0_r, Z.eqb_refl in E by lia. change (negb true) with false in E. cbv iota in E.
  exists h'. auto.
Qed.

(* THE HEART: a log of fixed answers over W in which the walk of a well-formed planted list ends is the planted
   list, published OK. *)
Lemma walk_planted: forall W ats h st off caps,
  Zlength W = 64 -> NoDup ats -> Forall at_ok ats -> Zlength ats <= 48 -> links W ats ->
  list_head (sublist 0 16 W) = hd 0 ats -> Forall (served W) h ->
  walk (sublist 0 16 W) h = Some (st, off, caps) ->
  st = S_OK /\ caps = map (cap_of W) ats.
Proof.
  intros W ats h st off caps LW ND AOK LA LK HD SV E.
  unfold walk, header_checks in E.
  apply header_step in E; [ | simpl; lia | lia | exact SV ]. destruct E as [h1 [SV1 E]].
  apply header_step in E; [ | simpl; lia | lia | exact SV1 ]. destruct E as [h2 [SV2 E]].
  apply header_step in E; [ | simpl; lia | lia | exact SV2 ]. destruct E as [h3 [SV3 E]].
  apply header_step in E; [ | simpl; lia | lia | exact SV3 ]. destruct E as [h4 [SV4 E]].
  cbn [walk_header] in E. rewrite HD in E.
  apply (walk_chain_planted W ats nil 50 h4 st off caps); auto.
  rewrite Zlength_correct in LA. lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* Bits.                                                                   *)
(* ---------------------------------------------------------------------- *)

Lemma testbit_small: forall x k j, 0 <= x < 2 ^ k -> 0 <= k <= j -> Z.testbit x j = false.
Proof.
  intros x k j [H0 H1] [Hk Hkj].
  apply Z.testbit_false; [ lia | ].
  rewrite Z.div_small; [ reflexivity | ].
  split; [ lia | ]. apply Z.lt_le_trans with (2 ^ k); auto. apply Z.pow_le_mono_r; lia.
Qed.

Lemma tb255: forall j, 0 <= j -> Z.testbit 255 j = (j <? 8).
Proof. intros. change 255 with (Z.ones 8). apply Z.testbit_ones_nonneg; lia. Qed.

Lemma tbhi16: forall j, 0 <= j -> Z.testbit 4294901760 j = (negb (j <? 16) && (j <? 32))%bool.
Proof.
  intros. change 4294901760 with (Z.ldiff (Z.ones 32) (Z.ones 16)).
  rewrite Z.ldiff_spec, !Z.testbit_ones_nonneg by lia. apply andb_comm.
Qed.

Lemma u32_bits: forall x, 0 <= x -> (forall j, 32 <= j -> Z.testbit x j = false) -> x <= Int.max_unsigned.
Proof.
  intros x Hx B.
  assert (E: x = Z.land x (Z.ones 32)).
  { apply Z.bits_inj'. intros j Hj. rewrite Z.land_spec, Z.testbit_ones_nonneg by lia.
    destruct (Z.ltb_spec j 32).
    - rewrite andb_true_r. reflexivity.
    - rewrite B by lia. reflexivity. }
  rewrite E, Z.land_ones by lia. pose proof (Z.mod_pos_bound x (2 ^ 32) ltac:(lia)).
  change Int.max_unsigned with (2 ^ 32 - 1). lia.
Qed.

Lemma u32_high: forall x j, 0 <= x <= Int.max_unsigned -> 32 <= j -> Z.testbit x j = false.
Proof. intros. apply (testbit_small x 32 j); [ change Int.max_unsigned with (2 ^ 32 - 1) in *; lia | lia ]. Qed.

(* The word the harness plants for a header: (w & 0xffff0000) | (next << 8) | id. *)
Definition plant (w nx id: Z) : Z := Z.lor (Z.lor (Z.land w 4294901760) (Z.shiftl nx 8)) id.

Lemma plant_id: forall w nx id, 0 <= nx < 256 -> 0 <= id < 256 -> Z.land (plant w nx id) 255 = id.
Proof.
  intros w nx id Hn Hi. unfold plant. apply Z.bits_inj'. intros j Hj.
  rewrite Z.land_spec, !Z.lor_spec, Z.land_spec, Z.shiftl_spec, tb255, tbhi16 by lia.
  destruct (Z.ltb_spec j 8).
  - rewrite (Z.testbit_neg_r nx) by lia.
    destruct (Z.ltb_spec j 16); [ | lia ]. simpl.
    destruct (Z.testbit w j), (Z.testbit id j); reflexivity.
  - rewrite (testbit_small id 8 j) by (simpl; lia). rewrite andb_false_r. reflexivity.
Qed.

Lemma plant_next: forall w nx id, 0 <= nx < 256 -> 0 <= id < 256 ->
  Z.land (Z.shiftr (plant w nx id) 8) 255 = nx.
Proof.
  intros w nx id Hn Hi. unfold plant. apply Z.bits_inj'. intros j Hj.
  rewrite Z.land_spec, Z.shiftr_spec, !Z.lor_spec, Z.land_spec, Z.shiftl_spec, tb255, tbhi16 by lia.
  replace (j + 8 - 8) with j by lia.
  destruct (Z.ltb_spec j 8).
  - destruct (Z.ltb_spec (j + 8) 16); [ | lia ].
    rewrite (testbit_small id 8 (j + 8)) by (simpl; lia). simpl.
    destruct (Z.testbit nx j), (Z.testbit w (j + 8)); reflexivity.
  - rewrite (testbit_small nx 8 j) by (simpl; lia). rewrite !andb_false_r. reflexivity.
Qed.

Lemma plant_range: forall w nx id, 0 <= w <= Int.max_unsigned -> 0 <= nx < 256 -> 0 <= id < 256 ->
  0 <= plant w nx id <= Int.max_unsigned.
Proof.
  intros w nx id Hw Hn Hi. unfold plant. split.
  - apply Z.lor_nonneg. split; [ apply Z.lor_nonneg; split | lia ].
    + apply Z.land_nonneg. lia.
    + apply Z.shiftl_nonneg. lia.
  - apply u32_bits.
    + apply Z.lor_nonneg. split; [ apply Z.lor_nonneg; split | lia ].
      * apply Z.land_nonneg. lia.
      * apply Z.shiftl_nonneg. lia.
    + intros j Hj. rewrite !Z.lor_spec, Z.land_spec, Z.shiftl_spec by lia.
      rewrite (u32_high w j Hw Hj), (testbit_small nx 8 (j - 8)), (testbit_small id 8 j) by (simpl; lia).
      reflexivity.
Qed.

(* The status word's capability bit, set and cleared; the head byte of word 13, replaced and cleared. *)
Lemma set_cap_bit: forall w, 0 <= w -> Z.land (Z.lor w 1048576) 1048576 <> 0.
Proof.
  intros w Hw E.
  assert (T: Z.testbit (Z.land (Z.lor w 1048576) 1048576) 20 = true).
  { rewrite Z.land_spec, Z.lor_spec. change 1048576 with (2 ^ 20). rewrite Z.pow2_bits_eqb by lia.
    rewrite orb_true_r. reflexivity. }
  rewrite E in T. discriminate.
Qed.

Lemma clear_cap_bit: forall w, Z.land (Z.land w 4293918719) 1048576 = 0.
Proof. intros. rewrite <- Z.land_assoc. change (Z.land 4293918719 1048576) with 0. apply Z.land_0_r. Qed.

Lemma set_head: forall w a, 0 <= a < 256 -> Z.land (Z.lor (Z.land w 4294967040) a) 255 = a.
Proof.
  intros w a Ha. rewrite Z.land_lor_distr_l, <- Z.land_assoc. change (Z.land 4294967040 255) with 0.
  rewrite Z.land_0_r, Z.lor_0_l. change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  apply Z.mod_small. simpl. lia.
Qed.

Lemma clear_head: forall w, Z.land (Z.land w 4294967040) 255 = 0.
Proof. intros. rewrite <- Z.land_assoc. change (Z.land 4294967040 255) with 0. apply Z.land_0_r. Qed.

(* Ranges of the bitwise results. *)
Lemma land_range: forall a b, 0 <= a <= Int.max_unsigned -> 0 <= b -> 0 <= Z.land a b <= Int.max_unsigned.
Proof.
  intros a b Ha Hb. split; [ apply Z.land_nonneg; lia | ].
  apply u32_bits; [ apply Z.land_nonneg; lia | ].
  intros j Hj. rewrite Z.land_spec, (u32_high a j Ha Hj). reflexivity.
Qed.

Lemma lor_range: forall a b, 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  0 <= Z.lor a b <= Int.max_unsigned.
Proof.
  intros a b Ha Hb. split; [ apply Z.lor_nonneg; lia | ].
  apply u32_bits; [ apply Z.lor_nonneg; lia | ].
  intros j Hj. rewrite Z.lor_spec, (u32_high a j Ha Hj), (u32_high b j Hb Hj). reflexivity.
Qed.

(* Int operations on in-range values, as Z operations. *)
Lemma int_and: forall a b, 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Int.and (Int.repr a) (Int.repr b) = Int.repr (Z.land a b).
Proof. intros. unfold Int.and. rewrite !Int.unsigned_repr by lia. reflexivity. Qed.

Lemma int_or: forall a b, 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Int.or (Int.repr a) (Int.repr b) = Int.repr (Z.lor a b).
Proof. intros. unfold Int.or. rewrite !Int.unsigned_repr by lia. reflexivity. Qed.

Lemma int_shl8: forall a, 0 <= a <= Int.max_unsigned ->
  Int.shl (Int.repr a) (Int.repr 8) = Int.repr (Z.shiftl a 8).
Proof. intros. unfold Int.shl. rewrite !Int.unsigned_repr by rep_lia. reflexivity. Qed.

Lemma int_shru16: forall a, 0 <= a <= Int.max_unsigned ->
  Int.shru (Int.repr a) (Int.repr 16) = Int.repr (Z.shiftr a 16).
Proof. intros. unfold Int.shru. rewrite !Int.unsigned_repr by rep_lia. reflexivity. Qed.

Lemma shiftr_range: forall a n, 0 <= a <= Int.max_unsigned -> 0 <= n -> 0 <= Z.shiftr a n <= Int.max_unsigned.
Proof.
  intros a n Ha Hn. rewrite Z.shiftr_div_pow2 by lia. split.
  - apply Z.div_pos; [ lia | apply Z.pow_pos_nonneg; lia ].
  - apply Z.le_trans with a; [ | lia ]. apply Z.div_le_upper_bound; [ apply Z.pow_pos_nonneg; lia | ].
    assert (1 <= 2 ^ n) by (apply Z.pow_le_mono_r with (a := 2) (b := 0) in Hn; simpl in Hn; lia). nia.
Qed.

Lemma shiftl8_range: forall a, 0 <= a < 256 -> 0 <= Z.shiftl a 8 <= Int.max_unsigned.
Proof. intros. rewrite Z.shiftl_mul_pow2 by lia. simpl. rep_lia. Qed.

Lemma repr_m65536: Int.repr (-65536) = Int.repr 4294901760.
Proof. apply Int.eqm_samerepr. exists (-1). reflexivity. Qed.

Lemma not_255: Int.not (Int.repr 255) = Int.repr 4294967040.
Proof. reflexivity. Qed.

Lemma not_cap_bit: Int.not (Int.repr 1048576) = Int.repr 4293918719.
Proof. reflexivity. Qed.

(* offset / 4 of the callback, an int division of a uint8_t offset. *)
Lemma divs4: forall off, 0 <= off <= 252 -> Int.signed (Int.divs (Int.repr off) (Int.repr 4)) = off / 4.
Proof.
  intros off H. unfold Int.divs. rewrite (Int.signed_repr off), (Int.signed_repr 4) by rep_lia.
  rewrite Z.quot_div_nonneg by lia.
  assert (0 <= off / 4 <= 63) by (Z.div_mod_to_equations; lia).
  rewrite Int.signed_repr by rep_lia. reflexivity.
Qed.
