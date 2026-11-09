(* Law consumer_obligations: the facts of Defs.records that the harness's records_ok follows: the walk one record at
   a time, and the packing of an NMI record (pack6) one byte at a time. *)
Require Import VST.floyd.proofauto.
Require Import LeanosMadt.proof.Defs.
Require Import LeanosMadt.proof.MadtSpecs.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Lemma walk_S: forall f bytes pos count nmi,
  walk_records (S f) bytes pos count nmi =
  if Zlength bytes <=? pos then Some (count, nmi)
  else if Zlength bytes - pos <? 2 then None
  else if (Znth (pos + 1) bytes <? 2) || (Zlength bytes - pos <? Znth (pos + 1) bytes) then None
  else if Znth pos bytes =? 4 then
    if negb (Znth (pos + 1) bytes =? 6) then None
    else walk_records f bytes (pos + Znth (pos + 1) bytes) (count + 1)
           (if count <? 4 then upd_Znth count nmi (pack6 bytes pos) else nmi)
  else walk_records f bytes (pos + Znth (pos + 1) bytes) count nmi.
Proof. reflexivity. Qed.

(* The first k bytes of the record at pos, packed little-endian. *)
Definition pk (bytes: list Z) (pos: Z) (k: nat) : Z :=
  fold_right Z.lor 0 (map (fun b => Z.shiftl (Znth (pos + Z.of_nat b) bytes) (8 * Z.of_nat b)) (seq 0 k)).

Lemma pk_6: forall bytes pos, pk bytes pos 6 = pack6 bytes pos.
Proof. reflexivity. Qed.

Lemma pk_0: forall bytes pos, pk bytes pos 0 = 0.
Proof. reflexivity. Qed.

Lemma fold_lor: forall l y, fold_right Z.lor y l = Z.lor (fold_right Z.lor 0 l) y.
Proof.
  induction l as [ | a l IH ]; intros y; simpl.
  - destruct y; reflexivity.
  - rewrite IH, Z.lor_assoc. reflexivity.
Qed.

Lemma pk_S: forall bytes pos k,
  pk bytes pos (S k) = Z.lor (pk bytes pos k) (Z.shiftl (Znth (pos + Z.of_nat k) bytes) (8 * Z.of_nat k)).
Proof.
  intros. unfold pk. rewrite seq_S, map_app, fold_right_app. simpl. rewrite Z.lor_0_r. apply fold_lor.
Qed.

Lemma lor_bound: forall a b m, 0 <= a < 2 ^ m -> 0 <= b < 2 ^ m -> 0 <= Z.lor a b < 2 ^ m.
Proof.
  intros a b m Ha Hb. assert (0 <= Z.lor a b) by (apply Z.lor_nonneg; lia). split; auto.
  destruct (Z.eq_dec a 0) as [-> | Na]; [ rewrite Z.lor_0_l; lia | ].
  destruct (Z.eq_dec b 0) as [-> | Nb]; [ rewrite Z.lor_0_r; lia | ].
  assert (P: 0 < Z.lor a b).
  { destruct (Z.eq_dec (Z.lor a b) 0) as [E | E]; [ | lia ]. apply Z.lor_eq_0_iff in E. lia. }
  apply Z.log2_lt_pow2; auto. rewrite Z.log2_lor by lia.
  apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

Lemma shiftl_bound: forall x k, 0 <= x < 256 -> 0 <= k <= 5 -> 0 <= Z.shiftl x (8 * k) < 2 ^ 48.
Proof.
  intros x k Hx Hk. rewrite Z.shiftl_mul_pow2 by lia.
  assert (2 ^ (8 * k) * 2 ^ 8 <= 2 ^ 48).
  { rewrite <- Z.pow_add_r by lia. apply Z.pow_le_mono_r; lia. }
  assert (0 < 2 ^ (8 * k)) by (apply Z.pow_pos_nonneg; lia). nia.
Qed.

Lemma pk_bound: forall bytes pos k, (k <= 6)%nat ->
  (forall j, 0 <= j < Z.of_nat k -> 0 <= Znth (pos + j) bytes < 256) ->
  0 <= pk bytes pos k < 2 ^ 48.
Proof.
  intros bytes pos k. induction k as [ | k IH ]; intros Hk Hb.
  - rewrite pk_0. lia.
  - rewrite pk_S. apply lor_bound.
    + apply IH; [ lia | intros j Hj; apply Hb; lia ].
    + apply shiftl_bound; [ apply Hb; lia | lia ].
Qed.

(* One more byte of the record at pos, as the C computes it on 64-bit words. *)
Lemma or_shl_pk: forall bytes pos b, 0 <= b < 6 ->
  (forall j, 0 <= j < 6 -> 0 <= Znth (pos + j) bytes < 256) ->
  Int64.or (Int64.repr (pk bytes pos (Z.to_nat b)))
           (Int64.shl (Int64.repr (Znth (pos + b) bytes)) (Int64.repr (8 * b))) =
  Int64.repr (pk bytes pos (Z.to_nat (b + 1))).
Proof.
  intros bytes pos b Hb Hr.
  assert (P: 0 <= pk bytes pos (Z.to_nat b) < 2 ^ 48).
  { apply pk_bound; [ lia | intros j Hj; apply Hr; lia ]. }
  assert (X: 0 <= Znth (pos + b) bytes < 256) by (apply Hr; lia).
  assert (Sh: 0 <= Z.shiftl (Znth (pos + b) bytes) (8 * b) < 2 ^ 48) by (apply shiftl_bound; lia).
  assert (M: 2 ^ 48 <= Int64.max_unsigned) by (unfold Int64.max_unsigned; simpl; lia).
  replace (Z.to_nat (b + 1)) with (S (Z.to_nat b)) by lia. rewrite pk_S.
  rewrite Z2Nat.id by lia.
  unfold Int64.or, Int64.shl.
  rewrite (Int64.unsigned_repr (Znth (pos + b) bytes)) by lia.
  rewrite (Int64.unsigned_repr (8 * b)) by (unfold Int64.max_unsigned; simpl; lia).
  rewrite (Int64.unsigned_repr (Z.shiftl _ _)) by lia.
  rewrite (Int64.unsigned_repr (pk _ _ _)) by lia.
  reflexivity.
Qed.

Lemma pack6_bound: forall bytes pos, (forall j, 0 <= j < 6 -> 0 <= Znth (pos + j) bytes < 256) ->
  0 <= pack6 bytes pos <= Int64.max_unsigned.
Proof.
  intros bytes pos Hr. rewrite <- pk_6.
  assert (0 <= pk bytes pos 6 < 2 ^ 48) by (apply pk_bound; [ lia | intros j Hj; apply Hr; simpl in Hj; lia ]).
  assert (2 ^ 48 <= Int64.max_unsigned) by (unfold Int64.max_unsigned; simpl; lia). lia.
Qed.

Lemma mul64_repr': forall a b, Int64.mul (Int64.repr a) (Int64.repr b) = Int64.repr (a * b).
Proof.
  intros. unfold Int64.mul. apply Int64.eqm_samerepr. apply Int64.eqm_mult; apply Int64.eqm_sym, Int64.eqm_unsigned_repr.
Qed.

Lemma shift_amount: forall i, 0 <= i < 6 -> Int64.Z_mod_modulus (8 * Int64.Z_mod_modulus i) < 64.
Proof.
  intros i Hi. rewrite !Int64.Z_mod_modulus_eq. change Int64.modulus with 18446744073709551616.
  rewrite (Z.mod_small i) by lia. rewrite Z.mod_small by lia. lia.
Qed.
