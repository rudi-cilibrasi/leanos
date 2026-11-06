(* Lemmas for the body proofs of include/qotom_bsp_consumer.h (BindProof.v): pointer tests on maybe_at objects, the
   consumer model of Defs.v (run, next_call, consume) one answer at a time in prefix form, stage by stage (the byte
   stream, the NMI policy, the finish), the record walk `records` one record at a time, and the word arithmetic of
   the C expressions. *)
Require Import VST.floyd.proofauto.
Require Import LeanosMadt.madt.code.
Require Import LeanosMadt.proof.Defs.
Require Import LeanosMadt.proof.MadtSpecs.
#[local] Existing Instance MadtSpecs.CS.
Local Open Scope Z_scope.
Local Open Scope bool_scope.   (* && and || are andb and orb here *)

(* ---------- NULL tests ---------- *)

Definition b2z (b: bool) : Z := if b then 1 else 0.

Lemma isnull_null: isnull nullval = true.
Proof. unfold isnull. destruct (Val.eq nullval nullval); [ reflexivity | congruence ]. Qed.

Lemma isnull_nonnull: forall p, p <> nullval -> isnull p = false.
Proof. intros. unfold isnull. destruct (Val.eq p nullval); [ congruence | reflexivity ]. Qed.

Lemma isnull_false: forall p, isnull p = false -> p <> nullval.
Proof. intros p H E. subst. rewrite isnull_null in H. discriminate. Qed.

Lemma maybe_valid: forall sh t v p Q, readable_share sh -> sizeof t > 0 ->
  maybe_at sh t v p * Q |-- valid_pointer p.
Proof.
  intros. unfold maybe_at. destruct (Val.eq p nullval).
  - subst. apply valid_pointer_null.
  - apply sepcon_valid_pointer1. apply data_at_valid_ptr; auto.
Qed.

Lemma maybe_at_nonnull: forall sh t v p, p <> nullval -> maybe_at sh t v p = data_at sh t v p.
Proof. intros. unfold maybe_at. destruct (Val.eq p nullval); [ contradiction | reflexivity ]. Qed.

Lemma maybe_at_null: forall sh t v, maybe_at sh t v nullval = emp.
Proof. intros. unfold maybe_at. destruct (Val.eq nullval nullval); [ reflexivity | congruence ]. Qed.

Ltac tc_ptr :=
  match goal with |- _ |-- denote_tc_test_eq ?p _ =>
    apply denote_tc_test_eq_split;
    [ match goal with |- context [maybe_at ?sh ?t ?v p] =>
        eapply derives_trans; [ | apply (maybe_valid sh t v p TT); [ auto | simpl; try rewrite Z.max_r by lia; try lia ] ];
        cancel end
    | apply valid_pointer_null ]
  end.

Lemma notbool_ptr: forall p, is_pointer_or_null p ->
  force_val (sem_cast_i2bool (force_val (option_map (fun b : bool => bool2val (negb b)) (bool_val_p p)))) =
  Vint (Int.repr (b2z (isnull p))).
Proof.
  intros. destruct p; try contradiction.
  - simpl in H. subst. change (Vlong Int64.zero) with nullval. rewrite isnull_null. reflexivity.
  - rewrite isnull_nonnull by (intro X; inv X). reflexivity.
Qed.

Lemma b2z_true: forall c, Int.repr (b2z c) <> Int.zero -> c = true.
Proof. intros [ | ] H; [ reflexivity | exfalso; apply H; reflexivity ]. Qed.
Lemma b2z_false: forall c, Int.repr (b2z c) = Int.zero -> c = false.
Proof. intros [ | ] H; [ exfalso; apply Int.one_not_zero; exact H | reflexivity ]. Qed.

Ltac bfix :=
  repeat match goal with
  | H: Int.repr (b2z _) <> Int.zero |- _ => apply b2z_true in H
  | H: Int.repr (b2z _) = Int.zero |- _ => apply b2z_false in H
  end.

Lemma bool2val_b2z: forall b, bool2val b = Vint (Int.repr (b2z b)).
Proof. intros [ | ]; reflexivity. Qed.

(* ---------- 64-bit words ---------- *)

Lemma eq64_repr: forall a b, u64_ok a -> u64_ok b -> Int64.eq (Int64.repr a) (Int64.repr b) = (a =? b).
Proof.
  intros. unfold u64_ok in *. unfold Int64.eq. rewrite !Int64.unsigned_repr by auto.
  destruct (zeq a b); destruct (Z.eqb_spec a b); auto; lia.
Qed.

Lemma ltu64_repr: forall a b, u64_ok a -> u64_ok b -> Int64.ltu (Int64.repr a) (Int64.repr b) = (a <? b).
Proof.
  intros. unfold u64_ok in *. unfold Int64.ltu. rewrite !Int64.unsigned_repr by auto.
  destruct (zlt a b); destruct (Z.ltb_spec a b); auto; lia.
Qed.

Lemma repr64_inj: forall a b, u64_ok a -> u64_ok b -> Int64.repr a = Int64.repr b -> a = b.
Proof. intros. unfold u64_ok in *. apply repr_inj_unsigned64; auto. Qed.

Lemma repr64_neq: forall a b, Int64.repr a <> Int64.repr b -> a <> b.
Proof. intros a b H E. subst. contradiction. Qed.

Lemma repr32_neq: forall a b, Int.repr a <> Int.repr b -> a <> b.
Proof. intros a b H E. subst. contradiction. Qed.

Lemma eq32_repr: forall a b, 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Int.eq (Int.repr a) (Int.repr b) = (a =? b).
Proof.
  intros. unfold Int.eq. rewrite !Int.unsigned_repr by auto.
  destruct (zeq a b); destruct (Z.eqb_spec a b); auto; lia.
Qed.

Lemma u64_ok_Znth: forall l i, Forall u64_ok l -> 0 <= i < Zlength l -> u64_ok (Znth i l).
Proof. intros. apply Forall_Znth; auto. Qed.

Lemma tc_byte: forall b, byte_ok b -> tc_val tuchar (Vint (Int.repr b)).
Proof. intros. unfold byte_ok in H. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. Qed.

Lemma Znth_bytes_val: forall (d: Inhabitant val) bytes i, 0 <= i < Zlength bytes ->
  @Znth val d i (bytes_val bytes) = Vint (Int.repr (Znth i bytes)).
Proof. intros. unfold bytes_val. rewrite (@Znth_map Z _ val d) by lia. reflexivity. Qed.

Lemma upd_prefix: forall (cur: list Z) (rest: list val) v n, Zlength cur < n -> Zlength rest = n ->
  upd_Znth (Zlength cur) (map vl cur ++ sublist (Zlength cur) n rest) (Vlong (Int64.repr v)) =
  map vl (cur ++ [v]) ++ sublist (Zlength cur + 1) n rest.
Proof. intros. unfold vl. list_solve. Qed.

Lemma upd_copy: forall (r state: list Z) w, Zlength r = 16 -> Zlength state = 12 -> 0 <= w < 12 ->
  upd_Znth w (map vl (sublist 3 (3 + w) r) ++ sublist w 12 (map vl state)) (vl (Znth (w + 3) r)) =
  map vl (sublist 3 (3 + (w + 1)) r) ++ sublist (w + 1) 12 (map vl state).
Proof. intros. list_solve. Qed.

Lemma nmi_store: forall nmi count p,
  upd_Znth count (map vl nmi) (Vlong (Int64.repr p)) = map vl (upd_Znth count nmi p).
Proof. intros. exact (upd_Znth_map vl count nmi p). Qed.

Lemma byte_ok_u64: forall b, byte_ok b -> u64_ok b.
Proof. unfold byte_ok, u64_ok. intros. rep_lia. Qed.

(* The packing of an NMI record: bytes pos .. pos + k - 1 of the span, little-endian. *)
Definition packk (bytes: list Z) (pos: Z) (k: nat) : Z :=
  fold_right Z.lor 0 (map (fun b => Z.shiftl (Znth (pos + Z.of_nat b) bytes) (8 * Z.of_nat b)) (seq 0 k)).

Lemma pack6_packk: forall bytes pos, pack6 bytes pos = packk bytes pos 6.
Proof. reflexivity. Qed.

Lemma fold_lor_last: forall l y, fold_right Z.lor y l = Z.lor (fold_right Z.lor 0 l) y.
Proof.
  induction l as [ | a l IH]; intros y; simpl.
  - reflexivity.
  - rewrite IH. rewrite Z.lor_assoc. reflexivity.
Qed.

Lemma packk_S: forall bytes pos k,
  packk bytes pos (S k) = Z.lor (packk bytes pos k) (Z.shiftl (Znth (pos + Z.of_nat k) bytes) (8 * Z.of_nat k)).
Proof.
  intros. unfold packk. rewrite seq_S, map_app, fold_right_app. simpl. rewrite Z.lor_0_r. apply fold_lor_last.
Qed.

Lemma packk_succ: forall bytes pos k, 0 <= k ->
  packk bytes pos (Z.to_nat (k + 1)) = Z.lor (packk bytes pos (Z.to_nat k)) (Z.shiftl (Znth (pos + k) bytes) (8 * k)).
Proof.
  intros. rewrite Z2Nat.inj_add, Nat.add_1_r, packk_S by lia. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma pack_step64: forall p b s, 0 <= b <= Int64.max_unsigned -> 0 <= s < 64 ->
  Int64.or (Int64.repr p) (Int64.shl (Int64.repr b) (Int64.repr s)) = Int64.repr (Z.lor p (Z.shiftl b s)).
Proof.
  intros. unfold Int64.shl. rewrite !Int64.unsigned_repr by rep_lia. apply or64_repr.
Qed.

(* ---------- the argument checks ---------- *)

Lemma if_false_eq: forall {A} (a b: A), (if false then a else b) = b.
Proof. reflexivity. Qed.

Lemma neg_length_ok: forall l, 0 <= l -> ((l =? 0) || (65492 <? l)) = negb (length_ok l).
Proof.
  intros. unfold length_ok, MAX_LENGTH.
  destruct (Z.eqb_spec l 0); destruct (Z.ltb_spec 65492 l); destruct (Z.ltb_spec 0 l);
    destruct (Z.leb_spec l (65536 - 44)); simpl; auto; lia.
Qed.

Lemma invalid_out_null: forall e o l, invalid_call e o nullval l = true.
Proof. intros. unfold invalid_call. rewrite isnull_null. reflexivity. Qed.

Lemma invalid_chain: forall e o out l, out <> nullval -> 0 <= l ->
  invalid_call e o out l = (isnull e || isnull o || (l =? 0) || (65492 <? l)).
Proof.
  intros. unfold invalid_call. rewrite isnull_nonnull by auto. rewrite <- neg_length_ok by auto.
  rewrite orb_false_l, orb_assoc. reflexivity.
Qed.

Lemma valid_ok: forall e o out l, invalid_call e o out l = false ->
  e <> nullval /\ o <> nullval /\ out <> nullval /\ length_ok l = true.
Proof.
  unfold invalid_call. intros. apply orb_false_iff in H as [H H3]. apply orb_false_iff in H as [H H2].
  apply orb_false_iff in H as [H1 H0]. apply negb_false_iff in H3. apply isnull_false in H0, H1, H2. auto.
Qed.

Lemma shift_ok: forall k, 0 <= k < 6 -> Int64.Z_mod_modulus (8 * Int64.Z_mod_modulus k) < 64.
Proof.
  intros. rewrite !Int64.Z_mod_modulus_eq. rewrite (Z.mod_small k) by rep_lia. rewrite Z.mod_small by rep_lia. lia.
Qed.

Lemma pack_goal: forall bytes pos k, 0 <= k < 6 -> 0 <= Znth (pos + k) bytes <= 255 ->
  vl (packk bytes pos (Z.to_nat (k + 1))) =
  Vlong (Int64.or (Int64.repr (packk bytes pos (Z.to_nat k)))
          (Int64.shl (Int64.repr (Int.unsigned (Int.repr (Znth (pos + k) bytes))))
             (Int64.repr (Int.unsigned (Int.repr 8) * k)))).
Proof.
  intros. rewrite packk_succ by lia. rewrite !Int.unsigned_repr by rep_lia. unfold vl. f_equal.
  symmetry. apply pack_step64; rep_lia.
Qed.

(* ---------- the model, one answer at a time ---------- *)

Lemma list_eqb_refl: forall l, list_eqb l l = true.
Proof.
  intros. unfold list_eqb. rewrite Z.eqb_refl. simpl.
  induction l as [ | a l IH]; simpl; [ reflexivity | rewrite Z.eqb_refl; exact IH ].
Qed.

Lemma call_eqb_refl: forall c, call_eqb c c = true.
Proof. destruct c; simpl; rewrite ?list_eqb_refl, ?Z.eqb_refl; reflexivity. Qed.

Lemma run_app: forall x h p p' rest, run x p h = Some p' -> run x p (h ++ rest) = run x p' rest.
Proof.
  induction h as [ | [c v] h IH]; intros p p' rest H.
  - simpl in H. inv H. reflexivity.
  - simpl in H |- *. destruct p as [s | o]; [ | discriminate ].
    destruct (call_eqb c (expected x s)); [ eapply IH; eauto | discriminate ].
Qed.

Lemma run_snoc: forall x h s v, run x (start x) h = Some (Go s) ->
  run x (start x) (h ++ [(expected x s, v)]) = Some (step x s v).
Proof. intros. rewrite (run_app _ _ _ _ _ H). simpl. rewrite call_eqb_refl. reflexivity. Qed.

Lemma next_call_go: forall x h s, run x (start x) h = Some (Go s) -> next_call x h = Some (expected x s).
Proof. intros. unfold next_call. rewrite H. reflexivity. Qed.

Lemma consume_ret: forall x h o, run x (start x) h = Some (Return o) -> consume x h = Some o.
Proof. intros. unfold consume. rewrite H. reflexivity. Qed.

Lemma run_start: forall bytes ob, length_ok (Zlength bytes) = true ->
  run (bytes, ob) (start (bytes, ob)) nil = Some (Go (Stream 0 initial_state nil)).
Proof. intros. unfold start. simpl fst. rewrite H. reflexivity. Qed.

(* ---------- the byte stream ---------- *)

(* After the 16 answers r of byte i. *)
Definition stream_end (bytes: list Z) (i: Z) (r: list Z) : progress :=
  let n := Zlength bytes in
  let offset := 44 + i in
  if negb (Znth 0 r =? 1) then Return (reject 3 0 offset)
  else if Znth 1 r =? 2 then Return (reject 2 (Znth 2 r) offset)
  else if negb (Znth 1 r =? (if i + 1 =? n then 3 else 1)) || negb (Znth 2 r =? 0) ||
          negb (Znth 3 r =? offset + 1) || negb (Znth 15 r =? Znth i bytes)
  then Return (reject 3 0 offset)
  else if i + 1 =? n then after_stream bytes r (sublist 3 15 r) else Go (Stream (i + 1) (sublist 3 15 r) nil).

(* After the answers cur of byte i. *)
Definition stream_at (bytes: list Z) (i: Z) (state cur: list Z) : progress :=
  if Zlength cur <? 16 then Go (Stream i state cur) else stream_end bytes i cur.

Lemma stream_at_go: forall bytes i state cur, Zlength cur < 16 -> stream_at bytes i state cur = Go (Stream i state cur).
Proof. intros. unfold stream_at. rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity. Qed.

Lemma stream_at_end: forall bytes i state cur, Zlength cur = 16 -> stream_at bytes i state cur = stream_end bytes i cur.
Proof. intros. unfold stream_at. rewrite H. reflexivity. Qed.

Lemma stream_call: forall bytes ob h i state cur,
  run (bytes, ob) (start (bytes, ob)) h = Some (stream_at bytes i state cur) -> Zlength cur < 16 ->
  next_call (bytes, ob) h =
    Some (Step state (44 + Zlength bytes) (o_executing ob) (44 + i) (Znth i bytes) (Zlength cur)).
Proof.
  intros. rewrite stream_at_go in H by auto. rewrite (next_call_go _ _ _ H). reflexivity.
Qed.

Lemma stream_answer: forall bytes ob h i state cur v,
  run (bytes, ob) (start (bytes, ob)) h = Some (stream_at bytes i state cur) -> Zlength cur < 16 ->
  run (bytes, ob) (start (bytes, ob))
    (h ++ [(Step state (44 + Zlength bytes) (o_executing ob) (44 + i) (Znth i bytes) (Zlength cur), v)]) =
  Some (stream_at bytes i state (cur ++ [v])).
Proof.
  intros. rewrite stream_at_go in H by auto. exact (run_snoc (bytes, ob) h (Stream i state cur) v H).
Qed.

Definition se_bad_cond (bytes: list Z) (i: Z) (r: list Z) : bool :=
  negb (Znth 1 r =? (if i + 1 =? Zlength bytes then 3 else 1)) || negb (Znth 2 r =? 0) ||
  negb (Znth 3 r =? 44 + i + 1) || negb (Znth 15 r =? Znth i bytes).

Lemma se_r0: forall bytes i r, Znth 0 r <> 1 -> stream_end bytes i r = Return (reject 3 0 (44 + i)).
Proof. intros. unfold stream_end. cbv zeta. rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity. Qed.

Lemma se_r1: forall bytes i r, Znth 0 r = 1 -> Znth 1 r = 2 -> stream_end bytes i r = Return (reject 2 (Znth 2 r) (44 + i)).
Proof. intros. unfold stream_end. cbv zeta. rewrite H, H0. reflexivity. Qed.

Lemma se_bad: forall bytes i r, Znth 0 r = 1 -> Znth 1 r <> 2 -> se_bad_cond bytes i r = true ->
  stream_end bytes i r = Return (reject 3 0 (44 + i)).
Proof.
  intros. unfold se_bad_cond in H1. unfold stream_end. cbv zeta. rewrite H, (proj2 (Z.eqb_neq _ _) H0), H1.
  reflexivity.
Qed.

Lemma se_ok: forall bytes i r, Znth 0 r = 1 -> Znth 1 r <> 2 -> se_bad_cond bytes i r = false ->
  stream_end bytes i r =
    if i + 1 =? Zlength bytes then after_stream bytes r (sublist 3 15 r) else Go (Stream (i + 1) (sublist 3 15 r) nil).
Proof.
  intros. unfold se_bad_cond in H1. unfold stream_end. cbv zeta. rewrite H, (proj2 (Z.eqb_neq _ _) H0), H1.
  reflexivity.
Qed.

Lemma se_next: forall bytes i r, 0 <= i < Zlength bytes ->
  (if i + 1 =? Zlength bytes then after_stream bytes r (sublist 3 15 r) else Go (Stream (i + 1) (sublist 3 15 r) nil)) =
  (if i + 1 <? Zlength bytes then Go (Stream (i + 1) (sublist 3 15 r) nil) else after_stream bytes r (sublist 3 15 r)).
Proof.
  intros. destruct (Z.eqb_spec (i + 1) (Zlength bytes)); destruct (Z.ltb_spec (i + 1) (Zlength bytes));
    auto; lia.
Qed.

(* ---------- the NMI policy ---------- *)

Definition policy_end (last state p: list Z) : progress :=
  let off := Znth 0 state in
  if negb (Znth 0 p =? 1) || (1 <? Znth 3 p) || (4 <? Znth 4 p) then Return (reject 3 0 off)
  else if negb (Znth 1 p =? 1) then Return (reject 5 (Znth 2 p) off)
  else if negb (Znth 2 p =? 0) || negb (Znth 3 p =? 1) || negb (Znth 4 p =? 4) then Return (reject 3 0 off)
  else Go (Bound last state nil).

Definition policy_at (last state: list Z) (count: Z) (nmi cur: list Z) : progress :=
  if Zlength cur <? 5 then Go (Policy last state count nmi cur) else policy_end last state cur.

Lemma policy_at_go: forall last state count nmi cur, Zlength cur < 5 ->
  policy_at last state count nmi cur = Go (Policy last state count nmi cur).
Proof. intros. unfold policy_at. rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity. Qed.

Lemma policy_at_end: forall last state count nmi cur, Zlength cur = 5 ->
  policy_at last state count nmi cur = policy_end last state cur.
Proof. intros. unfold policy_at. rewrite H. reflexivity. Qed.

Lemma policy_call: forall bytes ob h last state count nmi cur,
  run (bytes, ob) (start (bytes, ob)) h = Some (policy_at last state count nmi cur) -> Zlength cur < 5 ->
  next_call (bytes, ob) h = Some (Nmi count nmi (o_routing ob) (Zlength cur)).
Proof.
  intros. rewrite policy_at_go in H by auto. rewrite (next_call_go _ _ _ H). reflexivity.
Qed.

Lemma policy_answer: forall bytes ob h last state count nmi cur v,
  run (bytes, ob) (start (bytes, ob)) h = Some (policy_at last state count nmi cur) -> Zlength cur < 5 ->
  run (bytes, ob) (start (bytes, ob)) (h ++ [(Nmi count nmi (o_routing ob) (Zlength cur), v)]) =
  Some (policy_at last state count nmi (cur ++ [v])).
Proof.
  intros. rewrite policy_at_go in H by auto. exact (run_snoc (bytes, ob) h (Policy last state count nmi cur) v H).
Qed.

Definition pe_c1 (p: list Z) : bool := negb (Znth 0 p =? 1) || (1 <? Znth 3 p) || (4 <? Znth 4 p).
Definition pe_c3 (p: list Z) : bool := negb (Znth 2 p =? 0) || negb (Znth 3 p =? 1) || negb (Znth 4 p =? 4).

Lemma pe_1: forall last state p, pe_c1 p = true -> policy_end last state p = Return (reject 3 0 (Znth 0 state)).
Proof. intros. unfold pe_c1 in H. unfold policy_end. cbv zeta. rewrite H. reflexivity. Qed.

Lemma pe_2: forall last state p, pe_c1 p = false -> Znth 1 p <> 1 ->
  policy_end last state p = Return (reject 5 (Znth 2 p) (Znth 0 state)).
Proof. intros. unfold pe_c1 in H. unfold policy_end. cbv zeta. rewrite H, (proj2 (Z.eqb_neq _ _) H0). reflexivity. Qed.

Lemma pe_3: forall last state p, pe_c1 p = false -> Znth 1 p = 1 -> pe_c3 p = true ->
  policy_end last state p = Return (reject 3 0 (Znth 0 state)).
Proof.
  intros. unfold pe_c1, pe_c3 in *. unfold policy_end. cbv zeta. rewrite H, H0, H1. reflexivity.
Qed.

Lemma pe_ok: forall last state p, pe_c1 p = false -> Znth 1 p = 1 -> pe_c3 p = false ->
  policy_end last state p = Go (Bound last state nil).
Proof.
  intros. unfold pe_c1, pe_c3 in *. unfold policy_end. cbv zeta. rewrite H, H0, H1. reflexivity.
Qed.

(* ---------- the finish ---------- *)

Definition bound_end (ob: observation) (state b: list Z) : progress :=
  let off := Znth 0 state in
  if negb (Znth 0 b =? 1) || negb (Znth 5 b =? 0) then Return (reject 3 0 off)
  else if (Znth 1 b =? 2) || (Znth 1 b =? 5) then Return (reject 4 (Znth 2 b) off)
  else if negb (Znth 1 b =? 1) || negb (Znth 2 b =? o_executing ob) || negb (Znth 3 b =? Znth 6 state) ||
          negb (Znth 4 b =? o_apic_base ob)
  then Return (reject 3 0 off)
  else Return (0, 0, off, Znth 2 b, Znth 3 b, Znth 4 b).

Definition bound_at (ob: observation) (last state cur: list Z) : progress :=
  if Zlength cur <? 6 then Go (Bound last state cur) else bound_end ob state cur.

Lemma bound_at_nil: forall ob last state, bound_at ob last state nil = Go (Bound last state nil).
Proof. reflexivity. Qed.

Lemma bound_at_go: forall ob last state cur, Zlength cur < 6 -> bound_at ob last state cur = Go (Bound last state cur).
Proof. intros. unfold bound_at. rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity. Qed.

Lemma bound_at_end: forall ob last state cur, Zlength cur = 6 -> bound_at ob last state cur = bound_end ob state cur.
Proof. intros. unfold bound_at. rewrite H. reflexivity. Qed.

Lemma bound_call: forall bytes ob h last state cur,
  run (bytes, ob) (start (bytes, ob)) h = Some (bound_at ob last state cur) -> Zlength cur < 6 ->
  next_call (bytes, ob) h =
    Some (Finish (Znth 1 last) (Znth 2 last) state (44 + Zlength bytes) (o_executing ob) (o_cpuid_edx ob)
                 (o_available ob) (o_apic_base ob) (o_sample_id ob) (Zlength cur)).
Proof.
  intros. rewrite bound_at_go in H by auto. rewrite (next_call_go _ _ _ H). reflexivity.
Qed.

Lemma bound_answer: forall bytes ob h last state cur v,
  run (bytes, ob) (start (bytes, ob)) h = Some (bound_at ob last state cur) -> Zlength cur < 6 ->
  run (bytes, ob) (start (bytes, ob))
    (h ++ [(Finish (Znth 1 last) (Znth 2 last) state (44 + Zlength bytes) (o_executing ob) (o_cpuid_edx ob)
                   (o_available ob) (o_apic_base ob) (o_sample_id ob) (Zlength cur), v)]) =
  Some (bound_at ob last state (cur ++ [v])).
Proof.
  intros. rewrite bound_at_go in H by auto. exact (run_snoc (bytes, ob) h (Bound last state cur) v H).
Qed.

Definition be_c1 (b: list Z) : bool := negb (Znth 0 b =? 1) || negb (Znth 5 b =? 0).
Definition be_c2 (b: list Z) : bool := (Znth 1 b =? 2) || (Znth 1 b =? 5).
Definition be_c3 (ob: observation) (state b: list Z) : bool :=
  negb (Znth 1 b =? 1) || negb (Znth 2 b =? o_executing ob) || negb (Znth 3 b =? Znth 6 state) ||
  negb (Znth 4 b =? o_apic_base ob).

Lemma be_1: forall ob state b, be_c1 b = true -> bound_end ob state b = Return (reject 3 0 (Znth 0 state)).
Proof. intros. unfold be_c1 in H. unfold bound_end. cbv zeta. rewrite H. reflexivity. Qed.

Lemma be_2: forall ob state b, be_c1 b = false -> be_c2 b = true ->
  bound_end ob state b = Return (reject 4 (Znth 2 b) (Znth 0 state)).
Proof. intros. unfold be_c1, be_c2 in *. unfold bound_end. cbv zeta. rewrite H, H0. reflexivity. Qed.

Lemma be_3: forall ob state b, be_c1 b = false -> be_c2 b = false -> be_c3 ob state b = true ->
  bound_end ob state b = Return (reject 3 0 (Znth 0 state)).
Proof. intros. unfold be_c1, be_c2, be_c3 in *. unfold bound_end. cbv zeta. rewrite H, H0, H1. reflexivity. Qed.

Lemma be_ok: forall ob state b, be_c1 b = false -> be_c2 b = false -> be_c3 ob state b = false ->
  bound_end ob state b = Return (0, 0, Znth 0 state, Znth 2 b, Znth 3 b, Znth 4 b).
Proof. intros. unfold be_c1, be_c2, be_c3 in *. unfold bound_end. cbv zeta. rewrite H, H0, H1. reflexivity. Qed.

(* ---------- the record walk ---------- *)

Lemma walk_fuel: forall bytes f1 f2 pos count nmi,
  (Z.to_nat (Zlength bytes - pos) < f1)%nat -> (Z.to_nat (Zlength bytes - pos) < f2)%nat ->
  walk_records f1 bytes pos count nmi = walk_records f2 bytes pos count nmi.
Proof.
  intros bytes f1. induction f1 as [ | f1 IH]; intros f2 pos count nmi H1 H2; [ lia | ].
  destruct f2 as [ | f2]; [ lia | ].
  cbn [walk_records].
  destruct (Zlength bytes <=? pos) eqn:E1; [ reflexivity | ].
  destruct (Zlength bytes - pos <? 2) eqn:E2; [ reflexivity | ].
  destruct ((Znth (pos + 1) bytes <? 2) || (Zlength bytes - pos <? Znth (pos + 1) bytes))%bool eqn:E3;
    [ reflexivity | ].
  apply orb_false_iff in E3. destruct E3 as [E3 E4].
  apply Z.leb_gt in E1. apply Z.ltb_ge in E2, E3, E4.
  destruct (Znth pos bytes =? 4).
  - destruct (negb (Znth (pos + 1) bytes =? 6)); [ reflexivity | ]. apply IH; lia.
  - apply IH; lia.
Qed.

(* The walk from record offset pos, with the count and the packed NMI records so far, ends as `records`. *)
Definition walk_inv (bytes: list Z) (pos count: Z) (nmi: list Z) : Prop :=
  walk_records (S (Z.to_nat (Zlength bytes - pos))) bytes pos count nmi = records bytes.

Lemma walk_start: forall bytes, walk_inv bytes 0 0 [0; 0; 0; 0].
Proof. intros. unfold walk_inv, records. rewrite Z.sub_0_r. reflexivity. Qed.

Lemma walk_done: forall bytes pos count nmi, walk_inv bytes pos count nmi -> Zlength bytes <= pos ->
  records bytes = Some (count, nmi).
Proof.
  intros. unfold walk_inv in H. cbn [walk_records] in H. rewrite (proj2 (Z.leb_le _ _) H0) in H. cbn [negb] in H. auto.
Qed.

Lemma walk_short: forall bytes pos count nmi, walk_inv bytes pos count nmi -> pos < Zlength bytes ->
  Zlength bytes - pos < 2 -> records bytes = None.
Proof.
  intros. unfold walk_inv in H. cbn [walk_records] in H.
  rewrite (proj2 (Z.leb_gt _ _) H0), (proj2 (Z.ltb_lt _ _) H1) in H. cbn [negb] in H. auto.
Qed.

Lemma walk_badlen: forall bytes pos count nmi, walk_inv bytes pos count nmi -> pos < Zlength bytes ->
  2 <= Zlength bytes - pos ->
  (Znth (pos + 1) bytes < 2 \/ Zlength bytes - pos < Znth (pos + 1) bytes) -> records bytes = None.
Proof.
  intros. unfold walk_inv in H. cbn [walk_records] in H.
  rewrite (proj2 (Z.leb_gt _ _) H0), (proj2 (Z.ltb_ge _ _) H1) in H.
  destruct H2 as [H2 | H2];
    [ rewrite (proj2 (Z.ltb_lt _ _) H2) in H | rewrite (proj2 (Z.ltb_lt _ _) H2), orb_true_r in H ];
    cbn [orb] in H; auto.
Qed.

Lemma walk_unfold: forall bytes pos count nmi, walk_inv bytes pos count nmi -> pos < Zlength bytes ->
  2 <= Zlength bytes - pos -> 2 <= Znth (pos + 1) bytes <= Zlength bytes - pos ->
  records bytes =
    if Znth pos bytes =? 4 then
      if negb (Znth (pos + 1) bytes =? 6) then None
      else walk_records (Z.to_nat (Zlength bytes - pos)) bytes (pos + Znth (pos + 1) bytes) (count + 1)
             (if count <? 4 then upd_Znth count nmi (pack6 bytes pos) else nmi)
    else walk_records (Z.to_nat (Zlength bytes - pos)) bytes (pos + Znth (pos + 1) bytes) count nmi.
Proof.
  intros. unfold walk_inv in H. cbn [walk_records] in H.
  rewrite (proj2 (Z.leb_gt _ _) H0), (proj2 (Z.ltb_ge _ _) H1) in H.
  rewrite (proj2 (Z.ltb_ge _ _) (proj1 H2)), (proj2 (Z.ltb_ge _ _) (proj2 H2)) in H. cbn [orb] in H.
  rewrite <- H. reflexivity.
Qed.

Lemma walk_nmi_bad: forall bytes pos count nmi, walk_inv bytes pos count nmi -> pos < Zlength bytes ->
  2 <= Zlength bytes - pos -> 2 <= Znth (pos + 1) bytes <= Zlength bytes - pos ->
  Znth pos bytes = 4 -> Znth (pos + 1) bytes <> 6 -> records bytes = None.
Proof.
  intros. rewrite (walk_unfold bytes pos count nmi) by auto.
  rewrite H3, (proj2 (Z.eqb_neq _ _) H4). reflexivity.
Qed.

Lemma walk_nmi: forall bytes pos count nmi, walk_inv bytes pos count nmi -> pos < Zlength bytes ->
  2 <= Zlength bytes - pos -> 2 <= Znth (pos + 1) bytes <= Zlength bytes - pos ->
  Znth pos bytes = 4 -> Znth (pos + 1) bytes = 6 ->
  walk_inv bytes (pos + Znth (pos + 1) bytes) (count + 1)
    (if count <? 4 then upd_Znth count nmi (pack6 bytes pos) else nmi).
Proof.
  intros. unfold walk_inv. rewrite (walk_unfold bytes pos count nmi) by auto.
  rewrite H3, H4, !Z.eqb_refl. cbn [negb]. apply walk_fuel; lia.
Qed.

Lemma walk_other: forall bytes pos count nmi, walk_inv bytes pos count nmi -> pos < Zlength bytes ->
  2 <= Zlength bytes - pos -> 2 <= Znth (pos + 1) bytes <= Zlength bytes - pos ->
  Znth pos bytes <> 4 -> walk_inv bytes (pos + Znth (pos + 1) bytes) count nmi.
Proof.
  intros. unfold walk_inv. rewrite (walk_unfold bytes pos count nmi) by auto.
  rewrite (proj2 (Z.eqb_neq _ _) H3). apply walk_fuel; lia.
Qed.

(* ---------- after the stream ---------- *)

Lemma after_none: forall bytes last state, records bytes = None ->
  after_stream bytes last state = Return (reject 3 0 (Znth 0 state)).
Proof. intros. unfold after_stream. rewrite H. reflexivity. Qed.

Lemma after_some: forall bytes last state count nmi, records bytes = Some (count, nmi) ->
  after_stream bytes last state = Go (Policy last state count nmi nil).
Proof. intros. unfold after_stream. rewrite H. reflexivity. Qed.

(* ---------- bounds ---------- *)

Ltac u64 :=
  first [ assumption
        | apply u64_ok_Znth; [ assumption | lia ]
        | apply byte_ok_u64; assumption
        | apply byte_ok_u64; apply Forall_Znth; auto; lia
        | unfold u64_ok; rep_lia
        | unfold u64_ok; match goal with |- context [if ?c then _ else _] => destruct c end; rep_lia ].

Ltac rng :=
  first [ rep_lia | match goal with |- context [if ?c then _ else _] => destruct c end; rep_lia
        | match goal with H: byte_ok ?x |- context [?x] => unfold byte_ok in H; rep_lia end ].

Ltac z64 :=
  repeat match goal with
  | H: context [Int64.sub (Int64.repr ?a) (Int64.repr ?b)] |- _ => rewrite (sub64_repr a b) in H
  | H: context [Int64.add (Int64.repr ?a) (Int64.repr ?b)] |- _ => rewrite (add64_repr a b) in H
  | H: context [Int64.mul (Int64.repr ?a) (Int64.repr ?b)] |- _ => rewrite (mul64_repr a b) in H
  | H: context [Int.unsigned (Int.repr ?x)] |- _ => rewrite (Int.unsigned_repr x) in H by rng
  | H: context [Int64.unsigned (Int64.repr ?x)] |- _ => rewrite (Int64.unsigned_repr x) in H by rng
  | H: context [Int64.zero] |- _ => change Int64.zero with (Int64.repr 0) in H
  | H: Int64.repr _ <> Int64.repr _ |- _ => apply repr64_neq in H
  | H: Int64.eq (Int64.repr ?a) (Int64.repr ?b) = true |- _ =>
      rewrite (eq64_repr a b) in H by u64; apply Z.eqb_eq in H
  | H: Int64.eq (Int64.repr ?a) (Int64.repr ?b) = false |- _ =>
      rewrite (eq64_repr a b) in H by u64; apply Z.eqb_neq in H
  | H: Int64.ltu (Int64.repr ?a) (Int64.repr ?b) = true |- _ =>
      rewrite (ltu64_repr a b) in H by u64; apply Z.ltb_lt in H
  | H: Int64.ltu (Int64.repr ?a) (Int64.repr ?b) = false |- _ =>
      rewrite (ltu64_repr a b) in H by u64; apply Z.ltb_ge in H
  | H: Int64.repr ?a = Int64.repr ?b |- _ => apply repr64_inj in H; [ | u64 | u64 ]
  | H: Int.repr _ <> Int.repr _ |- _ => apply repr32_neq in H
  | H: Int.eq (Int.repr ?a) (Int.repr ?b) = true |- _ => rewrite (eq32_repr a b) in H by rng; apply Z.eqb_eq in H
  | H: Int.eq (Int.repr ?a) (Int.repr ?b) = false |- _ => rewrite (eq32_repr a b) in H by rng; apply Z.eqb_neq in H
  | H: Int.repr ?a = Int.repr ?b |- _ => apply repr_inj_unsigned in H; [ | rng | rng ]
  end.

Ltac zrw := repeat match goal with
  | H: ?a = ?b |- context [?a =? ?b] => rewrite (proj2 (Z.eqb_eq a b) H)
  | H: ?a <> ?b |- context [?a =? ?b] => rewrite (proj2 (Z.eqb_neq a b) H)
  | H: ?a < ?b |- context [?a <? ?b] => rewrite (proj2 (Z.ltb_lt a b) H)
  | H: ?b <= ?a |- context [?a <? ?b] => rewrite (proj2 (Z.ltb_ge a b) H)
  | H: ?a >= ?b |- context [?a <? ?b] => rewrite (proj2 (Z.ltb_ge a b) (Z.ge_le _ _ H))
  | H: ?b > ?a |- context [?a <? ?b] => rewrite (proj2 (Z.ltb_lt a b) (Z.gt_lt _ _ H))
  | H: ?c = true |- context [?c] => lazymatch c with true => fail | false => fail | _ => rewrite H end
  | H: ?c = false |- context [?c] => lazymatch c with true => fail | false => fail | _ => rewrite H end
  end.

Ltac bnorm :=
  rewrite ?bool2val_b2z; unfold Int64.cmpu; change Int64.zero with (Int64.repr 0);
  rewrite ?sub64_repr, ?add64_repr, ?mul64_repr;
  rewrite ?eq64_repr, ?ltu64_repr by u64.

Ltac bclose :=
  repeat match goal with |- context [?a =? ?b] => destruct (Z.eqb_spec a b) end;
  repeat match goal with |- context [?a <? ?b] => destruct (Z.ltb_spec a b) end;
  first [ reflexivity | exfalso; lia ].
