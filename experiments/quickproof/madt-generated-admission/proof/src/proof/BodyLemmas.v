(* Lemmas for the body proofs of include/madt_generated_admission.h (EnvelopeProof.v, EntriesProof.v,
   ResultProof.v, AdmissionProof.v): the word arithmetic of the C expressions, the arrays one store at a time, and
   the model of Defs.v one answer at a time, phase by phase (the envelope, the entry stream, the result). *)
Require Import VST.floyd.proofauto.
Require Import LeanosMadtAdmission.madt_admission.code.
Require Import LeanosMadtAdmission.proof.Defs.
Require Import LeanosMadtAdmission.proof.MgaSpecs.
#[local] Existing Instance MgaSpecs.CS.
Local Open Scope Z_scope.

(* ---------- booleans as C ints ---------- *)

Definition b2z (b: bool) : Z := if b then 1 else 0.

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

(* ---------- words ---------- *)

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

Lemma byte_ok_u64: forall b, byte_ok b -> u64_ok b.
Proof. unfold byte_ok, u64_ok. intros. rep_lia. Qed.

Lemma u32_ok_u64: forall b, u32_ok b -> u64_ok b.
Proof. unfold u32_ok, u64_ok. intros. rep_lia. Qed.

Lemma tc_byte: forall b, byte_ok b -> tc_val tuchar (Vint (Int.repr b)).
Proof. intros. unfold byte_ok in H. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. Qed.

Lemma Znth_bytes_val: forall (d: Inhabitant val) bytes i, 0 <= i < Zlength bytes ->
  @Znth val d i (bytes_val bytes) = Vint (Int.repr (Znth i bytes)).
Proof. intros. unfold bytes_val. rewrite (@Znth_map Z _ val d) by lia. reflexivity. Qed.

(* The or of 64-bit words is 0 exactly when each is. *)
Lemma or64_zero: forall a b, Int64.or a b = Int64.zero <-> a = Int64.zero /\ b = Int64.zero.
Proof.
  intros a b. split.
  - intros H.
    assert (B: forall i, 0 <= i < Int64.zwordsize -> Int64.testbit a i = false /\ Int64.testbit b i = false).
    { intros i Hi. assert (E := f_equal (fun z => Int64.testbit z i) H). cbv beta in E.
      rewrite Int64.bits_or in E by auto. rewrite Int64.bits_zero in E.
      apply orb_false_iff in E. exact E. }
    split; apply Int64.same_bits_eq; intros i Hi; rewrite Int64.bits_zero; apply B; auto.
  - intros [-> ->]. apply Int64.or_zero.
Qed.

Lemma repr64_zero: forall a, u64_ok a -> (Int64.repr a = Int64.zero <-> a = 0).
Proof.
  intros. split; intros E.
  - apply repr64_inj; [ assumption | unfold u64_ok; rep_lia | exact E ].
  - subst. reflexivity.
Qed.

Lemma or4_zero: forall a b c d, u64_ok a -> u64_ok b -> u64_ok c -> u64_ok d ->
  (Int64.or (Int64.or (Int64.or (Int64.repr a) (Int64.repr b)) (Int64.repr c)) (Int64.repr d) = Int64.zero <->
   ((a =? 0) && (b =? 0) && (c =? 0) && (d =? 0))%bool = true).
Proof.
  intros. rewrite !or64_zero, !repr64_zero by auto. rewrite !andb_true_iff, !Z.eqb_eq. tauto.
Qed.

(* ---------- arrays ---------- *)

(* The answers so far, then the cells not yet written. *)
Lemma upd_answers: forall (cur: list Z) v n, Zlength cur < n ->
  upd_Znth (Zlength cur) (map vl cur ++ Zrepeat Vundef (n - Zlength cur)) (Vlong (Int64.repr v)) =
  map vl (cur ++ [v]) ++ Zrepeat Vundef (n - (Zlength cur + 1)).
Proof. intros. unfold vl. list_solve. Qed.

(* The entries' copy state[word] = answer[word + 3]. *)
Lemma upd_copy: forall (a st: list Z) w, Zlength a = 16 -> Zlength st = 12 -> 0 <= w < 12 ->
  upd_Znth w (map vl (sublist 3 (3 + w) a) ++ sublist w 12 (map vl st)) (vl (Znth (w + 3) a)) =
  map vl (sublist 3 (3 + (w + 1)) a) ++ sublist (w + 1) 12 (map vl st).
Proof. intros. list_solve. Qed.

(* ---------- the envelope ---------- *)

Lemma env_go: forall x i st cur, Zlength cur < 7 -> envelope_collect x i st cur = Go (ExpectEnvelope i st cur).
Proof. intros. unfold envelope_collect. rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity. Qed.

Lemma env_call: forall x h i st cur,
  run x (start x) h = Some (envelope_collect x i st cur) -> Zlength cur < 7 ->
  next_call x h = Some (EnvelopeStep st (i_length x) i (Znth i (i_bytes x)) (terminal x i) (Zlength cur)).
Proof. intros. rewrite env_go in H by auto. rewrite (next_call_go _ _ _ H). reflexivity. Qed.

Lemma env_answer: forall x h i st cur v,
  run x (start x) h = Some (envelope_collect x i st cur) -> Zlength cur < 7 ->
  run x (start x) (h ++ [(EnvelopeStep st (i_length x) i (Znth i (i_bytes x)) (terminal x i) (Zlength cur), v)]) =
  Some (envelope_collect x i st (cur ++ [v])).
Proof. intros. rewrite env_go in H by auto. exact (run_snoc x _ h (ExpectEnvelope i st cur) v H). Qed.

Lemma env_reject: forall x i st a r, Zlength a = 7 -> envelope_check x i a = r -> r <> S_OK ->
  envelope_collect x i st a = envelope_end x r.
Proof.
  intros. unfold envelope_collect. rewrite H. cbn zeta. rewrite H0.
  unfold envelope_end. rewrite (proj2 (Z.eqb_neq _ _) H1). reflexivity.
Qed.

Lemma env_accept: forall x i st a, Zlength a = 7 -> envelope_check x i a = S_OK ->
  envelope_collect x i st a = envelope_from x (i + 1) [Znth 3 a; Znth 4 a; Znth 5 a].
Proof. intros. unfold envelope_collect. rewrite H. cbn zeta. rewrite H0. reflexivity. Qed.

Lemma env_from_go: forall x i st, i <> i_length x -> envelope_from x i st = envelope_collect x i st nil.
Proof. intros. unfold envelope_from. rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity. Qed.

Lemma env_from_done: forall x st, envelope_from x (i_length x) st = envelope_end x (envelope_final x st).
Proof. intros. unfold envelope_from. rewrite Z.eqb_refl. reflexivity. Qed.

(* ---------- the entry stream ---------- *)

Lemma ent_go: forall x k st cur, Zlength cur < 16 -> entries_collect x k st cur = Go (ExpectEntries k st cur).
Proof. intros. unfold entries_collect. rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity. Qed.

Lemma ent_call: forall x h k st cur,
  run x (start x) h = Some (entries_collect x k st cur) -> Zlength cur < 16 ->
  next_call x h = Some (EntryStep st (i_length x) (i_executing x) k (Znth k (i_bytes x)) (Zlength cur)).
Proof. intros. rewrite ent_go in H by auto. rewrite (next_call_go _ _ _ H). reflexivity. Qed.

Lemma ent_answer: forall x h k st cur v,
  run x (start x) h = Some (entries_collect x k st cur) -> Zlength cur < 16 ->
  run x (start x) (h ++ [(EntryStep st (i_length x) (i_executing x) k (Znth k (i_bytes x)) (Zlength cur), v)]) =
  Some (entries_collect x k st (cur ++ [v])).
Proof. intros. rewrite ent_go in H by auto. exact (run_snoc x _ h (ExpectEntries k st cur) v H). Qed.

Lemma ent_end_reject: forall x r id, r <> S_OK -> entries_end x r id = Return (r, None).
Proof. intros. unfold entries_end. rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity. Qed.

Lemma ent_reject: forall x k st a r, Zlength a = 16 -> entries_check x k a = r -> r <> S_OK ->
  entries_collect x k st a = entries_end x r 0.
Proof.
  intros. unfold entries_collect. rewrite H. cbn zeta. rewrite H0.
  rewrite ent_end_reject by auto. rewrite (proj2 (Z.eqb_neq _ _) H1). reflexivity.
Qed.

Lemma ent_accept: forall x k st a, Zlength a = 16 -> entries_check x k a = S_OK ->
  entries_collect x k st a = entries_from x (k + 1) (sublist 3 15 a).
Proof. intros. unfold entries_collect. rewrite H. cbn zeta. rewrite H0. reflexivity. Qed.

Lemma ent_from_go: forall x k st, k <> i_length x -> entries_from x k st = entries_collect x k st nil.
Proof. intros. unfold entries_from. rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity. Qed.

Lemma ent_from_done: forall x st,
  entries_from x (i_length x) st = entries_end x (entries_final x st) (Znth 7 st).
Proof. intros. unfold entries_from. rewrite Z.eqb_refl. reflexivity. Qed.

Lemma ent_final_reject: forall x st r, entries_final x st = r -> r <> S_OK ->
  entries_end x (entries_final x st) (Znth 7 st) = entries_end x r 0.
Proof. intros. rewrite H, !ent_end_reject by auto. reflexivity. Qed.

Lemma rec_demorgan: forall a b c d e: bool,
  negb (a && b && c && d && e) = (negb a || negb b || negb c || negb d || negb e)%bool.
Proof. destruct a, b, c, d, e; reflexivity. Qed.

Lemma begin_reject: forall x, ((i_length x <=? 44) || (255 <? i_executing x))%bool = true ->
  begin_entries x = entries_end x S_ENTRIES_BOUNDS 0.
Proof. intros. unfold begin_entries. rewrite H. reflexivity. Qed.

Lemma begin_accept: forall x, ((i_length x <=? 44) || (255 <? i_executing x))%bool = false ->
  begin_entries x = entries_from x 44 initial_entries.
Proof. intros. unfold begin_entries. rewrite H. reflexivity. Qed.

(* ---------- the result ---------- *)

Lemma res_go: forall args cur, Zlength cur < 4 -> result_collect args cur = Go (ExpectResult args cur).
Proof. intros. unfold result_collect. rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity. Qed.

Lemma res_call: forall x h args cur,
  run x (start x) h = Some (result_collect args cur) -> Zlength cur < 4 ->
  next_call x h = Some (ResultQuery args (Zlength cur)).
Proof. intros. rewrite res_go in H by auto. rewrite (next_call_go _ _ _ H). reflexivity. Qed.

Lemma res_answer: forall x h args cur v,
  run x (start x) h = Some (result_collect args cur) -> Zlength cur < 4 ->
  run x (start x) (h ++ [(ResultQuery args (Zlength cur), v)]) = Some (result_collect args (cur ++ [v])).
Proof. intros. rewrite res_go in H by auto. exact (run_snoc x _ h (ExpectResult args cur) v H). Qed.

Lemma res_reject: forall args a r, Zlength a = 4 -> result_check args a = r -> r <> S_OK ->
  result_collect args a = result_end r 0.
Proof.
  intros. unfold result_collect. rewrite H. cbn. rewrite H0.
  unfold result_end. rewrite (proj2 (Z.eqb_neq _ _) H1). reflexivity.
Qed.

Lemma res_accept: forall args a, Zlength a = 4 -> result_check args a = S_OK ->
  result_collect args a = result_end S_OK (Znth 3 a).
Proof. intros. unfold result_collect. rewrite H. cbn. rewrite H0. reflexivity. Qed.

(* The result's last check, as the C computes it. *)
Definition res_c1 (args a: list Z) : bool := negb (Znth 3 a <? 2 ^ 32) || negb (Znth 3 a =? Znth 8 args).
Definition res_c2 (args a: list Z) : bool := res_c1 args a || negb (Znth 3 a =? Znth 9 args).

(* ---------- tactics ---------- *)

Ltac u64 :=
  first [ assumption
        | apply u64_ok_Znth; [ assumption | lia ]
        | apply byte_ok_u64; assumption
        | apply byte_ok_u64; apply Forall_Znth; auto; lia
        | apply u32_ok_u64; assumption
        | unfold u64_ok; rep_lia
        | unfold u64_ok; match goal with |- context [if ?c then _ else _] => destruct c end; rep_lia
        | unfold u64_ok, u32_ok, byte_ok in *; rep_lia ].

Ltac rng :=
  first [ rep_lia | match goal with |- context [if ?c then _ else _] => destruct c end; rep_lia
        | match goal with |- 0 <= Znth ?i ?l <= Int64.max_unsigned =>
            apply (u64_ok_Znth l i); [ assumption | lia ] end
        | match goal with H: byte_ok ?x |- context [?x] => unfold byte_ok in H; rep_lia end
        | unfold u64_ok, u32_ok, byte_ok in *; rep_lia ].

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

(* After entailer!, the run equation and a u32_ok of a literal. *)
Ltac u32_split := try match goal with |- _ /\ u32_ok _ => split; [ | unfold u32_ok; rep_lia ] end.
