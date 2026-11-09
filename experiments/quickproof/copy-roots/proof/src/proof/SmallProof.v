(* Bodies of the small functions of patch/roots_unit.c: qotom_root_table_entry, qotom_root_phys_ok,
   qotom_root_phys_disjoint, qotom_root_protected_frame, qotom_root_source_ancestors, frame_window_pages,
   frame_window_geometry_ok, and the three forwarding wrappers roots_build, window_build, window_root_exact. *)
Require Import VST.floyd.proofauto.
Require Import LeanosRoots.roots.code.
Require Import LeanosRoots.proof.Defs.
Require Import LeanosRoots.proof.RootsSpecs.
#[local] Existing Instance RootsSpecs.CS.

(* ---------------------------------------------------------------------- *)
(* 64-bit words                                                           *)
(* ---------------------------------------------------------------------- *)

Lemma repr_mod64: forall x, Int64.repr (x mod W) = Int64.repr x.
Proof. intros. unfold W. rewrite <- Int64.unsigned_repr_eq. apply Int64.repr_unsigned. Qed.

Lemma eq64: forall x y, word_ok x -> word_ok y -> Int64.eq (Int64.repr x) (Int64.repr y) = (x =? y).
Proof.
  intros x y Hx Hy. unfold word_ok in *. unfold Int64.eq.
  rewrite !Int64.unsigned_repr by lia. destruct (zeq x y); symmetry; [ apply Z.eqb_eq | apply Z.eqb_neq ]; auto.
Qed.

Lemma ltu64: forall x y, word_ok x -> word_ok y -> Int64.ltu (Int64.repr x) (Int64.repr y) = (x <? y).
Proof.
  intros x y Hx Hy. unfold word_ok in *. unfold Int64.ltu.
  rewrite !Int64.unsigned_repr by lia. destruct (zlt x y); symmetry; [ apply Z.ltb_lt | apply Z.ltb_ge ]; lia.
Qed.

Lemma word_mod: forall x, word_ok (x mod W).
Proof. intros. unfold word_ok, W. pose proof (Z.mod_pos_bound x Int64.modulus ltac:(rep_lia)). rep_lia. Qed.

Lemma word_ones: forall x, word_ok x -> Z.land x (Z.ones 64) = x.
Proof.
  intros x Hx. unfold word_ok in Hx. rewrite Z.land_ones by lia. apply Z.mod_small.
  change (2 ^ 64) with (Int64.max_unsigned + 1). lia.
Qed.

Lemma word_land_ones: forall x, word_ok (Z.land x (Z.ones 64)).
Proof.
  intros x. rewrite Z.land_ones by lia. unfold word_ok.
  pose proof (Z.mod_pos_bound x (2 ^ 64) ltac:(lia)).
  change (2 ^ 64) with (Int64.max_unsigned + 1) in *. lia.
Qed.

Lemma land_word: forall x y, word_ok x -> word_ok (Z.land x y).
Proof.
  intros x y Hx. rewrite <- (word_ones x Hx).
  rewrite <- Z.land_assoc, (Z.land_comm (Z.ones 64)), Z.land_assoc. apply word_land_ones.
Qed.

Lemma lor_word: forall x y, word_ok x -> word_ok y -> word_ok (Z.lor x y).
Proof.
  intros x y Hx Hy. rewrite <- (word_ones x Hx), <- (word_ones y Hy).
  rewrite <- Z.land_lor_distr_l. apply word_land_ones.
Qed.

Lemma clear_accessed_word: forall x, word_ok x -> word_ok (clear_accessed x).
Proof. intros. unfold clear_accessed. apply land_word. auto. Qed.

Lemma table_entry_word: forall phys k, word_ok (table_entry phys k).
Proof. intros. unfold table_entry. apply lor_word; [ apply word_mod | unfold word_ok; rep_lia ]. Qed.

Lemma pd_entry_word: forall phys i, word_ok (pd_entry phys i).
Proof. intros. unfold pd_entry. destruct (i <? 8); [ apply table_entry_word | unfold word_ok; rep_lia ]. Qed.

Lemma not32: Int64.not (Int64.repr 32) = Int64.repr (Z.lnot 32).
Proof. apply Int64.same_if_eq. reflexivity. Qed.

Lemma clear_accessed_repr: forall x,
  Int64.and (Int64.repr x) (Int64.not (Int64.repr 32)) = Int64.repr (clear_accessed x).
Proof. intros. rewrite not32, and64_repr. reflexivity. Qed.

Lemma sizeof_root: sizeof (Tstruct _qotom_root_pages noattr) = ROOT_BYTES.
Proof. reflexivity. Qed.

(* phys_ok's a mod 4096 =? 0 is the code's (a & 4095u) == 0. *)
Lemma land4095: forall a, 0 <= a -> Z.land a 4095 = a mod 4096.
Proof. intros. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma repr64_inj: forall x y, word_ok x -> word_ok y -> Int64.repr x = Int64.repr y -> x = y.
Proof.
  intros x y Hx Hy E. unfold word_ok in *.
  rewrite <- (Int64.unsigned_repr x), <- (Int64.unsigned_repr y) by lia. rewrite E. reflexivity.
Qed.

Lemma cmpu_le64: forall x y, Int64.cmpu Cle x y = negb (Int64.ltu y x).
Proof. reflexivity. Qed.
Lemma cmpu_ge64: forall x y, Int64.cmpu Cge x y = negb (Int64.ltu x y).
Proof. reflexivity. Qed.
Lemma cmpu_eq64: forall x y, Int64.cmpu Ceq x y = Int64.eq x y.
Proof. reflexivity. Qed.

Lemma eq64m: forall x y, word_ok y -> Int64.eq (Int64.repr x) (Int64.repr y) = (x mod W =? y).
Proof.
  intros x y Hy. unfold word_ok in *. unfold Int64.eq, W.
  rewrite (Int64.unsigned_repr y) by lia. rewrite Int64.unsigned_repr_eq.
  destruct (zeq (x mod Int64.modulus) y); symmetry; [ apply Z.eqb_eq | apply Z.eqb_neq ]; auto.
Qed.

Lemma ltu64m: forall x y, word_ok y -> Int64.ltu (Int64.repr y) (Int64.repr x) = (y <? x mod W).
Proof.
  intros x y Hy. unfold word_ok in *. unfold Int64.ltu, W.
  rewrite (Int64.unsigned_repr y) by lia. rewrite Int64.unsigned_repr_eq.
  destruct (zlt y (x mod Int64.modulus)); symmetry; [ apply Z.ltb_lt | apply Z.ltb_ge ]; lia.
Qed.

(* A word_ok side condition. *)
Ltac wok := first [ assumption | apply word_mod | apply land_word; assumption | unfold word_ok; rep_lia ].

Lemma cmpu_lt64: forall x y, Int64.cmpu Clt x y = Int64.ltu x y.
Proof. reflexivity. Qed.
Lemma cmpu_ne64: forall x y, Int64.cmpu Cne x y = negb (Int64.eq x y).
Proof. reflexivity. Qed.

(* Close b2z b = bool2val b' once b and b' are the same test. *)
Ltac bfin :=
  unfold bool2val, b2z; repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity.

(* ---------------------------------------------------------------------- *)
(* Leaf functions                                                         *)
(* ---------------------------------------------------------------------- *)

Lemma body_qotom_root_table_entry : semax_body Vprog Gprog f_qotom_root_table_entry table_entry_spec.
Proof.
  start_function.
  forward.
  entailer!. unfold table_entry.
  rewrite <- !or64_repr. rewrite repr_mod64. reflexivity.
Qed.

Lemma body_qotom_root_phys_ok : semax_body Vprog Gprog f_qotom_root_phys_ok phys_ok_spec.
Proof.
  start_function.
  assert (Hm: 0 <= a mod 4096 < 4096) by (apply Z.mod_pos_bound; lia).
  forward_if (temp _t'1 (Vint (Int.repr (b2z (negb (a =? 0) && (a mod 4096 =? 0))%bool)))).
  { forward. entailer!.
    assert (a <> 0) by (intro; subst; contradiction).
    rewrite cmpu_eq64, land4095 by (unfold word_ok in H; lia).
    rewrite eq64 by (unfold word_ok; rep_lia).
    rewrite (proj2 (Z.eqb_neq a 0)) by lia. simpl negb.
    destruct (a mod 4096 =? 0); reflexivity. }
  { forward. entailer!.
    assert (a = 0) by (apply repr64_inj; auto; unfold word_ok; rep_lia). subst. reflexivity. }
  forward_if (temp _t'2 (Vint (Int.repr (b2z (phys_ok a))))).
  { forward. entailer!.
    rewrite sizeof_root. rewrite cmpu_le64.
    change (Int64.sub (Int64.shl (Int64.repr 1) (Int64.repr 52)) (Int64.repr ROOT_BYTES))
      with (Int64.repr (2 ^ 52 - ROOT_BYTES)).
    rewrite ltu64 by (auto; unfold word_ok, ROOT_BYTES; rep_lia).
    unfold phys_ok. rewrite H0. simpl andb.
    change (2 ^ 52 - ROOT_BYTES) with 4503599627325440 in *.
    destruct (Z.ltb_spec 4503599627325440 a); destruct (Z.leb_spec a 4503599627325440);
      try lia; reflexivity. }
  { forward. entailer!. unfold phys_ok. rewrite H0. reflexivity. }
  forward.
Qed.

Lemma body_qotom_root_phys_disjoint : semax_body Vprog Gprog f_qotom_root_phys_disjoint phys_disjoint_spec.
Proof.
  start_function.
  forward.
  forward_if (temp _t'1 (Vint (Int.repr (b2z (disjoint a b))))).
  { forward. entailer!.
    rewrite ltu64 in H1 by auto. apply Z.ltb_ge in H1.
    rewrite sizeof_root, cmpu_ge64.
    rewrite ltu64 by (unfold word_ok, ROOT_BYTES in *; rep_lia).
    unfold disjoint. rewrite (proj2 (Z.leb_le a b)) by lia.
    destruct (Z.ltb_spec (b - a) ROOT_BYTES); destruct (Z.leb_spec ROOT_BYTES (b - a)); try lia; reflexivity. }
  { forward. entailer!.
    rewrite ltu64 in H1 by auto. apply Z.ltb_lt in H1.
    rewrite sizeof_root, cmpu_ge64.
    rewrite ltu64 by (unfold word_ok, ROOT_BYTES in *; rep_lia).
    unfold disjoint. rewrite (proj2 (Z.leb_gt a b)) by lia.
    destruct (Z.ltb_spec (a - b) ROOT_BYTES); destruct (Z.leb_spec ROOT_BYTES (a - b)); try lia; reflexivity. }
  forward.
Qed.

Lemma body_frame_window_pages : semax_body Vprog Gprog f_frame_window_pages window_pages_spec.
Proof.
  start_function.
  unfold window_val.
  forward. forward. forward.
  entailer!. unfold Int64.divu, pages_of, W.
  rewrite Int64.unsigned_repr_eq. rewrite (Int64.unsigned_repr 4096) by rep_lia. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* frame_window_geometry_ok                                               *)
(* ---------------------------------------------------------------------- *)

(* The prefixes of geometry_ok the code computes into _t'1 .. _t'5. *)
Definition geo1 (w: window) : bool := ((Z.land (w_base w) 4095 =? 0) && (w_base w <? w_limit w))%bool.
Definition geo2 (w: window) : bool := (geo1 w && (w_limit w <=? 16777216))%bool.
Definition geo3 (w: window) : bool :=
  (geo2 w && (((w_limit w - w_base w) mod W =? 4096) || ((w_limit w - w_base w) mod W =? 8192)))%bool.
Definition geo4 (w: window) : bool := (geo3 w && negb (w_slot w =? 0))%bool.
Definition geo5 (w: window) : bool := (geo4 w && (w_slot w <=? LEAVES))%bool.
Lemma geo6: forall w, geometry_ok w = (geo5 w && ((w_slot w + pages_of w) mod W <=? LEAVES))%bool.
Proof. reflexivity. Qed.

Lemma body_frame_window_geometry_ok : semax_body Vprog Gprog f_frame_window_geometry_ok geometry_ok_spec.
Proof.
  start_function.
  destruct H as (Wf & Ws & Wb & Wl & Wsl).
  assert (Hland := land_word (w_base w) 4095 Wb).
  unfold window_val.
  forward.
  forward_if (temp _t'1 (Vint (Int.repr (b2z (geo1 w))))).
  { change (Int.unsigned (Int.repr 4095)) with 4095 in *. rewrite ?and64_repr in *.
    assert (Hz: Z.land (w_base w) 4095 = 0).
    { apply repr64_inj; [ wok | wok | ]. match goal with Hq: Int64.repr _ = Int64.zero |- _ => exact Hq end. }
    forward. forward. forward. entailer!.
    unfold geo1. rewrite Hz. simpl andb. rewrite cmpu_lt64, ltu64 by wok. bfin. }
  { change (Int.unsigned (Int.repr 4095)) with 4095 in *. rewrite ?and64_repr in *.
    assert (Hz: Z.land (w_base w) 4095 <> 0).
    { intro X. match goal with Hq: Int64.repr _ <> Int64.repr 0 |- _ => apply Hq; rewrite X; reflexivity end. }
    forward. entailer!. unfold geo1. rewrite (proj2 (Z.eqb_neq _ _) Hz). reflexivity. }
  forward_if (temp _t'2 (Vint (Int.repr (b2z (geo2 w))))).
  { forward. forward. entailer!.
    unfold geo2. match goal with Hg: geo1 w = true |- _ => rewrite Hg end. simpl andb.
    rewrite cmpu_le64, ltu64 by wok. rewrite Z.leb_antisym. bfin. }
  { forward. entailer!. unfold geo2. match goal with Hg: geo1 w = false |- _ => rewrite Hg end. reflexivity. }
  forward_if (temp _t'3 (Vint (Int.repr (b2z (geo3 w))))).
  { forward. forward.
    forward_if (temp _t'3 (Vint (Int.repr (b2z (geo3 w))))).
    { change (Int.unsigned (Int.repr 4096)) with 4096 in *. rewrite ?sub64_repr in *.
      match goal with Hq: Int64.eq _ _ = true |- _ => rewrite eq64m in Hq by wok; apply Z.eqb_eq in Hq; rename Hq into Hd end.
      forward. entailer!.
      unfold geo3. match goal with Hg: geo2 w = true |- _ => rewrite Hg end.
      rewrite (proj2 (Z.eqb_eq _ _) Hd). reflexivity. }
    { change (Int.unsigned (Int.repr 4096)) with 4096 in *. rewrite ?sub64_repr in *.
      assert (Hd: (w_limit w - w_base w) mod W <> 4096).
      { intro X. match goal with Hq: Int64.repr _ <> Int64.repr 4096 |- _ => apply Hq end.
        rewrite <- (repr_mod64 (w_limit w - w_base w)), X. reflexivity. }
      forward. forward. forward. forward. entailer!.
      unfold geo3. match goal with Hg: geo2 w = true |- _ => rewrite Hg end.
      rewrite (proj2 (Z.eqb_neq _ _) Hd). simpl andb; simpl orb.
      rewrite cmpu_eq64, eq64m by wok. bfin. }
    entailer!. }
  { forward. entailer!. unfold geo3. match goal with Hg: geo2 w = false |- _ => rewrite Hg end. reflexivity. }
  forward_if (temp _t'4 (Vint (Int.repr (b2z (geo4 w))))).
  { forward. forward. entailer!.
    unfold geo4. match goal with Hg: geo3 w = true |- _ => rewrite Hg end. simpl andb.
    rewrite cmpu_ne64, eq64 by wok. bfin. }
  { forward. entailer!. unfold geo4. match goal with Hg: geo3 w = false |- _ => rewrite Hg end. reflexivity. }
  forward_if (temp _t'5 (Vint (Int.repr (b2z (geo5 w))))).
  { forward. forward. entailer!.
    unfold geo5. match goal with Hg: geo4 w = true |- _ => rewrite Hg end. simpl andb.
    rewrite cmpu_le64, ltu64 by wok. unfold LEAVES. rewrite Z.leb_antisym. bfin. }
  { forward. entailer!. unfold geo5. match goal with Hg: geo4 w = false |- _ => rewrite Hg end. reflexivity. }
  forward_if (temp _t'6 (Vint (Int.repr (b2z (geometry_ok w))))).
  { forward_call (wp, wsh, fetch, send, w).
    { split; auto. }
    unfold window_val. forward. forward. entailer!.
    rewrite geo6. match goal with Hg: geo5 w = true |- _ => rewrite Hg end. simpl andb.
    rewrite cmpu_le64, ltu64m by wok. unfold LEAVES. rewrite Z.leb_antisym. bfin. }
  { forward. entailer!. rewrite geo6. match goal with Hg: geo5 w = false |- _ => rewrite Hg end. reflexivity. }
  forward.
Qed.

(* ---------------------------------------------------------------------- *)
(* Lists                                                                  *)
(* ---------------------------------------------------------------------- *)

Lemma Zlength_longs: forall l, Zlength (longs l) = Zlength l.
Proof. intros. unfold longs. apply Zlength_map. Qed.

Lemma Znth_longs: forall (d: Inhabitant val) i l, 0 <= i < Zlength l ->
  @Znth val d i (longs l) = Vlong (Int64.repr (Znth i l)).
Proof. intros. unfold longs. rewrite Znth_map by lia. reflexivity. Qed.

Lemma Znth_word: forall i l, words_ok l -> 0 <= i < Zlength l -> word_ok (Znth i l).
Proof. intros i l H Hi. exact (proj1 (Forall_Znth l _) H i Hi). Qed.

Lemma member_app: forall f l1 l2, member f (l1 ++ l2) = (member f l1 || member f l2)%bool.
Proof. intros. unfold member. apply existsb_app. Qed.

Lemma member_In: forall f l, In f l -> member f l = true.
Proof. intros. unfold member. apply existsb_exists. exists f. split; auto. apply Z.eqb_refl. Qed.

Lemma member_one: forall f x, member f [x] = (f =? x).
Proof. intros. unfold member. simpl. apply orb_false_r. Qed.

Lemma sublist_snoc: forall (l: list Z) i, 0 <= i < Zlength l -> sublist 0 (i + 1) l = sublist 0 i l ++ [Znth i l].
Proof.
  intros. rewrite (sublist_split 0 i (i + 1)) by lia. rewrite sublist_len_1 by lia. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* qotom_root_protected_frame                                             *)
(* ---------------------------------------------------------------------- *)

Lemma body_qotom_root_protected_frame :
  semax_body Vprog Gprog f_qotom_root_protected_frame protected_frame_spec.
Proof.
  start_function.
  forward_for_simple_bound n
    (EX i: Z,
     PROP (member f (sublist 0 i fs) = false)
     LOCAL (temp _frame (Vlong (Int64.repr f)); temp _protected_frames p;
            temp _protected_count (Vlong (Int64.repr n)))
     SEP (data_at sh (tarray tulong (Zlength fs + Zlength rest)) (longs fs ++ rest) p)).
  { entailer!. }
  { assert (E: forall d: Inhabitant val, @Znth val d i (longs fs ++ rest) = Vlong (Int64.repr (Znth i fs))).
    { intros d. rewrite app_Znth1 by (rewrite Zlength_longs; lia). unfold longs. rewrite Znth_map by lia.
      reflexivity. }
    assert (Wi := Znth_word i fs H0 ltac:(lia)).
    cbv beta. Intros. forward.
    all: try solve [ entailer!; rewrite E; simpl; auto ].
    rewrite E.
    forward_if.
    { match goal with Hq: Int64.eq _ _ = true |- _ => rewrite eq64 in Hq by auto; apply Z.eqb_eq in Hq end.
      assert (M: member f (sublist 0 n fs) = true).
      { apply member_In. replace f with (Znth i (sublist 0 n fs)).
        - apply Znth_In. rewrite Zlength_sublist by lia. lia.
        - rewrite Znth_sublist by lia. replace (i + 0) with i by lia. assumption. }
      forward. rewrite M. entailer!. }
    { assert (Hne: Znth i fs <> f).
      { intro X. match goal with Hq: Int64.repr _ <> Int64.repr _ |- _ => apply Hq end. rewrite X. reflexivity. }
      forward. entailer!.
      rewrite sublist_snoc by lia. rewrite member_app.
      match goal with Hm: member f (sublist 0 i fs) = false |- _ => rewrite Hm end.
      rewrite member_one. simpl. apply Z.eqb_neq. auto. } }
  forward. entailer!.
  match goal with Hm: member _ _ = false |- _ => rewrite Hm end. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* qotom_root_source_ancestors                                            *)
(* ---------------------------------------------------------------------- *)

Lemma in_idx: forall n j, 0 <= n -> (In j (idx n) <-> 0 <= j < n).
Proof.
  intros n j Hn. unfold idx. rewrite in_map_iff. split.
  - intros [k [Hk Hin]]. apply in_seq in Hin. lia.
  - intros Hj. exists (Z.to_nat j). split; [ apply Z2Nat.id; lia | apply in_seq; lia ].
Qed.

Lemma forallb_idx: forall f n, 0 <= n -> (forallb f (idx n) = true <-> forall j, 0 <= j < n -> f j = true).
Proof.
  intros f n Hn. rewrite forallb_forall. split; intros H j Hj.
  - apply H. apply in_idx; lia.
  - apply H. apply in_idx in Hj; lia.
Qed.

Lemma forallb_idx1: forall f,
  forallb f (map (Z.add 1) (idx 511)) = true <-> forall j, 1 <= j < 512 -> f j = true.
Proof.
  intros f. rewrite forallb_forall. split.
  - intros H j Hj. apply H. apply in_map_iff. exists (j - 1). split; [ lia | apply in_idx; lia ].
  - intros H x Hx. apply in_map_iff in Hx. destruct Hx as [y [Hy Hin]].
    apply in_idx in Hin; [ | lia ]. subst x. apply H. lia.
Qed.

(* ancestors_ok as the four checks of qotom_root_source_ancestors. *)
Lemma ancestors_ok_iff: forall r phys, ancestors_ok r phys = true <->
  (clear_accessed (Znth 0 (pml4 r)) = table_entry phys 1 /\
   clear_accessed (Znth 0 (pdpt r)) = table_entry phys 2 /\
   (forall i, 1 <= i < 512 -> Znth i (pml4 r) = 0 /\ Znth i (pdpt r) = 0) /\
   (forall i, 0 <= i < 512 -> clear_accessed (Znth i (pd r)) = pd_entry phys i)).
Proof.
  intros r phys. unfold ancestors_ok. split.
  - intros H. apply andb_prop in H as [H D]. apply andb_prop in H as [H C]. apply andb_prop in H as [A B].
    apply Z.eqb_eq in A. apply Z.eqb_eq in B. rewrite forallb_idx1 in C. rewrite forallb_idx in D by lia.
    split; [ exact A | ]. split; [ exact B | ]. split.
    + intros i Hi. specialize (C i Hi). apply andb_prop in C as [C1 C2].
      split; apply Z.eqb_eq; assumption.
    + intros i Hi. apply Z.eqb_eq. apply D. exact Hi.
  - intros (A & B & C & D).
    apply andb_true_intro; split; [ apply andb_true_intro; split; [ apply andb_true_intro; split | ] | ].
    + apply Z.eqb_eq. exact A.
    + apply Z.eqb_eq. exact B.
    + apply forallb_idx1. intros i Hi. destruct (C i Hi) as [C1 C2]. rewrite C1, C2. reflexivity.
    + apply forallb_idx; [ lia | ]. intros i Hi. apply Z.eqb_eq. apply D. exact Hi.
Qed.

(* A load of a word of a root: the type check, then the loaded value as a Vlong. *)
Ltac load_long :=
  forward; try solve [ entailer!; rewrite Znth_longs by lia; simpl; auto ]; try (rewrite Znth_longs by lia).

Lemma body_qotom_root_source_ancestors :
  semax_body Vprog Gprog f_qotom_root_source_ancestors source_ancestors_spec.
Proof.
  start_function.
  destruct H as (L1 & L2 & L3 & L4 & W1 & W2 & W3 & W4).
  assert (Wm0 := Znth_word 0 (pml4 rv) W1 ltac:(lia)).
  assert (Wp0 := Znth_word 0 (pdpt rv) W2 ltac:(lia)).
  unfold root_val.
  forward_call (phys, 1).
  load_long.
  forward_if (temp _t'2 (Vint (Int.repr (b2z (negb ((clear_accessed (Znth 0 (pml4 rv)) =? table_entry phys 1) &&
                                                    (clear_accessed (Znth 0 (pdpt rv)) =? table_entry phys 2))))))).
  { match goal with Hq: Int64.and _ _ <> _ |- _ => rewrite clear_accessed_repr in Hq;
      assert (Hne: clear_accessed (Znth 0 (pml4 rv)) <> table_entry phys 1) by (intro X; apply Hq; rewrite X; reflexivity) end.
    forward. entailer!. rewrite (proj2 (Z.eqb_neq _ _) Hne). reflexivity. }
  { match goal with Hq: Int64.eq _ _ = true |- _ => rewrite clear_accessed_repr, eq64 in Hq;
      [ apply Z.eqb_eq in Hq; rename Hq into Heq | apply clear_accessed_word; auto | apply table_entry_word ] end.
    forward_call (phys, 2). load_long. forward. entailer!.
    rewrite Heq, Z.eqb_refl. simpl andb.
    unfold Int64.cmpu. rewrite clear_accessed_repr, eq64 by (apply clear_accessed_word || apply table_entry_word; auto).
    unfold bool2val, b2z. destruct (_ =? _); reflexivity. }
  forward_if.
  { forward. entailer!. destruct (ancestors_ok rv phys) eqn:EA; [ | reflexivity ].
    apply ancestors_ok_iff in EA. destruct EA as (A & B & _ & _).
    match goal with Hb: (_ && _)%bool = false |- _ => rewrite A, B, !Z.eqb_refl in Hb; discriminate end. }
  match goal with Hb: (_ && _)%bool = true |- _ => apply andb_prop in Hb; destruct Hb as [A0 B0] end.
  apply Z.eqb_eq in A0. apply Z.eqb_eq in B0.
  forward_for_simple_bound 512
    (EX i: Z,
     PROP (1 <= i; forall j, 1 <= j < i -> Znth j (pml4 rv) = 0 /\ Znth j (pdpt rv) = 0)
     LOCAL (temp _root r; temp _root_phys (Vlong (Int64.repr phys)))
     SEP (data_at sh t_root (root_val rv) r)).
  { entailer!; intros; lia. }
  { cbv beta. Intros. unfold root_val.
    assert (Wm := Znth_word i (pml4 rv) W1 ltac:(lia)).
    assert (Wp := Znth_word i (pdpt rv) W2 ltac:(lia)).
    load_long.
    forward_if (temp _t'4 (Vint (Int.repr (b2z (negb ((Znth i (pml4 rv) =? 0) && (Znth i (pdpt rv) =? 0))))))).
    { assert (Hne: Znth i (pml4 rv) <> 0).
      { intro X. match goal with Hq: Int64.repr _ <> Int64.repr 0 |- _ => apply Hq; rewrite X; reflexivity end. }
      forward. entailer!. rewrite (proj2 (Z.eqb_neq _ _) Hne). reflexivity. }
    { assert (Hz: Znth i (pml4 rv) = 0).
      { apply repr64_inj; [ auto | unfold word_ok; rep_lia | ].
        match goal with Hq: Int64.repr _ = Int64.zero |- _ => exact Hq end. }
      load_long. forward. entailer!. rewrite Hz, Z.eqb_refl. simpl andb.
      unfold Int64.cmpu. rewrite eq64 by (auto; unfold word_ok; rep_lia).
      unfold bool2val, b2z. destruct (Znth i (pdpt rv) =? 0); reflexivity. }
    forward_if.
    { forward. entailer!. destruct (ancestors_ok rv phys) eqn:EA; [ | reflexivity ].
      apply ancestors_ok_iff in EA. destruct EA as (_ & _ & C & _). destruct (C i ltac:(lia)) as [C1 C2].
      match goal with Hb: (_ && _)%bool = false |- _ => rewrite C1, C2 in Hb; simpl in Hb; discriminate end. }
    { match goal with Hb: (_ && _)%bool = true |- _ => apply andb_prop in Hb; destruct Hb as [Hb1 Hb2] end.
      apply Z.eqb_eq in Hb1. apply Z.eqb_eq in Hb2.
      forward. entailer!. intros j Hj. destruct (zeq j i); [ subst j; split; assumption | ].
      match goal with Hf: forall j, 1 <= j < i -> _ |- _ => apply Hf; lia end. } }
  Intros.
  match goal with Hf: forall j, 1 <= j < 512 -> _ |- _ => rename Hf into C0 end.
  forward_for_simple_bound 512
    (EX i: Z,
     PROP (forall j, 0 <= j < i -> clear_accessed (Znth j (pd rv)) = pd_entry phys j)
     LOCAL (temp _root r; temp _root_phys (Vlong (Int64.repr phys)))
     SEP (data_at sh t_root (root_val rv) r)).
  { entailer!; intros; lia. }
  { cbv beta. Intros. unfold root_val.
    assert (Wd := Znth_word i (pd rv) W3 ltac:(lia)).
    forward_if (temp _t'5 (Vlong (Int64.repr (pd_entry phys i)))).
    { change (Int.unsigned (Int.repr 8)) with 8 in *.
      forward_call (phys, 3 + i).
      forward. entailer!. unfold pd_entry. rewrite (proj2 (Z.ltb_lt i 8)) by lia. reflexivity. }
    { change (Int.unsigned (Int.repr 8)) with 8 in *.
      forward. entailer!. unfold pd_entry. rewrite (proj2 (Z.ltb_ge i 8)) by lia. reflexivity. }
    forward.
    load_long.
    forward_if.
    { match goal with Hq: Int64.and _ _ <> _ |- _ => rewrite clear_accessed_repr in Hq;
        assert (Hne: clear_accessed (Znth i (pd rv)) <> pd_entry phys i) by (intro X; apply Hq; rewrite X; reflexivity) end.
      forward. entailer!. destruct (ancestors_ok rv phys) eqn:EA; [ | reflexivity ].
      apply ancestors_ok_iff in EA. destruct EA as (_ & _ & _ & D). exfalso. apply Hne. apply D. lia. }
    { match goal with Hq: Int64.eq _ _ = true |- _ => rewrite clear_accessed_repr, eq64 in Hq;
        [ apply Z.eqb_eq in Hq; rename Hq into Heq | apply clear_accessed_word; auto | apply pd_entry_word ] end.
      forward. entailer!. intros j Hj. destruct (zeq j i); [ subst j; exact Heq | ].
      match goal with Hf: forall j, 0 <= j < i -> _ |- _ => apply Hf; lia end. } }
  forward. entailer!.
  rewrite (proj2 (ancestors_ok_iff rv phys)); [ reflexivity | ].
  split; [ exact A0 | split; [ exact B0 | split; [ exact C0 | ] ] ].
  match goal with Hf: forall j, 0 <= j < 512 -> _ |- _ => exact Hf end.
Qed.

(* ---------------------------------------------------------------------- *)
(* The wrappers                                                           *)
(* ---------------------------------------------------------------------- *)

Lemma body_roots_build : semax_body Vprog Gprog f_roots_build roots_build_spec.
Proof.
  start_function.
  forward_call (source, ssh, src, sp, closed, kold, kp, copy, cold, cp, frames, fsh, fs, n,
                aliases, ash, al, arest, m, result, rold).
  Intros status. forward. Exists status. entailer!.
Qed.

Lemma body_window_build : semax_body Vprog Gprog f_window_build window_build_spec.
Proof.
  start_function.
  forward_call (source, ssh, src, sp, closed, kold, kp, frames, fsh, fs, n,
                wp, wsh, fetch, fold, send, sold, w, first, fr, builtp, built).
  Intros vret. destruct vret as [[[[[status k'] fe'] se'] r'] b']. simpl fst in *; simpl snd in *.
  forward. Exists status k' fe' se' r' b'. entailer!.
Qed.

Lemma body_window_root_exact : semax_body Vprog Gprog f_window_root_exact window_root_exact_spec.
Proof.
  start_function.
  forward_call (r, rsh, rv, rp, k, ksh, kv, kp, frames, fsh, fs, n, wp, wsh, fetch, send, w, writable).
  forward.
Qed.
