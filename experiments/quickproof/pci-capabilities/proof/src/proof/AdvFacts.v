(* Law capabilities_adversarial: from a walk `walk words h = Some (st, off, caps)` (Defs.walk), the facts each check
   of the harness reads, on the indices of the device's log h (the four header reads, then the list reads).  Pure. *)
Require Import VST.floyd.proofauto.
Require Import LeanosCaps.proof.Defs.
Require Import LeanosCaps.proof.AdvWalk.
Local Open Scope Z_scope.

(* Header read k: its offset and mask (header_offsets[k] and masks[k] of the harness). *)
Definition hc_off (k: Z) : Z := fst (Znth k header_checks).
Definition hc_mask (k: Z) : Z := snd (Znth k header_checks).
(* An answer matches the initial header under the mask of header read k. *)
Definition hmatch (words: list Z) (k: Z) (a: answer) : Prop :=
  Z.land (aval a) (hc_mask k) = Z.land (Znth (hc_off k / 4) words) (hc_mask k).

(* The list reads of the log, their pointers, and the pointer the last read names (the harness's named_pointer). *)
Definition chain (h: list answer) : list answer := sublist 4 (Zlength h) h.
Definition hptr (words: list Z) (h: list answer) (i: Z) : Z := Znth i (ptrs (list_head words) (chain h)).
Definition named (words: list Z) (h: list answer) : Z :=
  if Zlength h =? 4 then list_head words else nptr (Znth (Zlength h - 1) h).
(* Some list read asked for p (the harness's `repeated`). *)
Definition seen_in (h: list answer) (p: Z) : bool := existsb (fun a => aoff a =? p) (chain h).

Lemma Zlength_chain: forall h, 4 <= Zlength h -> Zlength (chain h) = Zlength h - 4.
Proof. intros. unfold chain. rewrite Zlength_sublist by lia. lia. Qed.

Lemma Znth_chain: forall h i, 0 <= i < Zlength h - 4 -> Znth i (chain h) = Znth (4 + i) h.
Proof. intros. unfold chain. rewrite Znth_sublist by lia. f_equal; lia. Qed.

Lemma hptr_0: forall words h, hptr words h 0 = list_head words.
Proof. intros. unfold hptr. apply Znth_ptrs_0. Qed.

Lemma hptr_S: forall words h i, 0 <= i < Zlength h - 4 -> hptr words h (i + 1) = nptr (Znth (4 + i) h).
Proof.
  intros. unfold hptr. rewrite Znth_ptrs_S by (rewrite Zlength_chain by lia; lia).
  rewrite Znth_chain by lia. reflexivity.
Qed.

Lemma hptr_range: forall words h i, 4 <= Zlength h -> 0 <= i <= Zlength h - 4 -> 0 <= hptr words h i <= 255.
Proof.
  intros. unfold hptr. apply ptrs_range; [ apply list_head_range | rewrite Zlength_chain by lia; lia ].
Qed.

Lemma named_hptr: forall words h, 4 <= Zlength h -> named words h = hptr words h (Zlength h - 4).
Proof.
  intros words h L. unfold named. destruct (Zlength h =? 4) eqn:E.
  - apply Z.eqb_eq in E. rewrite E. rewrite hptr_0. reflexivity.
  - apply Z.eqb_neq in E. replace (Zlength h - 4) with ((Zlength h - 5) + 1) by lia.
    rewrite hptr_S by lia. f_equal. f_equal. lia.
Qed.

Lemma named_range: forall words h, 4 <= Zlength h -> 0 <= named words h <= 255.
Proof. intros. rewrite named_hptr by auto. apply hptr_range; lia. Qed.

(* The shape of a walk: a header read that fails, or the four header reads and then the list loop. *)
Lemma walk_view: forall words h st off caps, walk words h = Some (st, off, caps) ->
  (forall k, 0 <= k < Zlength h -> k < 4 -> aoff (Znth k h) = hc_off k) /\
  ((exists k, 0 <= k < 4 /\ Zlength h = k + 1 /\ (forall j, 0 <= j < k -> hgood header_checks words h j) /\
       caps = nil /\ off = aoff (Znth k h) /\
       ((st = S_READ_FAILED /\ aok (Znth k h) = false) \/
        (st = S_HEADER_CHANGED /\ aok (Znth k h) = true /\ ~ hmatch words k (Znth k h)))) \/
   (4 <= Zlength h /\ (forall j, 0 <= j < 4 -> hgood header_checks words h j) /\
    (forall i, 0 <= i < Zlength (chain h) -> rgood nil 0 (ptrs (list_head words) (chain h)) (chain h) i) /\
    (forall i, 0 <= i < Zlength (chain h) - 1 -> agood (chain h) i) /\
    chain_out nil 0 nil (list_head words) (chain h) st off caps)).
Proof.
  intros words h st off caps W. unfold walk in W. apply walk_header_gen in W.
  change (Zlength header_checks) with 4 in W.
  destruct W as [(k & Hk & Lk & G & Ok & C)|(L & G & W)].
  - split.
    + intros j Hj Hj4. destruct (Z.eq_dec j k) as [->|Hne]; [ exact Ok | ].
      apply G. lia.
    + left. exists k. split; [ exact Hk | ]. split; [ exact Lk | ]. split; [ exact G | ].
      destruct C as [(C1 & C2)|(C1 & C2 & C3)]; inversion C2 || inversion C3; subst.
      * split; [ reflexivity | ]. split; [ symmetry; exact Ok | ]. left; auto.
      * split; [ reflexivity | ]. split; [ symmetry; exact Ok | ]. right; auto.
  - split.
    + intros j Hj Hj4. apply G. lia.
    + right. split; [ lia | ]. split; [ exact G | ].
      apply walk_chain_facts in W; [ exact W | lia ].
Qed.

Section Facts.
Variables (words: list Z) (h: list answer) (st off: Z) (caps: list (Z * Z)).
Hypothesis W: walk words h = Some (st, off, caps).

Ltac view :=
  destruct (walk_view _ _ _ _ _ W) as [HO [(k & Hk & Lk & G & Ec & Eo & C)|(L & G & R & A & O)]];
  [ | pose proof (Zlength_chain h L) as Lc ].

Lemma f_hoff: forall k, 0 <= k < Zlength h -> k < 4 -> aoff (Znth k h) = hc_off k.
Proof. exact (proj1 (walk_view _ _ _ _ _ W)). Qed.

Lemma f_st: st = S_OK \/ st = S_READ_FAILED \/ st = S_HEADER_CHANGED \/ st = S_POINTER \/ st = S_CYCLE \/
            st = S_ABSENT.
Proof.
  view.
  - destruct C as [(C & _)|(C & _)]; subst; auto.
  - unfold chain_out in O. destruct O as [O|[O|[O|[O|O]]]]; destruct O as [O _]; subst; auto 6.
Qed.

Lemma f_st_range: 0 <= st <= 6 /\ st <> S_ARGUMENT.
Proof.
  destruct f_st as [E|[E|[E|[E|[E|E]]]]]; subst; unfold S_OK, S_ARGUMENT, S_READ_FAILED, S_HEADER_CHANGED,
    S_POINTER, S_CYCLE, S_ABSENT; lia.
Qed.

Lemma f_caps: st <> S_OK -> caps = nil.
Proof.
  intros N. view; [ exact Ec | ].
  unfold chain_out in O. destruct O as [O|[O|[O|[O|O]]]].
  - destruct O as [O _]. contradiction.
  - destruct O as (_ & _ & _ & _ & O). exact O.
  - destruct O as (_ & _ & _ & _ & _ & O). exact O.
  - destruct O as (_ & _ & _ & _ & O & _). exact O.
  - destruct O as (_ & _ & _ & _ & _ & O & _). exact O.
Qed.

Lemma f_len: 1 <= Zlength h.
Proof. view; lia. Qed.

Lemma f_ok: forall k, 0 <= k < Zlength h - 1 -> aok (Znth k h) = true.
Proof.
  intros j Hj. view.
  - destruct (G j ltac:(lia)) as (_ & G2 & _). exact G2.
  - destruct (Z_lt_le_dec j 4) as [J|J].
    + destruct (G j ltac:(lia)) as (_ & G2 & _). exact G2.
    + destruct (A (j - 4) ltac:(lia)) as [A1 _]. rewrite Znth_chain in A1 by lia.
      replace (4 + (j - 4)) with j in A1 by lia. exact A1.
Qed.

Lemma f_hm: forall k, 0 <= k < Zlength h - 1 -> k < 4 -> hmatch words k (Znth k h).
Proof.
  intros j Hj Hj4. view.
  - destruct (G j ltac:(lia)) as (_ & _ & G3). exact G3.
  - destruct (G j ltac:(lia)) as (_ & _ & G3). exact G3.
Qed.

Lemma f_RF: st = S_READ_FAILED -> aok (Znth (Zlength h - 1) h) = false /\ off = aoff (Znth (Zlength h - 1) h).
Proof.
  intros E. view.
  - replace (Zlength h - 1) with k by lia.
    destruct C as [(C1 & C2)|(C1 & _)]; [ split; auto | subst; discriminate ].
  - unfold chain_out in O. destruct O as [O|[O|[O|[O|O]]]];
      try (destruct O as [O _]; subst; discriminate).
    destruct O as (_ & O1 & O2 & O3 & _).
    destruct (R (Zlength (chain h) - 1) ltac:(lia)) as (R1 & _).
    rewrite Znth_chain in O2, R1 by lia. replace (4 + (Zlength (chain h) - 1)) with (Zlength h - 1) in O2, R1 by lia.
    split; [ exact O2 | rewrite R1; exact O3 ].
Qed.

Ltac st_absurd :=
  exfalso; unfold S_OK, S_ARGUMENT, S_READ_FAILED, S_HEADER_CHANGED, S_POINTER, S_CYCLE, S_ABSENT in *;
  subst; first [ congruence | lia ].

(* The last answer, as the last of the list reads. *)
Lemma last_chain: 4 < Zlength h ->
  Znth (Zlength (chain h) - 1) (chain h) = Znth (Zlength h - 1) h.
Proof.
  intros. rewrite Znth_chain by (rewrite Zlength_chain by lia; lia). rewrite Zlength_chain by lia. f_equal; lia.
Qed.

Lemma f_okL: st <> S_READ_FAILED -> aok (Znth (Zlength h - 1) h) = true.
Proof.
  intros N. view.
  - replace (Zlength h - 1) with k by lia.
    destruct C as [(C1 & _)|(_ & C2 & _)]; [ contradiction | exact C2 ].
  - destruct (Z.eq_dec (Zlength h) 4) as [E4|E4].
    + rewrite E4. destruct (G 3 ltac:(lia)) as (_ & G2 & _). exact G2.
    + rewrite <- last_chain by lia. unfold chain_out in O.
      destruct O as [O|[O|[O|[O|O]]]].
      * destruct O as (_ & _ & _ & _ & O). destruct (O (Zlength (chain h) - 1) ltac:(lia)) as [O1 _]. exact O1.
      * destruct O as [O _]. contradiction.
      * destruct O as (_ & _ & O & _). exact O.
      * destruct O as (_ & O & _). destruct (O (Zlength (chain h) - 1) ltac:(lia)) as [O1 _]. exact O1.
      * destruct O as (_ & O & _). destruct (O (Zlength (chain h) - 1) ltac:(lia)) as [O1 _]. exact O1.
Qed.

Lemma f_HC: st = S_HEADER_CHANGED ->
  Zlength h - 1 < 4 /\ ~ hmatch words (Zlength h - 1) (Znth (Zlength h - 1) h) /\ off = aoff (Znth (Zlength h - 1) h).
Proof.
  intros E. view.
  - replace (Zlength h - 1) with k by lia.
    destruct C as [(C1 & _)|(_ & _ & C3)]; [ st_absurd | ]. split; [ lia | ]. split; [ exact C3 | exact Eo ].
  - unfold chain_out in O. destruct O as [O|[O|[O|[O|O]]]]; destruct O as [O _]; st_absurd.
Qed.

Lemma f_n4: st <> S_READ_FAILED -> st <> S_HEADER_CHANGED -> 4 <= Zlength h.
Proof.
  intros N1 N2. view; [ | exact L ].
  destruct C as [(C1 & _)|(C1 & _)]; contradiction.
Qed.

Lemma f_last_abs: st <> S_READ_FAILED -> st <> S_HEADER_CHANGED -> st <> S_ABSENT -> 4 <= Zlength h - 1 ->
  Z.land (aval (Znth (Zlength h - 1) h)) 255 <> 255.
Proof.
  intros N1 N2 N3 L4. view.
  - destruct C as [(C1 & _)|(C1 & _)]; contradiction.
  - rewrite <- last_chain by lia. unfold chain_out in O.
    destruct O as [O|[O|[O|[O|O]]]].
    * destruct O as (_ & _ & _ & _ & O). destruct (O (Zlength (chain h) - 1) ltac:(lia)) as [_ O1]. exact O1.
    * destruct O as [O _]. contradiction.
    * destruct O as [O _]. contradiction.
    * destruct O as (_ & O & _). destruct (O (Zlength (chain h) - 1) ltac:(lia)) as [_ O1]. exact O1.
    * destruct O as (_ & O & _). destruct (O (Zlength (chain h) - 1) ltac:(lia)) as [_ O1]. exact O1.
Qed.

Lemma f_last_hm: st <> S_READ_FAILED -> st <> S_HEADER_CHANGED -> Zlength h - 1 < 4 ->
  hmatch words (Zlength h - 1) (Znth (Zlength h - 1) h).
Proof.
  intros N1 N2 L4. view.
  - destruct C as [(C1 & _)|(C1 & _)]; contradiction.
  - destruct (G (Zlength h - 1) ltac:(lia)) as (_ & _ & G3). exact G3.
Qed.

Lemma f_AB: st = S_ABSENT ->
  4 <= Zlength h - 1 /\ Z.land (aval (Znth (Zlength h - 1) h)) 255 = 255 /\ off = aoff (Znth (Zlength h - 1) h).
Proof.
  intros E. view.
  - destruct C as [(C1 & _)|(C1 & _)]; st_absurd.
  - unfold chain_out in O. destruct O as [O|[O|[O|[O|O]]]]; try (destruct O as [O _]; st_absurd).
    destruct O as (_ & O1 & O2 & O3 & O4 & _).
    destruct (R (Zlength (chain h) - 1) ltac:(lia)) as (R1 & _).
    rewrite last_chain in O3, R1 by lia.
    split; [ lia | ]. split; [ exact O3 | rewrite R1; exact O4 ].
Qed.

Lemma f_PC: st = S_POINTER \/ st = S_CYCLE -> named words h <> 0 /\ off = named words h.
Proof.
  intros E. view.
  - destruct C as [(C1 & _)|(C1 & _)]; destruct E; st_absurd.
  - rewrite named_hptr by lia. unfold hptr. rewrite <- Lc.
    unfold chain_out in O. destruct O as [O|[O|[O|[O|O]]]];
      try (destruct O as [O _]; destruct E; st_absurd).
    + destruct O as (_ & _ & O3 & O4 & _). split; [ congruence | exact O3 ].
    + destruct O as (_ & _ & O3 & O4 & _). split; [ lia | exact O3 ].
Qed.

Lemma existsb_Znth_false {A} {d: Inhabitant A}: forall (f: A -> bool) l,
  (forall j, 0 <= j < Zlength l -> f (Znth j l) = false) -> existsb f l = false.
Proof.
  intros f l H. destruct (existsb f l) eqn:E; auto.
  apply existsb_exists in E. destruct E as [x [I F]]. apply In_Znth in I. destruct I as [j [Hj Ej]].
  subst x. rewrite H in F by auto. discriminate.
Qed.

Lemma existsb_Znth_true {A} {d: Inhabitant A}: forall (f: A -> bool) l j,
  0 <= j < Zlength l -> f (Znth j l) = true -> existsb f l = true.
Proof.
  intros f l j Hj F. apply existsb_exists. exists (Znth j l). split; auto. apply Znth_In. auto.
Qed.

Lemma f_P: st = S_POINTER ->
  named words h < 64 \/ Z.land (named words h) 3 <> 0 \/ (seen_in h (named words h) = false /\ Zlength h = 52).
Proof.
  intros E. view.
  - destruct C as [(C1 & _)|(C1 & _)]; st_absurd.
  - rewrite named_hptr by lia. unfold hptr. rewrite <- Lc.
    unfold chain_out in O. destruct O as [O|[O|[O|[O|O]]]]; try (destruct O as [O _]; st_absurd).
    destruct O as (_ & _ & O3 & _ & _ & O6). rewrite <- O3.
    destruct O6 as [O6|[O6|(_ & D & C)]]; [ left; exact O6 | right; left; exact O6 | ].
    right; right. split; [ | lia ].
    unfold seen_in. apply existsb_Znth_false. intros j Hj.
    destruct (R j Hj) as (R1 & _). rewrite R1. apply Z.eqb_neq. apply D. exact Hj.
Qed.

Lemma f_C: st = S_CYCLE -> 64 <= named words h /\ Z.land (named words h) 3 = 0 /\ seen_in h (named words h) = true.
Proof.
  intros E. view.
  - destruct C as [(C1 & _)|(C1 & _)]; st_absurd.
  - rewrite named_hptr by lia. unfold hptr. rewrite <- Lc.
    unfold chain_out in O. destruct O as [O|[O|[O|[O|O]]]]; try (destruct O as [O _]; st_absurd).
    destruct O as (_ & _ & O3 & O4 & O5 & _ & O7). rewrite <- O3.
    split; [ exact O4 | ]. split; [ exact O5 | ].
    destruct O7 as [I|(j & Hj & Ej)]; [ destruct I | ].
    unfold seen_in. apply (existsb_Znth_true _ _ j Hj).
    destruct (R j Hj) as (R1 & _). rewrite R1, Ej. apply Z.eqb_refl.
Qed.

Lemma f_hdr4: st = S_OK -> forall k, 0 <= k < 4 -> aok (Znth k h) = true /\ hmatch words k (Znth k h).
Proof.
  intros E j Hj. view.
  - destruct C as [(C1 & _)|(C1 & _)]; st_absurd.
  - destruct (G j Hj) as (_ & G2 & G3). split; [ exact G2 | exact G3 ].
Qed.

Lemma f_OK: st = S_OK ->
  off = 0 /\ Zlength h = 4 + Zlength caps /\ Zlength caps <= 48 /\ hptr words h (Zlength caps) = 0 /\
  forall i, 0 <= i < Zlength caps ->
    Znth i caps = (hptr words h i, aval (Znth (4 + i) h)) /\
    64 <= hptr words h i /\ Z.land (hptr words h i) 3 = 0 /\
    (forall j, 0 <= j < i -> hptr words h j <> hptr words h i) /\
    aoff (Znth (4 + i) h) = hptr words h i /\ aok (Znth (4 + i) h) = true /\
    Z.land (aval (Znth (4 + i) h)) 255 <> 255 /\
    hptr words h (i + 1) = nptr (Znth (4 + i) h).
Proof.
  intros E. view.
  - destruct C as [(C1 & _)|(C1 & _)]; st_absurd.
  - unfold chain_out in O. destruct O as [O|[O|[O|[O|O]]]]; try (destruct O as [O _]; st_absurd).
    destruct O as (_ & O2 & O3 & O4 & O5). simpl rev in O3. rewrite app_nil_l in O3. subst caps.
    rewrite Zlength_caps_of. unfold hptr.
    assert (B: Zlength (chain h) <= 48).
    { destruct (Z.eq_dec (Zlength (chain h)) 0) as [Z0|Z0]; [ lia | ].
      destruct (R (Zlength (chain h) - 1) ltac:(lia)) as (_ & _ & _ & _ & _ & R6). lia. }
    split; [ exact O2 | ]. split; [ lia | ]. split; [ exact B | ]. split; [ exact O4 | ].
    intros i Hi.
    destruct (R i Hi) as (R1 & R2 & R3 & R4 & R5 & R6). destruct (O5 i Hi) as [A1 A2].
    rewrite Znth_chain in R1, A1, A2 by lia.
    split; [ rewrite Znth_caps_of by exact Hi; rewrite Znth_chain by lia; reflexivity | ].
    split; [ exact R2 | ]. split; [ exact R3 | ]. split; [ exact R5 | ].
    split; [ exact R1 | ]. split; [ exact A1 | ]. split; [ exact A2 | ].
    rewrite Znth_ptrs_S by exact Hi. rewrite Znth_chain by lia. reflexivity.
Qed.

End Facts.
