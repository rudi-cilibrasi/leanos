(* Law capabilities_adversarial: what a walk of pci_collect_capabilities (Defs.walk) says about the device's answers,
   as facts on the indices of the log (the facts the harness's checks read).  Pure: no program here. *)
Require Import VST.floyd.proofauto.
Require Import LeanosCaps.proof.Defs.
Local Open Scope Z_scope.

(* An answer's parts. *)
Definition aoff (a: answer) : Z := fst (fst a).
Definition aok (a: answer) : bool := snd (fst a).
Definition aval (a: answer) : Z := snd a.
(* The next pointer of a capability header word: bits 8..15. *)
Definition nptr (a: answer) : Z := Z.land (Z.shiftr (aval a) 8) 255.

(* The pointers of the list loop from `next`, given the answers c of its reads: next, then each answer's next
   pointer (one more than the answers). *)
Fixpoint ptrs (next: Z) (c: list answer) : list Z :=
  match c with nil => [next] | a :: c' => next :: ptrs (nptr a) c' end.
(* The headers the loop publishes from these reads: each pointer with its answer's value. *)
Fixpoint caps_of (next: Z) (c: list answer) : list (Z * Z) :=
  match c with nil => nil | a :: c' => (next, aval a) :: caps_of (nptr a) c' end.

Lemma Zlength_ptrs: forall c next, Zlength (ptrs next c) = Zlength c + 1.
Proof.
  induction c as [|a c IH]; intros next; simpl ptrs; [ reflexivity | ].
  rewrite !Zlength_cons, IH. lia.
Qed.

Lemma Znth_ptrs_0: forall c next, Znth 0 (ptrs next c) = next.
Proof. intros [|a c] next; reflexivity. Qed.

Lemma Znth_ptrs_S: forall c next i, 0 <= i < Zlength c -> Znth (i + 1) (ptrs next c) = nptr (Znth i c).
Proof.
  induction c as [|a c IH]; intros next i Hi; [ rewrite Zlength_nil in Hi; lia | ].
  rewrite Zlength_cons in Hi. simpl ptrs. rewrite Znth_pos_cons by lia. replace (i + 1 - 1) with i by lia.
  destruct (Z.eq_dec i 0) as [->|Hne].
  - rewrite Znth_ptrs_0, Znth_0_cons. reflexivity.
  - rewrite (Znth_pos_cons i c a) by lia.
    replace i with ((i - 1) + 1) at 1 by lia. apply IH. lia.
Qed.

Lemma Zlength_caps_of: forall c next, Zlength (caps_of next c) = Zlength c.
Proof.
  induction c as [|a c IH]; intros next; simpl caps_of; [ reflexivity | ].
  rewrite !Zlength_cons, IH. reflexivity.
Qed.

Lemma Znth_caps_of: forall c next i, 0 <= i < Zlength c ->
  Znth i (caps_of next c) = (Znth i (ptrs next c), aval (Znth i c)).
Proof.
  induction c as [|a c IH]; intros next i Hi; [ rewrite Zlength_nil in Hi; lia | ].
  rewrite Zlength_cons in Hi. simpl caps_of. simpl ptrs.
  destruct (Z.eq_dec i 0) as [->|Hne].
  - rewrite !Znth_0_cons. reflexivity.
  - rewrite !Znth_pos_cons by lia. apply IH. lia.
Qed.

Lemma land255_range: forall x, 0 <= Z.land x 255 <= 255.
Proof.
  intros x. change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound x (2 ^ 8) ltac:(lia)). change (2 ^ 8) with 256 in *. change (Z.ones 8) with 255. lia.
Qed.

Lemma list_head_range: forall words, 0 <= list_head words <= 255.
Proof.
  intros. unfold list_head. destruct (_ =? 0); [ lia | apply land255_range ].
Qed.

Lemma nptr_range: forall a, 0 <= nptr a <= 255.
Proof. intros. apply land255_range. Qed.

Lemma ptrs_range: forall c next i, 0 <= next <= 255 -> 0 <= i <= Zlength c -> 0 <= Znth i (ptrs next c) <= 255.
Proof.
  intros c next i Hn Hi. destruct (Z.eq_dec i 0) as [->|Hne].
  - rewrite Znth_ptrs_0. exact Hn.
  - replace i with ((i - 1) + 1) by lia. rewrite Znth_ptrs_S by lia. apply nptr_range.
Qed.

(* ---------------------------------------------------------------------- *)
(* The list loop                                                           *)
(* ---------------------------------------------------------------------- *)

(* Read i of the loop was asked for pointer i (P = ptrs next c), which passed the loop's checks: at least 0x40,
   aligned, not already seen, not read before, and fewer than 48 headers read. *)
Definition rgood (seen: list Z) (count: Z) (P: list Z) (c: list answer) (i: Z) : Prop :=
  aoff (Znth i c) = Znth i P /\ 64 <= Znth i P /\ Z.land (Znth i P) 3 = 0 /\
  ~ In (Znth i P) seen /\ (forall j, 0 <= j < i -> Znth j P <> Znth i P) /\ count + i < 48.

(* Answer i succeeded, and is not an absent header. *)
Definition agood (c: list answer) (i: Z) : Prop :=
  aok (Znth i c) = true /\ Z.land (aval (Znth i c)) 255 <> 255.

(* The outcome of the loop from (next, count, seen, acc) on the answers c. *)
Definition chain_out (seen: list Z) (count: Z) (acc: list (Z * Z)) (next: Z) (c: list answer)
    (st off: Z) (caps: list (Z * Z)) : Prop :=
  (st = S_OK /\ off = 0 /\ caps = rev acc ++ caps_of next c /\ Znth (Zlength c) (ptrs next c) = 0 /\
     (forall i, 0 <= i < Zlength c -> agood c i)) \/
  (st = S_READ_FAILED /\ 1 <= Zlength c /\ aok (Znth (Zlength c - 1) c) = false /\
     off = Znth (Zlength c - 1) (ptrs next c) /\ caps = nil) \/
  (st = S_ABSENT /\ 1 <= Zlength c /\ aok (Znth (Zlength c - 1) c) = true /\
     Z.land (aval (Znth (Zlength c - 1) c)) 255 = 255 /\ off = Znth (Zlength c - 1) (ptrs next c) /\ caps = nil) \/
  (st = S_POINTER /\ (forall i, 0 <= i < Zlength c -> agood c i) /\ off = Znth (Zlength c) (ptrs next c) /\
     off <> 0 /\ caps = nil /\
     (off < 64 \/ Z.land off 3 <> 0 \/
      (~ In off seen /\ (forall j, 0 <= j < Zlength c -> Znth j (ptrs next c) <> off) /\ count + Zlength c = 48))) \/
  (st = S_CYCLE /\ (forall i, 0 <= i < Zlength c -> agood c i) /\ off = Znth (Zlength c) (ptrs next c) /\
     64 <= off /\ Z.land off 3 = 0 /\ caps = nil /\
     (In off seen \/ exists j, 0 <= j < Zlength c /\ Znth j (ptrs next c) = off)).

Lemma existsb_eqb_false: forall (x: Z) l, existsb (Z.eqb x) l = false -> ~ In x l.
Proof.
  intros x l E I. assert (existsb (Z.eqb x) l = true) by (apply existsb_exists; exists x; split; auto; apply Z.eqb_refl).
  congruence.
Qed.

Lemma existsb_eqb_true: forall (x: Z) l, existsb (Z.eqb x) l = true -> In x l.
Proof.
  intros x l E. apply existsb_exists in E. destruct E as [y [I E]]. apply Z.eqb_eq in E. subst. exact I.
Qed.

Lemma final_some: forall o ans o', final o ans = Some o' -> ans = nil /\ o' = o.
Proof. intros o [|a ans] o' E; simpl in E; [ inv E; auto | discriminate ]. Qed.

Lemma walk_chain_facts: forall fuel next count seen acc c st off caps,
  0 <= count <= 48 ->
  walk_chain fuel next count seen acc c = Some (st, off, caps) ->
  (forall i, 0 <= i < Zlength c -> rgood seen count (ptrs next c) c i) /\
  (forall i, 0 <= i < Zlength c - 1 -> agood c i) /\
  chain_out seen count acc next c st off caps.
Proof.
  induction fuel as [|f IH]; intros next count seen acc c st off caps Hc W; [ discriminate | ].
  simpl in W.
  destruct (next =? 0) eqn:E0.
  { apply final_some in W. destruct W as [-> W]. inv W. apply Z.eqb_eq in E0.
    unfold chain_out. rewrite !Zlength_nil. split; [ intros; lia | ]. split; [ intros; lia | ].
    left. simpl. rewrite app_nil_r. repeat split; auto; try (intros; lia). }
  apply Z.eqb_neq in E0.
  destruct ((next <? 64) || negb (Z.land next 3 =? 0))%bool eqn:E1.
  { apply final_some in W. destruct W as [-> W]. inv W.
    unfold chain_out. rewrite !Zlength_nil. split; [ intros; lia | ]. split; [ intros; lia | ].
    do 3 right. left. simpl. repeat split; auto; try (intros; lia). }
  apply orb_false_iff in E1. destruct E1 as [E1a E1b].
  apply Z.ltb_ge in E1a. apply negb_false_iff, Z.eqb_eq in E1b.
  destruct (existsb (Z.eqb next) seen) eqn:E2.
  { apply final_some in W. destruct W as [-> W]. inv W.
    unfold chain_out. rewrite !Zlength_nil. split; [ intros; lia | ]. split; [ intros; lia | ].
    do 4 right. simpl. repeat split; auto; try (intros; lia).
    all: left; apply existsb_eqb_true; exact E2. }
  apply existsb_eqb_false in E2.
  destruct (count =? 48) eqn:E3.
  { apply final_some in W. destruct W as [-> W]. inv W. apply Z.eqb_eq in E3.
    unfold chain_out. rewrite !Zlength_nil. split; [ intros; lia | ]. split; [ intros; lia | ].
    do 3 right. left. simpl. repeat split; auto; try (intros; lia).
    all: right; right; repeat split; auto; intros; lia. }
  apply Z.eqb_neq in E3.
  destruct c as [|[[o ok] v] c']; [ discriminate | ].
  destruct (negb (o =? next)) eqn:E4; [ discriminate | ].
  apply negb_false_iff, Z.eqb_eq in E4. subst o.
  (* the read of `next` *)
  assert (G0: rgood seen count (ptrs next (@cons answer (next, ok, v) c')) (@cons answer (next, ok, v) c') 0).
  { unfold rgood. simpl ptrs. rewrite !Znth_0_cons. unfold aoff. simpl.
    repeat split; auto; try lia. }
  destruct (negb ok) eqn:E5.
  { apply final_some in W. destruct W as [-> W]. inv W. apply negb_true_iff in E5. subst ok.
    unfold chain_out. change (Zlength [(next, false, v)]) with 1.
    split; [ intros i Hi; replace i with 0 by lia; exact G0 | ]. split; [ intros; lia | ].
    right; left. simpl. repeat split; auto; lia. }
  apply negb_false_iff in E5. subst ok.
  destruct (Z.land v 255 =? 255) eqn:E6.
  { apply final_some in W. destruct W as [-> W]. inv W. apply Z.eqb_eq in E6.
    unfold chain_out. change (Zlength [(next, true, v)]) with 1.
    split; [ intros i Hi; replace i with 0 by lia; exact G0 | ]. split; [ intros; lia | ].
    do 2 right; left. simpl. repeat split; auto; lia. }
  apply Z.eqb_neq in E6.
  assert (A0: agood (@cons answer (next, true, v) c') 0) by (unfold agood; rewrite Znth_0_cons; simpl; auto).
  apply IH in W; [ | lia ].
  destruct W as (R & A & O).
  change (Z.land (Z.shiftr v 8) 255) with (nptr (next, true, v)) in R, O.
  remember ((next, true, v) : answer) as a eqn:Ea.
  assert (EP: ptrs next (a :: c') = next :: ptrs (nptr a) c') by reflexivity.
  remember (ptrs (nptr a) c') as P' eqn:EP'.
  assert (Ln: Zlength (a :: c') = Zlength c' + 1) by (rewrite Zlength_cons; reflexivity).
  pose proof (Zlength_nonneg c') as Lc'.
  (* index shifting *)
  assert (SP: forall i, 0 < i -> Znth i (next :: P') = Znth (i - 1) P') by (intros; apply Znth_pos_cons; lia).
  assert (SC: forall i, 0 < i -> Znth i (a :: c') = Znth (i - 1) c') by (intros; apply Znth_pos_cons; lia).
  assert (AG: forall i, 0 <= i < Zlength c' -> agood c' i -> agood (a :: c') (i + 1)).
  { intros i Hi G. unfold agood in *. rewrite SC by lia. replace (i + 1 - 1) with i by lia. exact G. }
  assert (AGall: (forall i, 0 <= i < Zlength c' -> agood c' i) ->
                 forall i, 0 <= i < Zlength c' + 1 -> agood (a :: c') i).
  { intros H i Hi. destruct (Z.eq_dec i 0) as [->|Hne]; [ exact A0 | ].
    replace i with ((i - 1) + 1) by lia. apply AG; [ lia | apply H; lia ]. }
  assert (NOTIN: forall x, ~ In x (next :: seen) -> ~ In x seen /\ next <> x).
  { intros x N. split; [ intro I; apply N; right; exact I | intro E; apply N; left; exact E ]. }
  assert (SPn: Znth (Zlength c' + 1) (next :: P') = Znth (Zlength c') P')
    by (rewrite SP by lia; f_equal; lia).
  rewrite Ln, EP. rewrite EP in G0.
  split; [ | split ].
  - intros i Hi. destruct (Z.eq_dec i 0) as [->|Hne]; [ exact G0 | ].
    specialize (R (i - 1) ltac:(lia)). unfold rgood in R |- *.
    rewrite SC, SP by lia. destruct R as (R1 & R2 & R3 & R4 & R5 & R6).
    apply NOTIN in R4. destruct R4 as [R4 R4'].
    repeat split; auto; try lia.
    intros j Hj. destruct (Z.eq_dec j 0) as [->|Hj0]; [ rewrite Znth_0_cons; exact R4' | ].
    rewrite SP by lia. apply R5. lia.
  - intros i Hi. destruct (Z.eq_dec i 0) as [->|Hne]; [ exact A0 | ].
    replace i with ((i - 1) + 1) by lia. apply AG; [ lia | apply A; lia ].
  - unfold chain_out in O |- *. rewrite <- EP' in O. rewrite Ln, EP.
    destruct O as [O|[O|[O|[O|O]]]].
    + destruct O as (O1 & O2 & O3 & O4 & O5). left. rewrite SPn.
      split; [ exact O1 | ]. split; [ exact O2 | ].
      split; [ rewrite O3; simpl rev; rewrite <- app_assoc; subst a; reflexivity | ].
      split; [ exact O4 | apply AGall; exact O5 ].
    + destruct O as (O1 & O2 & O3 & O4 & O5). right; left.
      replace (Zlength c' + 1 - 1) with (Zlength c') by lia.
      rewrite SC, SP by lia. repeat split; auto; lia.
    + destruct O as (O1 & O2 & O3 & O4 & O5 & O6). do 2 right; left.
      replace (Zlength c' + 1 - 1) with (Zlength c') by lia.
      rewrite SC, SP by lia. repeat split; auto; lia.
    + destruct O as (O1 & O2 & O3 & O4 & O5 & O6). do 3 right; left. rewrite SPn.
      split; [ exact O1 | ]. split; [ apply AGall; exact O2 | ].
      split; [ exact O3 | ]. split; [ exact O4 | ]. split; [ exact O5 | ].
      destruct O6 as [O6|[O6|(N & D & C)]]; [ left; exact O6 | right; left; exact O6 | ].
      right; right. apply NOTIN in N. destruct N as [N N'].
      repeat split; auto; try lia.
      intros j Hj. destruct (Z.eq_dec j 0) as [->|Hj0]; [ rewrite Znth_0_cons; exact N' | ].
      rewrite SP by lia. apply D. lia.
    + destruct O as (O1 & O2 & O3 & O4 & O5 & O6 & O7). do 4 right. rewrite SPn.
      split; [ exact O1 | ]. split; [ apply AGall; exact O2 | ].
      split; [ exact O3 | ]. split; [ exact O4 | ]. split; [ exact O5 | ]. split; [ exact O6 | ].
      destruct O7 as [I|(j & Hj & E)].
      * destruct I as [I|I]; [ right; exists 0; rewrite Znth_0_cons; split; [ lia | exact I ] | left; exact I ].
      * right. exists (j + 1). rewrite SP by lia. replace (j + 1 - 1) with j by lia. split; [ lia | exact E ].
Qed.

(* ---------------------------------------------------------------------- *)
(* The header reads                                                        *)
(* ---------------------------------------------------------------------- *)

(* Header read j: at the j-th header offset, successful, and matching the initial header under the j-th mask. *)
Definition hgood (hs: list (Z * Z)) (words: list Z) (ans: list answer) (j: Z) : Prop :=
  aoff (Znth j ans) = fst (Znth j hs) /\ aok (Znth j ans) = true /\
  Z.land (aval (Znth j ans)) (snd (Znth j hs)) = Z.land (Znth (fst (Znth j hs) / 4) words) (snd (Znth j hs)).

Lemma walk_header_gen: forall hs words ans o, walk_header hs words ans = Some o ->
  (exists k, 0 <= k < Zlength hs /\ Zlength ans = k + 1 /\ (forall j, 0 <= j < k -> hgood hs words ans j) /\
     aoff (Znth k ans) = fst (Znth k hs) /\
     ((aok (Znth k ans) = false /\ o = (S_READ_FAILED, fst (Znth k hs), nil)) \/
      (aok (Znth k ans) = true /\
       Z.land (aval (Znth k ans)) (snd (Znth k hs)) <> Z.land (Znth (fst (Znth k hs) / 4) words) (snd (Znth k hs)) /\
       o = (S_HEADER_CHANGED, fst (Znth k hs), nil)))) \/
  (Zlength hs <= Zlength ans /\ (forall j, 0 <= j < Zlength hs -> hgood hs words ans j) /\
   walk_chain 50 (list_head words) 0 nil nil (sublist (Zlength hs) (Zlength ans) ans) = Some o).
Proof.
  induction hs as [|[o0 m0] hs IH]; intros words ans o W.
  - right. simpl in W. rewrite Zlength_nil. split; [ apply Zlength_nonneg | ].
    split; [ intros; lia | ]. rewrite sublist_same by auto. exact W.
  - destruct ans as [|[[o' ok] v] rest]; [ discriminate | ].
    cbn [walk_header] in W.
    destruct (negb (o' =? o0)) eqn:E1; [ discriminate | ].
    apply negb_false_iff, Z.eqb_eq in E1. subst o'.
    pose proof (Zlength_nonneg hs) as Lhs. pose proof (Zlength_nonneg rest) as Lr.
    destruct (negb ok) eqn:E2.
    { apply final_some in W. destruct W as [-> ->]. apply negb_true_iff in E2. subst ok.
      left. exists 0. rewrite Zlength_cons. rewrite !Znth_0_cons. unfold aoff, aok; simpl.
      repeat split; auto; try lia. all: intros; lia. }
    apply negb_false_iff in E2. subst ok.
    destruct (negb (Z.land v m0 =? Z.land (Znth (o0 / 4) words) m0)) eqn:E3.
    { apply final_some in W. destruct W as [-> ->]. apply negb_true_iff, Z.eqb_neq in E3.
      left. exists 0. rewrite Zlength_cons. rewrite !Znth_0_cons. unfold aoff, aok, aval; simpl.
      repeat split; auto; try lia. all: intros; lia. }
    apply negb_false_iff, Z.eqb_eq in E3.
    assert (H0: hgood ((o0, m0) :: hs) words (@cons answer (o0, true, v) rest) 0).
    { unfold hgood. rewrite !Znth_0_cons. unfold aoff, aok, aval; simpl. auto. }
    assert (HS: forall j, 0 <= j < Zlength hs -> hgood hs words rest j ->
                hgood ((o0, m0) :: hs) words (@cons answer (o0, true, v) rest) (j + 1)).
    { intros j Hj G. unfold hgood in *. rewrite !Znth_pos_cons by lia. replace (j + 1 - 1) with j by lia. exact G. }
    apply IH in W. destruct W as [(k & Hk & Lk & Gk & Ok & Ck)|(L & G & W)].
    + left. exists (k + 1). rewrite !Zlength_cons.
      split; [ lia | ]. split; [ lia | ].
      split.
      { intros j Hj. destruct (Z.eq_dec j 0) as [->|Hj0]; [ exact H0 | ].
        replace j with ((j - 1) + 1) by lia. apply HS; [ lia | apply Gk; lia ]. }
      rewrite !Znth_pos_cons by lia. replace (k + 1 - 1) with k by lia.
      split; [ exact Ok | exact Ck ].
    + right. rewrite !Zlength_cons. split; [ lia | split ].
      * intros j Hj. destruct (Z.eq_dec j 0) as [->|Hj0]; [ exact H0 | ].
        replace j with ((j - 1) + 1) by lia. apply HS; [ lia | apply G; lia ].
      * rewrite sublist_S_cons by lia. replace (Z.succ (Zlength hs) - 1) with (Zlength hs) by lia.
        replace (Z.succ (Zlength rest) - 1) with (Zlength rest) by lia. exact W.
Qed.
