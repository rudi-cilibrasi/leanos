(* Law enumeration_exact: facts of the scan model of Defs.v that the law's device follows.  The scan's states
   after answers are those of `run start`, and run extends answer by answer (run_snoc); every such state keeps
   inv (its counters in range, its headers whole but for the one being read), and the number of answers it has
   taken is nreads. *)
Require Import VST.floyd.proofauto.
Require Import LeanosEnum.proof.Defs.
Local Open Scope Z_scope.

(* A whole header: its 16 dwords. *)
Definition complete (f: found) : Prop := Zlength (snd f) = WORDS.

Definition inv (s: state) : Prop :=
  let '(next, w, fs) := s in
  0 <= next <= FUNCTIONS /\ 0 <= w < WORDS /\ Zlength fs <= CAPACITY /\
  Forall (fun f => 0 <= fst f < FUNCTIONS) fs /\
  (if w =? 0 then Forall complete fs
   else exists ws rest, fs = (next - 1, ws) :: rest /\ Zlength ws = w /\ Forall complete rest).

(* The dwords read after the identity, over the headers found. *)
Fixpoint extra (fs: list found) : Z :=
  match fs with nil => 0 | f :: r => Zlength (snd f) - 1 + extra r end.

Definition nreads (s: state) : Z := let '(next, _, fs) := s in next + extra fs.

Lemma inv_start: inv start.
Proof.
  unfold inv, start. rewrite Zlength_nil. simpl.
  split; [ unfold FUNCTIONS; lia | ]. split; [ unfold WORDS; lia | ]. split; [ unfold CAPACITY; lia | ].
  split; constructor.
Qed.

Lemma step_inv: forall s a s',
  inv s -> live s = true -> answers (request s) a = true -> step s a = Go s' ->
  inv s' /\ nreads s' = nreads s + 1.
Proof.
  intros [[next w] fs] [[[i o] ok] v] s' I L A S.
  unfold inv in I. destruct I as (Rn & Rw & Rf & Fi & Fc).
  unfold live in L. unfold request, answers in A. unfold step in S.
  destruct ok; simpl in S; [ | discriminate ].
  destruct (Z.eqb_spec w 0) as [W0|W0].
  - subst w. simpl in A, L. apply andb_prop in A. destruct A as [Ai Ao].
    apply Z.eqb_eq in Ai. apply Z.eqb_eq in Ao. subst i o.
    destruct (Z.eqb_spec next FUNCTIONS) as [E|E]; [ discriminate | ].
    destruct (Z.land v 65535 =? 65535).
    + inv S. unfold inv, nreads. split; [ | lia ].
      split; [ unfold FUNCTIONS in *; lia | ]. split; [ exact Rw | ]. split; [ exact Rf | ].
      split; [ exact Fi | exact Fc ].
    + destruct (Zlength fs =? CAPACITY) eqn:C; [ discriminate | ]. apply Z.eqb_neq in C.
      inv S. unfold inv, nreads. simpl extra. unfold found in *. rewrite ?Zlength_cons, ?Zlength_nil. split.
      * split; [ unfold FUNCTIONS in *; lia | ]. split; [ unfold WORDS; lia | ].
        split; [ unfold CAPACITY in *; lia | ]. split.
        -- constructor; [ simpl; unfold FUNCTIONS in *; lia | exact Fi ].
        -- simpl. exists [v], fs. split; [ f_equal; f_equal; lia | ]. split; [ reflexivity | exact Fc ].
      * lia.
  - cbv beta iota in Fc.
    destruct Fc as (ws & rest & -> & Lw & Fr).
    simpl in S. injection S; intros <-. unfold inv, nreads. simpl extra. unfold found in *.
    rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil.
    split; [ | lia ].
    pose proof (Forall_inv Fi) as Fi0. pose proof (Forall_inv_tail Fi) as Fi1.
    split; [ lia | ].
    destruct (Z.eqb_spec w 15) as [E|E]; cbv beta iota; rewrite Zlength_cons in Rf.
    + split; [ unfold WORDS; lia | ]. split; [ lia | ].
      split; [ constructor; [ simpl in *; lia | exact Fi1 ] | ].
      change (0 =? 0) with true. cbv beta iota.
      constructor; [ unfold complete; simpl snd; rewrite Zlength_app, Zlength_cons, Zlength_nil; unfold WORDS in *; lia
                   | exact Fr ].
    + split; [ unfold WORDS in *; lia | ]. split; [ lia | ].
      split; [ constructor; [ simpl in *; lia | exact Fi1 ] | ].
      destruct (Z.eqb_spec (w + 1) 0) as [E1|E1]; [ lia | ].
      exists (ws ++ [v]), rest. split; [ reflexivity | ].
      split; [ rewrite Zlength_app, Zlength_cons, Zlength_nil; lia | exact Fr ].
Qed.

Lemma run_snoc: forall h a s0,
  run s0 (h ++ [a]) =
  match run s0 h with
  | Some (Go s) =>
      if (live s && answers (request s) a)%bool then
        match step s a with Go s' => Some (Go s') | Stop st i o => Some (Stop st i o) end
      else None
  | _ => None
  end.
Proof.
  induction h as [ | b h IH ]; intros a s0.
  - simpl. destruct (live s0 && answers (request s0) a)%bool; [ | reflexivity ].
    destruct (step s0 a); reflexivity.
  - simpl. destruct (live s0 && answers (request s0) b)%bool; [ | reflexivity ].
    destruct (step s0 b) as [ s' | st i o ].
    + apply IH.
    + destruct h; reflexivity.
Qed.

Lemma run_go: forall h s, run start h = Some (Go s) -> inv s /\ nreads s = Zlength h.
Proof.
  induction h as [ | a h IH ] using rev_ind; intros s R.
  - simpl in R. inv R. split; [ apply inv_start | reflexivity ].
  - rewrite run_snoc in R.
    destruct (run start h) as [ [ s0 | ? ? ? ] | ] eqn:R0; try discriminate.
    destruct (live s0 && answers (request s0) a)%bool eqn:LA; [ | discriminate ].
    apply andb_prop in LA. destruct LA as [L A].
    destruct (step s0 a) eqn:S; inv R.
    destruct (IH s0 eq_refl) as [I N].
    destruct (step_inv s0 a s I L A S) as [I' N'].
    split; [ exact I' | ]. rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma run_stop: forall h st i o, run start h = Some (Stop st i o) ->
  exists h' a s, h = h' ++ [a] /\ run start h' = Some (Go s) /\ live s = true /\
                 answers (request s) a = true /\ step s a = Stop st i o.
Proof.
  intros h st i o R. destruct h as [ | a h' ] using rev_ind; [ discriminate | ].
  rewrite run_snoc in R.
  destruct (run start h') as [ [ s | ? ? ? ] | ] eqn:R0; try discriminate.
  destruct (live s && answers (request s) a)%bool eqn:LA; [ | discriminate ].
  apply andb_prop in LA. destruct LA as [L A].
  destruct (step s a) eqn:S; inv R.
  exists h', a, s. auto.
Qed.

Lemma next_read_go: forall h i off, next_read h = Some (i, off) ->
  exists next w fs, run start h = Some (Go (next, w, fs)) /\ live (next, w, fs) = true /\
                    request (next, w, fs) = (i, off).
Proof.
  intros h i off N. unfold next_read in N.
  destruct (run start h) as [ [ [ [next w] fs ] | ? ? ? ] | ] eqn:R; try discriminate.
  destruct (live (next, w, fs)) eqn:L; [ | discriminate ].
  inv N. exists next, w, fs. auto.
Qed.

Lemma extra_bound: forall fs, Forall (fun f => Zlength (snd f) <= WORDS) fs ->
  0 <= extra fs + Zlength fs <= WORDS * Zlength fs.
Proof.
  induction fs as [ | f fs IH ]; intros F.
  - simpl. rewrite ?Zlength_nil. lia.
  - inv F. specialize (IH H2). simpl extra. unfold found in *. rewrite Zlength_cons.
    pose proof (Zlength_nonneg (snd f)). unfold WORDS in *. lia.
Qed.

(* The answers the scan takes: fewer than 2^32. *)
Lemma nreads_bound: forall s, inv s -> nreads s <= FUNCTIONS + WORDS * CAPACITY.
Proof.
  intros [[next w] fs] (Rn & Rw & Rf & Fi & Fc). unfold nreads.
  assert (F: Forall (fun f => Zlength (snd f) <= WORDS) fs).
  { destruct (w =? 0).
    - eapply Forall_impl; [ | exact Fc ]. intros f E. unfold complete in E. lia.
    - destruct Fc as (ws & rest & -> & Lw & Fr). constructor; [ simpl; lia | ].
      eapply Forall_impl; [ | exact Fr ]. intros f E. unfold complete in E. lia. }
  pose proof (extra_bound fs F). pose proof (Zlength_nonneg fs).
  unfold FUNCTIONS, WORDS, CAPACITY, found in *. nia.
Qed.

(* The ranges of the location of a function. *)
Lemma bus_range: forall i, 0 <= i < FUNCTIONS -> 0 <= bus_of i <= 255.
Proof.
  intros i Hi. unfold bus_of, FUNCTIONS in *. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
  split; [ apply Z.div_pos; lia | ]. apply Z.lt_succ_r. apply Z.div_lt_upper_bound; lia.
Qed.

Lemma land_ones_range: forall x n, 0 <= n -> 0 <= Z.land x (Z.ones n) < 2 ^ n.
Proof. intros x n Hn. rewrite Z.land_ones by lia. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. Qed.

Lemma dev_range: forall i, 0 <= dev_of i <= 31.
Proof.
  intros. unfold dev_of.
  pose proof (land_ones_range (Z.shiftr i 3) 5 ltac:(lia)). change (Z.ones 5) with 31 in *.
  change (2 ^ 5) with 32 in *. lia.
Qed.

Lemma fn_range: forall i, 0 <= fn_of i <= 7.
Proof.
  intros. unfold fn_of.
  pose proof (land_ones_range i 3 ltac:(lia)). change (Z.ones 3) with 7 in *. change (2 ^ 3) with 8 in *. lia.
Qed.

(* The read the scan makes: of a function of the segment, at an offset of the 64-byte header. *)
Lemma request_range: forall s i o ok v, inv s -> live s = true -> answers (request s) (i, o, ok, v) = true ->
  0 <= i < FUNCTIONS /\ 0 <= o <= 60.
Proof.
  intros [[next w] fs] i o ok v (Rn & Rw & Rf & Fi & Fc) L A.
  unfold request, answers, live in *. unfold FUNCTIONS, WORDS in *.
  destruct (Z.eqb_spec w 0) as [W0|W0].
  - subst w. simpl in A, L. apply andb_prop in A. destruct A as [Ai Ao].
    apply Z.eqb_eq in Ai. apply Z.eqb_eq in Ao. subst i o.
    destruct (Z.eqb_spec next 65536); [ discriminate | ]. lia.
  - simpl in A. apply andb_prop in A. destruct A as [Ai Ao].
    apply Z.eqb_eq in Ai. apply Z.eqb_eq in Ao. subst i o.
    cbv beta iota in Fc. destruct Fc as (ws & rest & E & _). subst fs.
    pose proof (Forall_inv Fi) as X. simpl in X. lia.
Qed.

(* A return at an answer: a failed read, or the 17th function found (at its identity read). *)
Lemma step_stop: forall next w fs i' o' ok v st i o,
  answers (request (next, w, fs)) (i', o', ok, v) = true -> step (next, w, fs) (i', o', ok, v) = Stop st i o ->
  i = i' /\ o = o' /\
  (ok = false /\ st = S_READ_FAILED \/ ok = true /\ w = 0 /\ Zlength fs = CAPACITY /\ st = S_CAPACITY_EXCEEDED /\ o = 0).
Proof.
  intros next w fs i' o' ok v st i o A S. unfold step in S.
  destruct ok; simpl in S.
  - destruct (Z.eqb_spec w 0) as [W0|W0]; [ | discriminate ].
    destruct (Z.land v 65535 =? 65535); [ discriminate | ].
    destruct (Z.eqb_spec (Zlength fs) CAPACITY) as [C|C]; [ | discriminate ].
    inv S. unfold request, answers in A. simpl in A. apply andb_prop in A. destruct A as [_ Ao].
    apply Z.eqb_eq in Ao. subst o'. auto 10.
  - inv S. auto.
Qed.

Lemma run_stop_status: forall h st i o, run start h = Some (Stop st i o) ->
  st = S_READ_FAILED \/ st = S_CAPACITY_EXCEEDED.
Proof.
  intros h st i o R. destruct (run_stop h st i o R) as (h' & [[[i' o'] ok] v] & [[next w] fs] & _ & _ & _ & A & S).
  destruct (step_stop next w fs i' o' ok v st i o A S) as (_ & _ & [ (_ & E) | (_ & _ & _ & E & _) ]); auto.
Qed.
