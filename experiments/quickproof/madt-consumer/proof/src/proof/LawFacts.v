(* Law consumer_obligations: the oracle's invariant J against the model's run, one answer at a time: what a call
   of each export implies of the oracle (its checks), and the oracle after each export's update. *)
Require Import VST.floyd.proofauto.
Require Import LeanosMadt.proof.Defs.
Require Import LeanosMadt.proof.MadtSpecs.
Require Import LeanosMadt.proof.LawProg LeanosMadt.proof.LawDefs.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* ---------------------------------------------------------------------- *)
(* The run, one answer more                                               *)
(* ---------------------------------------------------------------------- *)

Lemma run_snoc: forall x p h c v,
  run x p (h ++ [(c, v)]) =
  match run x p h with
  | Some (Go s) => if call_eqb c (expected x s) then Some (step x s v) else None
  | _ => None
  end.
Proof.
  intros x p h. revert p. induction h as [ | [c' v'] h IH ]; intros p c v; simpl.
  - destruct p as [s | o]; [ | reflexivity ]. destruct (call_eqb c (expected x s)); reflexivity.
  - destruct p as [s | o]; [ | reflexivity ]. destruct (call_eqb c' (expected x s)); [ apply IH | reflexivity ].
Qed.

Lemma list_eqb_refl: forall l, list_eqb l l = true.
Proof.
  intros l. unfold list_eqb. rewrite Z.eqb_refl. simpl.
  induction l as [ | a l IH ]; simpl; [ reflexivity | ]. rewrite Z.eqb_refl. exact IH.
Qed.

Lemma call_eqb_refl: forall c, call_eqb c c = true.
Proof. intros [ ] ; simpl; rewrite ?list_eqb_refl, ?Z.eqb_refl; reflexivity. Qed.

(* The invariant at a progress of the consumer. *)
Definition Jp (x: inputs) (p: progress) (s: ost) : Prop :=
  match p with Go g => go_inv x g s | Return r => main_ok x r s end.

Lemma J_snoc: forall x h g v s, run x (start x) h = Some (Go g) ->
  J x (h ++ [(expected x g, v)]) s = Jp x (step x g v) s.
Proof.
  intros x h g v s R. unfold J. rewrite run_snoc, R, call_eqb_refl. destruct (step x g v); reflexivity.
Qed.

Lemma next_call_go: forall x h c, next_call x h = Some c ->
  exists g, run x (start x) h = Some (Go g) /\ c = expected x g.
Proof.
  unfold next_call. intros x h c E. destruct (run x (start x) h) as [[g | o] | ]; inversion E; eauto.
Qed.

Lemma J_go: forall x h g s, run x (start x) h = Some (Go g) -> J x h s -> go_inv x g s.
Proof. unfold J. intros x h g s R K. rewrite R in K. exact K. Qed.

Lemma J_consume: forall x h o s, consume x h = Some o -> J x h s -> main_ok x o s.
Proof.
  unfold consume, J. intros x h o s C K. destruct (run x (start x) h) as [[g | r] | ]; inversion C; subst; auto.
Qed.

Lemma J_start: forall bytes ob s, length_ok (Zlength bytes) = true ->
  os_phase s = 0 -> os_byte s = 0 -> os_word s = 0 -> os_state s = initial_state -> os_rejected s = 0 ->
  J (bytes, ob) nil s.
Proof.
  intros bytes ob s L P B W S R. unfold J, run, start. simpl fst. rewrite L. simpl.
  unfold length_ok in L. apply andb_true_iff in L as [L1 L2]. apply Z.ltb_lt in L1.
  rewrite Zlength_nil, sublist_nil. repeat split; auto; lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* The calls                                                               *)
(* ---------------------------------------------------------------------- *)

Lemma step_call: forall x h s state tl ex off byte word,
  next_call x h = Some (Step state tl ex off byte word) -> J x h s ->
  exists i cur, run x (start x) h = Some (Go (Stream i state cur)) /\ go_inv x (Stream i state cur) s /\
    tl = 44 + Zlength (fst x) /\ ex = o_executing (snd x) /\ off = 44 + i /\ byte = Znth i (fst x) /\
    word = Zlength cur.
Proof.
  intros x h s state tl ex off byte word N K. destruct (next_call_go _ _ _ N) as [g [R E]].
  pose proof (J_go _ _ _ _ R K) as G. destruct x as [bytes ob].
  destruct g as [i st cur | last st count nmi cur | last st cur]; simpl in E; inversion E; subst.
  exists i, cur. auto 8.
Qed.

Lemma nmi_call: forall x h s count nmi routing word,
  next_call x h = Some (Nmi count nmi routing word) -> J x h s ->
  exists last state cur, run x (start x) h = Some (Go (Policy last state count nmi cur)) /\
    go_inv x (Policy last state count nmi cur) s /\ routing = o_routing (snd x) /\ word = Zlength cur.
Proof.
  intros x h s count nmi routing word N K. destruct (next_call_go _ _ _ N) as [g [R E]].
  pose proof (J_go _ _ _ _ R K) as G. destruct x as [bytes ob].
  destruct g as [i st cur | last st count' nmi' cur | last st cur]; simpl in E; inversion E; subst.
  exists last, st, cur. auto.
Qed.

Lemma finish_call: forall x h s st er state tl ex edx av ab sid word,
  next_call x h = Some (Finish st er state tl ex edx av ab sid word) -> J x h s ->
  exists last cur, run x (start x) h = Some (Go (Bound last state cur)) /\ go_inv x (Bound last state cur) s /\
    st = Znth 1 last /\ er = Znth 2 last /\ tl = 44 + Zlength (fst x) /\ ex = o_executing (snd x) /\
    edx = o_cpuid_edx (snd x) /\ av = o_available (snd x) /\ ab = o_apic_base (snd x) /\
    sid = o_sample_id (snd x) /\ word = Zlength cur.
Proof.
  intros x h s st er state tl ex edx av ab sid word N K. destruct (next_call_go _ _ _ N) as [g [R E]].
  pose proof (J_go _ _ _ _ R K) as G. destruct x as [bytes ob].
  destruct g as [i st' cur | last st' count nmi cur | last st' cur]; simpl in E; inversion E; subst.
  exists last, cur. auto 12.
Qed.

(* ---------------------------------------------------------------------- *)
(* The oracle's updates                                                    *)
(* ---------------------------------------------------------------------- *)

(* The answer of the current word recorded, the word advanced (every export's first case). *)
Definition s_answer (s: ost) (v: Z) : ost :=
  mk_ost (os_phase s) (os_byte s) (os_word s + 1) (os_state s) (upd_Znth (os_word s) (os_answer s) v)
         (os_count s) (os_nmi s) (os_policy s) (os_bound s) (os_rejected s).
Definition s_policy (s: ost) (v: Z) : ost :=
  mk_ost (os_phase s) (os_byte s) (os_word s + 1) (os_state s) (os_answer s) (os_count s) (os_nmi s)
         (upd_Znth (os_word s) (os_policy s) v) (os_bound s) (os_rejected s).
Definition s_bound (s: ost) (v: Z) : ost :=
  mk_ost (os_phase s) (os_byte s) (os_word s + 1) (os_state s) (os_answer s) (os_count s) (os_nmi s)
         (os_policy s) (upd_Znth (os_word s) (os_bound s) v) (os_rejected s).

(* The stream's transition accepted: the next byte (or, after the last, the policy). *)
Definition s_accept (s: ost) (n: Z) (r: list Z) : ost :=
  mk_ost (if os_byte s + 1 =? n then 1 else 0) (os_byte s + 1) 0 (sublist 3 15 r) r
         (os_count s) (os_nmi s) (os_policy s) (os_bound s) (os_rejected s).
(* ... rejected. *)
Definition s_reject (s: ost) (r: list Z) : ost :=
  mk_ost 3 (os_byte s) (os_word s) (os_state s) r (os_count s) (os_nmi s) (os_policy s) (os_bound s) 1.
(* The policy's fifth word. *)
Definition s_policy_done (s: ost) (p: list Z) : ost :=
  mk_ost (if pacc p then 2 else 3) (os_byte s) 0 (os_state s) (os_answer s) (os_count s) (os_nmi s) p
         (os_bound s) (os_rejected s).
(* The finish's sixth word. *)
Definition s_bound_done (s: ost) (b: list Z) : ost :=
  mk_ost 3 (os_byte s) 0 (os_state s) (os_answer s) (os_count s) (os_nmi s) (os_policy s) b (os_rejected s).

(* The C test of the stream's transition (the harness's step export). *)
Definition accept_b (n i b: Z) (r: list Z) : bool :=
  (Znth 0 r =? 1) && negb (Znth 1 r =? 2) && (Znth 1 r =? (if i + 1 =? n then 3 else 1)) && (Znth 2 r =? 0) &&
  (Znth 3 r =? 44 + i + 1) && (Znth 15 r =? b).

Lemma step_stream_full: forall bytes ob i state cur v, Zlength cur = 15 ->
  step (bytes, ob) (Stream i state cur) v =
  if accept_b (Zlength bytes) i (Znth i bytes) (cur ++ [v]) then
    (if i + 1 =? Zlength bytes then after_stream bytes (cur ++ [v]) (sublist 3 15 (cur ++ [v]))
     else Go (Stream (i + 1) (sublist 3 15 (cur ++ [v])) nil))
  else Return (reject (if two_b (cur ++ [v]) then 2 else 3) (if two_b (cur ++ [v]) then Znth 2 (cur ++ [v]) else 0)
                      (44 + i)).
Proof.
  intros bytes ob i state cur v L. unfold step.
  replace (Zlength (cur ++ [v]) <? 16) with false by (symmetry; apply Z.ltb_ge; rewrite Zlength_app, L; reflexivity).
  unfold accept_b, two_b.
  destruct (Znth 0 (cur ++ [v]) =? 1); simpl; [ | reflexivity ].
  destruct (Znth 1 (cur ++ [v]) =? 2); simpl; [ reflexivity | ].
  destruct (Znth 1 (cur ++ [v]) =? (if i + 1 =? Zlength bytes then 3 else 1));
  destruct (Znth 2 (cur ++ [v]) =? 0); destruct (Znth 3 (cur ++ [v]) =? 44 + i + 1);
  destruct (Znth 15 (cur ++ [v]) =? Znth i bytes); simpl; reflexivity.
Qed.

Lemma answer_snoc: forall (cur ans: list Z) v, Zlength ans = 16 -> Zlength cur < 16 ->
  sublist 0 (Zlength cur) ans = cur ->
  sublist 0 (Zlength cur + 1) (upd_Znth (Zlength cur) ans v) = cur ++ [v].
Proof. intros. list_solve. Qed.

Lemma answer_full: forall (cur ans: list Z) v, Zlength ans = 16 -> Zlength cur = 15 ->
  sublist 0 15 ans = cur -> upd_Znth 15 ans v = cur ++ [v].
Proof. intros. list_solve. Qed.

Lemma prefix_snoc: forall (cur l: list Z) v k, Zlength l = k -> Zlength cur < k ->
  sublist 0 (Zlength cur) l = cur ->
  sublist 0 (Zlength cur + 1) (upd_Znth (Zlength cur) l v) = cur ++ [v].
Proof. intros. list_solve. Qed.

Lemma prefix_full: forall (cur l: list Z) v k, Zlength l = k + 1 -> Zlength cur = k -> 0 <= k ->
  sublist 0 k l = cur -> upd_Znth k l v = cur ++ [v].
Proof. intros. list_solve. Qed.

(* Close a goal of go_inv / main_ok: split, introduce, then arithmetic and the facts of the context. *)
Ltac close_ok :=
  repeat (first [ progress intros | split ]);
  try (match goal with H: pacc [_; _; _; _; _] = false |- _ => compute in H; discriminate H end);
  try congruence; try lia;
  try (match goal with |- context [if ?b then _ else _] => destruct b; first [ lia | congruence ] end).

Lemma Jp_stream_more: forall bytes ob i state cur v s,
  go_inv (bytes, ob) (Stream i state cur) s -> Zlength (os_answer s) = 16 -> Zlength cur < 15 ->
  Jp (bytes, ob) (step (bytes, ob) (Stream i state cur) v) (s_answer s v).
Proof.
  intros bytes ob i state cur v s (P & B & W & S & A & R & I & C) L C15.
  unfold step. rewrite Zlength_app, Zlength_cons, Zlength_nil.
  replace (Zlength cur + Z.succ 0 <? 16) with true by (symmetry; apply Z.ltb_lt; lia).
  unfold Jp, go_inv, s_answer; simpl in *. rewrite Zlength_app, Zlength_cons, Zlength_nil, W.
  replace (Zlength cur + Z.succ 0) with (Zlength cur + 1) by lia.
  repeat split; auto; try lia. apply answer_snoc; auto; lia.
Qed.

Lemma Jp_stream_accept: forall bytes ob i state cur v s,
  go_inv (bytes, ob) (Stream i state cur) s -> Zlength (os_answer s) = 16 -> Zlength cur = 15 ->
  nmi_ok bytes s ->
  accept_b (Zlength bytes) i (Znth i bytes) (upd_Znth 15 (os_answer s) v) = true ->
  Jp (bytes, ob) (step (bytes, ob) (Stream i state cur) v)
     (s_accept s (Zlength bytes) (upd_Znth 15 (os_answer s) v)).
Proof.
  intros bytes ob i state cur v s (P & B & W & S & A & R & I & C) L C15 NM Acc.
  simpl fst in *. rewrite C15 in A.
  assert (E: upd_Znth 15 (os_answer s) v = cur ++ [v]) by (apply answer_full; auto).
  rewrite step_stream_full by auto. rewrite E in *. rewrite Acc.
  unfold s_accept. rewrite B.
  destruct (Z.eqb_spec (i + 1) (Zlength bytes)) as [En | En].
  - unfold after_stream. destruct (records bytes) as [[count nmi] | ] eqn:Rc.
    + unfold Jp, go_inv; simpl. rewrite sublist_nil. repeat split; auto; lia.
    + unfold Jp, main_ok, reject; simpl. unfold walk_b. rewrite Rc.
      repeat split; auto; try lia; try discriminate.
  - unfold Jp, go_inv; simpl. rewrite sublist_nil. repeat split; auto; lia.
Qed.

Lemma Jp_stream_reject: forall bytes ob i state cur v s,
  go_inv (bytes, ob) (Stream i state cur) s -> Zlength (os_answer s) = 16 -> Zlength cur = 15 ->
  accept_b (Zlength bytes) i (Znth i bytes) (upd_Znth 15 (os_answer s) v) = false ->
  Jp (bytes, ob) (step (bytes, ob) (Stream i state cur) v) (s_reject s (upd_Znth 15 (os_answer s) v)).
Proof.
  intros bytes ob i state cur v s (P & B & W & S & A & R & I & C) L C15 Acc.
  simpl fst in *. rewrite C15 in A.
  assert (E: upd_Znth 15 (os_answer s) v = cur ++ [v]) by (apply answer_full; auto).
  rewrite step_stream_full by auto. rewrite E in *. rewrite Acc.
  unfold Jp, main_ok, reject, s_reject; simpl. rewrite B.
  repeat split; try (intros; lia); try (destruct (two_b (cur ++ [v])); lia); auto.
Qed.

(* The policy's test (the C of the NMI export's last word). *)
Lemma step_policy_full: forall bytes ob last state count nmi cur v, Zlength cur = 4 ->
  step (bytes, ob) (Policy last state count nmi cur) v =
  if pacc (cur ++ [v]) then Go (Bound last state nil)
  else Return (reject (if five_b (cur ++ [v]) then 5 else 3) (if five_b (cur ++ [v]) then Znth 2 (cur ++ [v]) else 0)
                      (Znth 0 state)).
Proof.
  intros bytes ob last state count nmi cur v L. unfold step.
  replace (Zlength (cur ++ [v]) <? 5) with false by (symmetry; apply Z.ltb_ge; rewrite Zlength_app, L; reflexivity).
  unfold pacc, five_b.
  set (p0 := Znth 0 (cur ++ [v])). set (p1 := Znth 1 (cur ++ [v])). set (p2 := Znth 2 (cur ++ [v])).
  set (p3 := Znth 3 (cur ++ [v])). set (p4 := Znth 4 (cur ++ [v])).
  destruct (Z.eqb_spec p0 1), (Z.eqb_spec p1 1), (Z.eqb_spec p2 0), (Z.eqb_spec p3 1), (Z.eqb_spec p4 4),
    (Z.ltb_spec 1 p3), (Z.ltb_spec 4 p4), (Z.leb_spec p3 1), (Z.leb_spec p4 4);
    try (exfalso; lia); simpl; reflexivity.
Qed.

Lemma pacc_list: forall p, Zlength p = 5 -> pacc p = true -> p = [1; 1; 0; 1; 4].
Proof.
  intros p L A. unfold pacc in A. repeat rewrite andb_true_iff in A.
  destruct A as [[[[A0 A1] A2] A3] A4]. apply Z.eqb_eq in A0, A1, A2, A3, A4.
  do 5 (destruct p as [ | ? p ]; [ rewrite ?Zlength_cons, Zlength_nil in L; lia | ]).
  destruct p; [ | rewrite !Zlength_cons in L; pose proof (Zlength_nonneg p); lia ].
  rewrite Znth_0_cons in A0. rewrite !Znth_pos_cons, !Znth_0_cons in * by lia. simpl in *. subst. reflexivity.
Qed.

Lemma Jp_policy_more: forall bytes ob last state count nmi cur v s,
  go_inv (bytes, ob) (Policy last state count nmi cur) s -> Zlength (os_policy s) = 5 -> Zlength cur < 4 ->
  Jp (bytes, ob) (step (bytes, ob) (Policy last state count nmi cur) v) (s_policy s v).
Proof.
  intros bytes ob last state count nmi cur v s (P & B & W & S & A & Pp & R & Rc & C) L C4.
  unfold step. rewrite Zlength_app, Zlength_cons, Zlength_nil.
  replace (Zlength cur + Z.succ 0 <? 5) with true by (symmetry; apply Z.ltb_lt; lia).
  unfold Jp, go_inv, s_policy; simpl in *. rewrite Zlength_app, Zlength_cons, Zlength_nil, W.
  replace (Zlength cur + Z.succ 0) with (Zlength cur + 1) by lia.
  repeat split; auto; try lia. apply (prefix_snoc cur (os_policy s) v 5); auto; lia.
Qed.

Lemma Jp_policy_done: forall bytes ob last state count nmi cur v s,
  go_inv (bytes, ob) (Policy last state count nmi cur) s -> Zlength (os_policy s) = 5 -> Zlength cur = 4 ->
  Jp (bytes, ob) (step (bytes, ob) (Policy last state count nmi cur) v)
     (s_policy_done s (upd_Znth 4 (os_policy s) v)).
Proof.
  intros bytes ob last state count nmi cur v s (P & B & W & S & A & Pp & R & Rc & C) L C4.
  simpl fst in *. rewrite C4 in Pp.
  assert (E: upd_Znth 4 (os_policy s) v = cur ++ [v]) by (apply (prefix_full cur (os_policy s) v 4); auto; lia).
  rewrite step_policy_full by auto. rewrite E.
  assert (Lp: Zlength (cur ++ [v]) = 5) by (rewrite Zlength_app, C4; reflexivity).
  unfold s_policy_done. destruct (pacc (cur ++ [v])) eqn:Pa.
  - unfold Jp, go_inv; simpl. rewrite sublist_nil. rewrite (pacc_list _ Lp Pa).
    repeat split; auto; try lia; congruence.
  - unfold Jp, main_ok, reject; simpl. unfold walk_b. rewrite Rc. close_ok.
Qed.

(* The finish's test (the C of main's checks of the bound). *)
Lemma step_bound_full: forall bytes ob last state cur v, Zlength cur = 5 ->
  step (bytes, ob) (Bound last state cur) v =
  Return (if bacc ob state (cur ++ [v])
          then (0, 0, Znth 0 state, Znth 2 (cur ++ [v]), Znth 3 (cur ++ [v]), Znth 4 (cur ++ [v]))
          else reject (if four_b (cur ++ [v]) then 4 else 3) (if four_b (cur ++ [v]) then Znth 2 (cur ++ [v]) else 0)
                      (Znth 0 state)).
Proof.
  intros bytes ob last state cur v L. unfold step.
  replace (Zlength (cur ++ [v]) <? 6) with false by (symmetry; apply Z.ltb_ge; rewrite Zlength_app, L; reflexivity).
  unfold bacc, four_b.
  set (b0 := Znth 0 (cur ++ [v])). set (b1 := Znth 1 (cur ++ [v])). set (b2 := Znth 2 (cur ++ [v])).
  set (b3 := Znth 3 (cur ++ [v])). set (b4 := Znth 4 (cur ++ [v])). set (b5 := Znth 5 (cur ++ [v])).
  destruct (Z.eqb_spec b0 1), (Z.eqb_spec b5 0), (Z.eqb_spec b1 2), (Z.eqb_spec b1 5), (Z.eqb_spec b1 1),
    (Z.eqb_spec b2 (o_executing ob)), (Z.eqb_spec b3 (Znth 6 state)), (Z.eqb_spec b4 (o_apic_base ob));
    try (exfalso; lia); simpl; reflexivity.
Qed.

Lemma Jp_bound_more: forall bytes ob last state cur v s,
  go_inv (bytes, ob) (Bound last state cur) s -> Zlength (os_bound s) = 6 -> Zlength cur < 5 ->
  Jp (bytes, ob) (step (bytes, ob) (Bound last state cur) v) (s_bound s v).
Proof.
  intros bytes ob last state cur v s (P & B & W & S & A & Pp & Bb & R & Rc & C) L C5.
  unfold step. rewrite Zlength_app, Zlength_cons, Zlength_nil.
  replace (Zlength cur + Z.succ 0 <? 6) with true by (symmetry; apply Z.ltb_lt; lia).
  unfold Jp, go_inv, s_bound; simpl in *. rewrite Zlength_app, Zlength_cons, Zlength_nil, W.
  replace (Zlength cur + Z.succ 0) with (Zlength cur + 1) by lia.
  repeat split; auto; try lia. apply (prefix_snoc cur (os_bound s) v 6); auto; lia.
Qed.

Lemma Jp_bound_done: forall bytes ob last state cur v s,
  go_inv (bytes, ob) (Bound last state cur) s -> Zlength (os_bound s) = 6 -> Zlength cur = 5 ->
  Jp (bytes, ob) (step (bytes, ob) (Bound last state cur) v) (s_bound_done s (upd_Znth 5 (os_bound s) v)).
Proof.
  intros bytes ob last state cur v s (P & B & W & S & A & Pp & Bb & R & Rc & C) L C5.
  simpl fst in *. rewrite C5 in Bb.
  assert (E: upd_Znth 5 (os_bound s) v = cur ++ [v]) by (apply (prefix_full cur (os_bound s) v 5); auto; lia).
  rewrite step_bound_full by auto. rewrite E.
  unfold Jp, main_ok, s_bound_done; simpl. unfold walk_b.
  destruct (records bytes) as [ [c m] | ]; [ | congruence ]. rewrite Pp, S. simpl pacc.
  destruct (bacc ob state (cur ++ [v])) eqn:Ba; simpl.
  - close_ok.
  - unfold reject. close_ok.
Qed.

(* ---------------------------------------------------------------------- *)
(* ost_ok across the updates                                               *)
(* ---------------------------------------------------------------------- *)

Lemma Forall_upd: forall (P: Z -> Prop) l i x, Forall P l -> P x -> Forall P (upd_Znth i l x).
Proof.
  intros P l i x F Px. destruct (zlt i 0); [ rewrite upd_Znth_out_of_range by lia; auto | ].
  destruct (zlt i (Zlength l)); [ | rewrite upd_Znth_out_of_range by lia; auto ].
  apply Forall_Znth. intros j Hj. rewrite upd_Znth_Zlength in Hj by lia.
  destruct (Z.eq_dec j i) as [-> | N]; [ rewrite upd_Znth_same by lia; auto | ].
  rewrite upd_Znth_diff by lia. apply Forall_Znth; auto.
Qed.

(* ---------------------------------------------------------------------- *)
(* The answered call of each export                                        *)
(* ---------------------------------------------------------------------- *)

Lemma J_snoc_step: forall bytes ob h i st cur v s',
  run (bytes, ob) (start (bytes, ob)) h = Some (Go (Stream i st cur)) ->
  J (bytes, ob) (h ++ [(Step st (44 + Zlength bytes) (o_executing ob) (44 + i) (Znth i bytes) (Zlength cur), v)]) s' =
  Jp (bytes, ob) (step (bytes, ob) (Stream i st cur) v) s'.
Proof. intros. exact (J_snoc (bytes, ob) h (Stream i st cur) v s' H). Qed.

Lemma J_snoc_nmi: forall bytes ob h last st count nmi cur v s',
  run (bytes, ob) (start (bytes, ob)) h = Some (Go (Policy last st count nmi cur)) ->
  J (bytes, ob) (h ++ [(Nmi count nmi (o_routing ob) (Zlength cur), v)]) s' =
  Jp (bytes, ob) (step (bytes, ob) (Policy last st count nmi cur) v) s'.
Proof. intros. exact (J_snoc (bytes, ob) h (Policy last st count nmi cur) v s' H). Qed.

Lemma J_snoc_finish: forall bytes ob h last st cur v s',
  run (bytes, ob) (start (bytes, ob)) h = Some (Go (Bound last st cur)) ->
  J (bytes, ob) (h ++ [(Finish (Znth 1 last) (Znth 2 last) st (44 + Zlength bytes) (o_executing ob)
                          (o_cpuid_edx ob) (o_available ob) (o_apic_base ob) (o_sample_id ob) (Zlength cur), v)]) s' =
  Jp (bytes, ob) (step (bytes, ob) (Bound last st cur) v) s'.
Proof. intros. exact (J_snoc (bytes, ob) h (Bound last st cur) v s' H). Qed.

(* ---------------------------------------------------------------------- *)
(* ost_ok and nmi_ok across the updates                                    *)
(* ---------------------------------------------------------------------- *)

Ltac ost_tac :=
  match goal with O: ost_ok _ |- ost_ok _ =>
    destruct O as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10 & O11 & O12 & O13 & O14 & O15) end;
  unfold ost_ok, u64_ok in *; simpl;
  repeat split; rewrite ?upd_Znth_Zlength by lia; auto; try rep_lia;
  try (apply Forall_upd; auto; unfold u64_ok; lia);
  try (apply Forall_sublist; apply Forall_upd; auto; unfold u64_ok; lia).

Lemma ost_ok_answer: forall s v, ost_ok s -> u64_ok v -> 0 <= os_word s < 16 -> ost_ok (s_answer s v).
Proof. intros. unfold s_answer. ost_tac. Qed.

Lemma ost_ok_policy: forall s v, ost_ok s -> u64_ok v -> 0 <= os_word s < 5 -> ost_ok (s_policy s v).
Proof. intros. unfold s_policy. ost_tac. Qed.

Lemma ost_ok_bound: forall s v, ost_ok s -> u64_ok v -> 0 <= os_word s < 6 -> ost_ok (s_bound s v).
Proof. intros. unfold s_bound. ost_tac. Qed.

Lemma ost_ok_accept: forall s n v, ost_ok s -> u64_ok v -> 0 <= os_byte s < n -> n <= MAX_LENGTH ->
  ost_ok (s_accept s n (upd_Znth 15 (os_answer s) v)).
Proof.
  intros. unfold s_accept. ost_tac.
  all: try (destruct (os_byte s + 1 =? n); unfold MAX_LENGTH in *; rep_lia).
  all: list_solve.
Qed.

Lemma ost_ok_reject: forall s v, ost_ok s -> u64_ok v -> ost_ok (s_reject s (upd_Znth 15 (os_answer s) v)).
Proof. intros. unfold s_reject. ost_tac. all: list_solve. Qed.

Lemma ost_ok_policy_done: forall s v, ost_ok s -> u64_ok v -> ost_ok (s_policy_done s (upd_Znth 4 (os_policy s) v)).
Proof. intros. unfold s_policy_done. ost_tac. all: try (destruct (pacc _); rep_lia). all: list_solve. Qed.

Lemma ost_ok_bound_done: forall s v, ost_ok s -> u64_ok v -> ost_ok (s_bound_done s (upd_Znth 5 (os_bound s) v)).
Proof. intros. unfold s_bound_done. ost_tac. all: list_solve. Qed.

Lemma nmi_ok_same: forall bytes s s', os_count s' = os_count s -> os_nmi s' = os_nmi s -> nmi_ok bytes s -> nmi_ok bytes s'.
Proof. unfold nmi_ok. intros bytes s s' C N K c m E. rewrite C, N. auto. Qed.
