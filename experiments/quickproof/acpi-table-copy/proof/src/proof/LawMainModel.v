(* Law table_copy_exact: two facts of the model main's checks compare pointers by: once the result's root or its
   entries are written, the root arena holds at least a header; every copy slot's offset lies inside the table
   arena.  By induction on the model's run; no program here. *)
Require Import VST.floyd.proofauto.
Require Import LeanosAcpi.proof.Defs.
Require Import LeanosAcpi.proof.AcpiSpecs.
Require Import LeanosAcpi.proof.LawModel.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* What main's pointer comparisons need of a mem. *)
Definition eok (x: inputs) (m: mem) : Prop :=
  ((m_root_copy m <> None \/ m_entries m <> None) -> HEADER_BYTES <= root_capacity x) /\
  Forall (fun sd => 0 <= s_offset sd < table_capacity x) (m_slots m).

(* What a stage carries for it: a table's offset inside the arena, a copy's length as the header check let it. *)
Definition gok (x: inputs) (st: stage) : Prop :=
  match st with
  | Copying g c =>
      match g with TRoot => True | TTable l => 0 <= l_offset l < table_capacity x end /\
      match c with
      | CHeader => True
      | CBody len => HEADER_BYTES <= len <= MAX_SDT_BYTES /\ len <= capacity_of x g
      | CChunk len _ _ _ _ => HEADER_BYTES <= len <= MAX_SDT_BYTES /\ len <= capacity_of x g
      end
  | Sequencing l _ => 0 <= l_offset l
  end.

Definition pok (x: inputs) (p: progress) : Prop :=
  match p with Go st m => gok x st /\ eok x m | Return _ _ m => eok x m end.

Lemma eok_write: forall x m d bs, eok x m -> eok x (write m d bs).
Proof. intros x m [ | | off] bs E; exact E. Qed.

Lemma eok_initial: forall x, eok x (initial x).
Proof.
  intros. split; [ intros [H | H]; contradiction H; reflexivity | constructor ].
Qed.

Lemma pok_begin_sdt: forall x g m, eok x m ->
  match g with TRoot => True | TTable l => 0 <= l_offset l < table_capacity x end -> pok x (begin_sdt x g m).
Proof.
  intros x g m E G. unfold begin_sdt. destruct (_ <? _); [ exact E | ].
  split; [ split; [ exact G | exact I ] | exact E ].
Qed.

Lemma pok_begin_table: forall x l m, eok x m -> 0 <= l_offset l -> pok x (begin_table x l m).
Proof.
  intros x l m E L. unfold begin_table. destruct (table_capacity x <=? l_offset l) eqn:B; [ exact E | ].
  apply Z.leb_gt in B. apply pok_begin_sdt; [ exact E | lia ].
Qed.

Lemma pok_tables_start: forall x addresses m, eok x m -> pok x (tables_start x addresses m).
Proof.
  intros x addresses m E. unfold tables_start. destruct (_ =? 0); [ exact E | ].
  apply pok_begin_table; [ exact E | simpl; lia ].
Qed.

Lemma pok_tables_done: forall x count m, eok x m -> pok x (tables_done count m).
Proof. intros x count m E. unfold tables_done. destruct (select_madt m); exact E. Qed.

Lemma pok_root_copied: forall x len cursor m, eok x m -> HEADER_BYTES <= root_capacity x ->
  pok x (root_copied x len cursor m).
Proof.
  intros x len cursor m [E1 E2] H.
  assert (E: forall m', m_slots m' = m_slots m -> eok x m').
  { intros m' Em. split; [ intros; exact H | rewrite Em; exact E2 ]. }
  unfold root_copied. cbv zeta.
  destruct (negb _); [ (cbn [pok]; apply E; reflexivity) | ].
  destruct (decode_entries _ _) as [st | [count w]]; [ (cbn [pok]; apply E; reflexivity) | ].
  destruct (decode_addresses _ _ _) as [st | addresses]; [ (cbn [pok]; apply E; reflexivity) | ].
  apply pok_tables_start. (cbn [pok]; apply E; reflexivity).
Qed.

Lemma pok_table_copied: forall x l len cursor m, eok x m -> 0 <= l_offset l < table_capacity x ->
  HEADER_BYTES <= len <= MAX_SDT_BYTES -> pok x (table_copied x l len cursor m).
Proof.
  intros x l len cursor m [E1 E2] L B. unfold table_copied. cbv zeta.
  assert (E: eok x (add_slot m (mk_sdt (Znth (l_entry l) (l_addresses l)) (l_offset l) len (cursor mod 2 ^ 32)))).
  { split; [ exact E1 | ]. unfold add_slot. simpl.
    apply Forall_app. split; [ exact E2 | constructor; [ simpl; lia | constructor ] ]. }
  destruct (_ <? padded len); [ exact E | ].
  destruct (negb _); [ exact E | ].
  split; [ | exact E ]. simpl.
  pose proof (padded_range len ltac:(unfold HEADER_BYTES in B; lia)). lia.
Qed.

Lemma pok_step: forall x st m r, gok x st -> eok x m -> pok x (step x st m r).
Proof.
  intros x st m r G E. destruct st as [g c | l cur].
  - destruct G as [Gg Gc]. destruct c as [ | len | len bs cursor byte cur]; unfold step; cbv zeta.
    + destruct (reply_value r =? 0); [ exact (eok_write _ _ _ _ E) | ].
      destruct ((_ <? HEADER_BYTES) || (MAX_SDT_BYTES <? _) || (capacity_of x g <? _)) eqn:B;
        [ exact (eok_write _ _ _ _ E) | ].
      apply orb_false_iff in B as [B B3]. apply orb_false_iff in B as [B1 B2].
      apply Z.ltb_ge in B1. apply Z.ltb_ge in B2. apply Z.ltb_ge in B3.
      split; [ split; [ exact Gg | lia ] | exact (eok_write _ _ _ _ E) ].
    + destruct (reply_value r =? 0); [ exact (eok_write _ _ _ _ E) | ].
      split; [ split; [ exact Gg | exact Gc ] | exact (eok_write _ _ _ _ E) ].
    + destruct (_ <? 5); [ split; [ split; [ exact Gg | exact Gc ] | exact E ] | ].
      destruct (negb _); [ exact E | ].
      destruct (_ <? len); [ split; [ split; [ exact Gg | exact Gc ] | exact E ] | ].
      destruct g as [ | l]; cbn [sdt_copied].
      * apply pok_root_copied; [ exact E | ]. cbn [capacity_of] in Gc. lia.
      * apply pok_table_copied; [ exact E | exact Gg | lia ].
  - unfold step. cbv zeta.
    destruct (_ <? 3); [ split; [ exact G | exact E ] | ].
    destruct (_ || _ || _); [ exact E | ].
    destruct (_ <? _).
    + apply pok_begin_table; [ exact E | exact G ].
    + apply pok_tables_done. exact E.
Qed.

Lemma pok_run: forall x h p p', pok x p -> run x p h = Some p' -> pok x p'.
Proof.
  intros x h. induction h as [ | [c r] h IH]; intros p p' P R; simpl in R.
  - injection R as <-. exact P.
  - destruct p as [st m | st pub m]; [ | discriminate ].
    destruct (_ && _); [ | discriminate ].
    destruct P as [P1 P2]. exact (IH _ _ (pok_step x st m r P1 P2) R).
Qed.

Lemma pok_start: forall x, pok x (start x).
Proof.
  intros. unfold start. destruct (_ || _); [ apply eok_initial | ].
  apply pok_begin_sdt; [ apply eok_initial | exact I ].
Qed.

Lemma run_eok: forall x h st pub m, run x (start x) h = Some (Return st pub m) -> eok x m.
Proof. intros x h st pub m R. exact (pok_run x h _ _ (pok_start x) R). Qed.

(* The MADT's index is a slot's. *)
Lemma select_from_range: forall tables ss k sel i, 0 <= k -> (forall j, sel = Some j -> 0 <= j < k) ->
  select_from tables ss k sel = inr i -> 0 <= i < k + Zlength ss.
Proof.
  intros tables ss. induction ss as [ | sd ss IH]; intros k sel i K S R; simpl in R.
  - destruct sel as [j | ]; [ | discriminate ]. injection R as <-. rewrite Zlength_nil. specialize (S j eq_refl). lia.
  - rewrite Zlength_cons.
    destruct (negb _); [ discriminate | ].
    destruct (signature_matches _ _ _).
    + destruct sel as [j | ]; [ discriminate | ].
      pose proof (IH (k + 1) (Some k) i ltac:(lia) ltac:(intros j E; injection E as <-; lia) R). lia.
    + pose proof (IH (k + 1) sel i ltac:(lia) ltac:(intros j E; specialize (S j E); lia) R). lia.
Qed.

Lemma select_madt_range: forall m i, select_madt m = inr i -> 0 <= i < Zlength (m_slots m).
Proof.
  intros m i R. pose proof (select_from_range _ _ 0 None i (Z.le_refl 0) ltac:(intros j E; discriminate) R). lia.
Qed.
