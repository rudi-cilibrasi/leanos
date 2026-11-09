(* Law frame_selection_exact: main's objects as malloc gives them (mres: NULL, or a token and an object of any
   contents), the NULL tests, and the records and the states as the steps take them. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosFrameSelection.harness.frame_selection_exact.code.
Require Import LeanosFrameSelection.proof.Defs.
Require Import LeanosFrameSelection.proof.FrameSpecs.
Require Import LeanosFrameSelection.proof.LawProg LeanosFrameSelection.proof.LawDefs LeanosFrameSelection.proof.LawFacts
  LeanosFrameSelection.proof.LawLib LeanosFrameSelection.proof.LawMainDefs.
Local Open Scope Z_scope.
#[export] Existing Instance LawProg.LCS.

Definition mres (t: type) (p: val) : mpred :=
  if eq_dec p nullval then emp else (malloc_token Ews t p * data_at_ Ews t p)%logic.

Definition isnul (p: val) : bool := if eq_dec p nullval then true else false.

Lemma mres_tc: forall t p (P: mpred), (mres t p * P)%logic |-- denote_tc_test_eq p (Vlong (Int64.repr 0)).
Proof.
  intros t p P. unfold mres. destruct (eq_dec p nullval) as [E | N].
  - subst. apply denote_tc_test_eq_split; apply valid_pointer_zero64; reflexivity.
  - apply denote_tc_test_eq_split; [ | apply valid_pointer_zero64; reflexivity ].
    rewrite sepcon_assoc.
    destruct (Z_le_gt_dec (sizeof t) 0) as [Z | Z].
    + apply sepcon_valid_pointer1. apply malloc_token_valid_pointer; auto.
    + apply sepcon_valid_pointer2. apply sepcon_valid_pointer1.
      apply data_at__valid_ptr; [ apply readable_nonidentity, writable_readable, writable_Ews | lia ].
Qed.

Lemma mres_tc': forall t p (P Q: mpred), P |-- (mres t p * Q)%logic -> P |-- denote_tc_test_eq p (Vlong (Int64.repr 0)).
Proof. intros. eapply derives_trans; [ exact H | apply mres_tc ]. Qed.

Lemma mres_ptr: forall t p, isnul p = false -> mres t p = (malloc_token Ews t p * data_at_ Ews t p)%logic.
Proof. intros t p E. unfold mres, isnul in *. destruct (eq_dec p nullval); [ discriminate | reflexivity ]. Qed.

Lemma isnul_false: forall p, p <> nullval -> isnul p = false.
Proof. intros. unfold isnul. destruct (eq_dec p nullval); [ contradiction | reflexivity ]. Qed.

Lemma null_test2: forall p, is_pointer_or_null p ->
  force_val (sem_cast_i2bool (force_val (sem_cmp_pp Ceq p (Vlong (Int64.repr 0))))) = Vint (Int.repr (Z.b2z (isnul p))).
Proof.
  intros p P. unfold isnul. destruct (eq_dec p nullval) as [E | N].
  - subst. vm_compute. reflexivity.
  - destruct p; try contradiction; simpl in *.
    + subst. exfalso. apply N. reflexivity.
    + vm_compute. reflexivity.
Qed.

Lemma b2z_true: forall b, Int.repr (Z.b2z b) <> Int.zero -> b = true.
Proof. intros [ ] E; [ reflexivity | exfalso; apply E; reflexivity ]. Qed.

Lemma b2z_false: forall b, Int.repr (Z.b2z b) = Int.zero -> b = false.
Proof. intros [ ] E; [ exfalso; exact (Int.one_not_zero E) | reflexivity ]. Qed.

Ltac b2z_hyp :=
  match goal with
  | E: Int.repr (Z.b2z _) <> Int.zero |- _ => apply b2z_true in E
  | E: Int.repr (Z.b2z _) = Int.zero |- _ => apply b2z_false in E
  end.

Ltac rw_bools :=
  repeat match goal with
  | E: ?b = true |- context [?b] => match type of b with bool => rewrite E end
  | E: ?b = false |- context [?b] => match type of b with bool => rewrite E end
  end.

(* ---------------------------------------------------------------------- *)
(* The records and the states as the steps take them                       *)
(* ---------------------------------------------------------------------- *)

Lemma records_cells: forall (cs: compspecs) p a b c, field_compatible (tarray tulong 3) nil p ->
  @data_at cs Ews (tarray tulong 3) [vl a; vl b; vl c] p =
  (@data_at cs Ews tulong (vl a) p * @data_at cs Ews tulong (vl b) (offset_val 8 p) *
   @data_at cs Ews tulong (vl c) (offset_val 16 p))%logic.
Proof.
  intros cs p a b c FC.
  unfold tarray in *.
  erewrite (split3_data_at_Tarray Ews tulong 3 1 2 [vl a; vl b; vl c] [vl a; vl b; vl c] [vl a] [vl b] [vl c] p);
    try reflexivity; try (cbn; lia).
  rewrite !field_address0_offset by auto with field_compatible.
  change (2 - 1) with 1. change (3 - 2) with 1.
  rewrite (data_at_singleton_array_eq Ews tulong (vl a) [vl a]) by reflexivity.
  rewrite (data_at_singleton_array_eq Ews tulong (vl b) [vl b]) by reflexivity.
  rewrite (data_at_singleton_array_eq Ews tulong (vl c) [vl c]) by reflexivity.
  reflexivity.
  split; [ reflexivity | exact I ].
Qed.

Lemma rec_addr: forall p k, isptr p -> 0 <= k <= 2 ->
  force_val (sem_add_ptr_int tulong Signed p (Vint (Int.repr k))) = offset_val (8 * k) p.
Proof.
  intros p k P K. destruct p; try contradiction. simpl. unfold offset_val. f_equal. f_equal.
  unfold Ptrofs.of_ints. rewrite Int.signed_repr by rep_lia. rewrite ptrofs_mul_repr. reflexivity.
Qed.

(* The law's fields but the four frame arguments main passes on after the selection (after_select). *)
Definition lrest4 (q: val) (x: inputs) (sp: val) (mm: mem) (s: lst) : mpred :=
 (field_at Ews t_law (DOT _call) (vi (w_call s)) q *
  field_at Ews t_law (DOT _take_next) (vi (i_take_next x)) q *
  field_at Ews t_law (DOT _running) (vi (w_running s)) q *
  field_at Ews t_law (DOT _manifest) (map vl (i_manifest x)) q *
  field_at Ews t_law (DOT _decoded) (map vl (i_decoded x)) q *
  field_at Ews t_law (DOT _usable) (map vl (i_usable x)) q *
  field_at Ews t_law (DOT _blocked) (map vl (i_blocked x)) q *
  field_at Ews t_law (DOT _reserved_expect) (map vl (m_reserved mm)) q *
  field_at Ews t_law (DOT _terminal_expect) (map vl (m_terminal mm)) q *
  field_at Ews t_law (DOT _states_expect) (states_val (m_states mm)) q *
  field_at Ews t_law (DOT _publication_expect) (map vl (m_publication mm)) q *
  field_at Ews t_law (DOT _rescan_expect) (map vl (m_rescan mm)) q *
  field_at Ews t_law (DOT _selected_expect) (vl (m_selected mm)) q *
  field_at Ews t_law (DOT _manifest_expect) (vl (m_selected_manifest mm)) q *
  field_at Ews t_law (DOT _next_expect) (vl (m_next mm)) q *
  field_at Ews t_law (DOT _decoder_expect) (vi (m_decoder mm)) q *
  field_at Ews t_law (DOT _states) sp q *
  field_at Ews t_law (DOT _step) (vi (w_step s)) q *
  field_at Ews t_law (DOT _expect) (vi (w_expect s)) q *
  field_at Ews t_law (DOT _verdict) (vi (w_verdict s)) q *
  field_at Ews t_law (DOT _block) (vl (w_block s)) q *
  field_at Ews t_law (DOT _word) (vl (w_word s)) q *
  field_at Ews t_law (DOT _candidate) (vl (w_candidate s)) q *
  field_at Ews t_law (DOT _scan) (vi (w_scan s)) q *
  field_at Ews t_law (DOT _manifest_status) (vl (w_ms s)) q *
  field_at Ews t_law (DOT _manifest_error) (vl (w_me s)) q *
  field_at Ews t_law (DOT _free_words) (map vl (w_free s)) q *
  field_at Ews t_law (DOT _candidate_manifest) (vl (w_cm s)) q *
  field_at Ews t_law (DOT _first) (vl (w_first s)) q *
  field_at Ews t_law (DOT _first_manifest) (vl (w_fm s)) q *
  field_at Ews t_law (DOT _second) (vl (w_second s)) q *
  field_at Ews t_law (DOT _answer) (map vl (w_answer s)) q *
  field_at Ews t_law (DOT _scrubbed) (vi (w_scrubbed s)) q)%logic.

Lemma lfields_sel4: forall q x sp mm s, lfields q x sp mm s =
  (field_at Ews t_law (DOT _selected) (vl (i_selected x)) q *
   field_at Ews t_law (DOT _selected_manifest) (vl (i_selected_manifest x)) q *
   field_at Ews t_law (DOT _published) (vl (i_published x)) q *
   field_at Ews t_law (DOT _next) (vl (i_next x)) q * lrest4 q x sp mm s)%logic.
Proof. intros. unfold lfields, lrest4. apply pred_ext; cancel. Qed.

Lemma lfields_sel4_fold: forall q x sp mm s,
  (field_at Ews t_law (DOT _selected) (vl (i_selected x)) q *
   field_at Ews t_law (DOT _selected_manifest) (vl (i_selected_manifest x)) q *
   field_at Ews t_law (DOT _published) (vl (i_published x)) q *
   field_at Ews t_law (DOT _next) (vl (i_next x)) q * lrest4 q x sp mm s)%logic |-- lfields q x sp mm s.
Proof. intros. rewrite lfields_sel4. apply derives_refl. Qed.

Lemma lrest4_after: forall q x m sp mm s, lrest4 q (after_select x m) sp mm s = lrest4 q x sp mm s.
Proof. reflexivity. Qed.

Lemma lrest4_with: forall q x f m sp mm s, lrest4 q (with_step x f m) sp mm s = lrest4 q x sp mm s.
Proof. reflexivity. Qed.

Lemma objs_after: forall x m mm P, objs (after_select x m) mm P = objs x mm P.
Proof. reflexivity. Qed.

Lemma inputs_ok_after: forall y m, inputs_ok y -> mem_ok m -> i_step y = FSelect ->
  inputs_ok (after_select (with_step y FCrossCheck m) m).
Proof.
  intros y m I M F. apply (inputs_ok_next y _ m I M). unfold allocate_next. rewrite F. reflexivity.
Qed.
