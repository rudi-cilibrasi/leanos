(* Law frame_selection_exact: what the parts of the proof of main share: main's context and return assertion, the
   statements from each step's turn on (then main's final return), main's state between the steps (main_pre: the
   law's fields and main's objects agree, as the inputs y with their memory i_mem y), the tail lemmas' statements,
   the objects between the law's compspecs and the unit's, and what a step's run keeps. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosFrameSelection.harness.frame_selection_exact.code.
Require Import LeanosFrameSelection.proof.Defs.
Require Import LeanosFrameSelection.proof.FrameSpecs.
Require Import LeanosFrameSelection.proof.LawProg LeanosFrameSelection.proof.LawDefs LeanosFrameSelection.proof.LawFacts
  LeanosFrameSelection.proof.LawLib.
Local Open Scope Z_scope.
#[export] Existing Instance LawProg.LCS.

Definition Gmain : funspecs :=
  [any_u64_spec; (_quickproof_malloc, malloc_spec');
   begin_terminal_spec; begin_select_spec; begin_cross_check_spec; begin_scrub_spec;
   begin_publication_result_spec; begin_publication_check_spec; begin_rescan_spec; check_step_spec;
   (_law_decode, decode_spec Ora_law); (_law_scrub, scrub_spec Ora_law);
   frame_terminal_spec Ora_law; frame_select_spec Ora_law; frame_cross_check_spec Ora_law;
   frame_scrub_selected_spec Ora_law; frame_publication_result_spec Ora_law; frame_publication_check_spec Ora_law;
   frame_rescan_spec Ora_law].

(* main's type context and return assertion, as start_function makes them. *)
Definition Delta0 : tycontext := func_tycontext f_main Vlaw Gmain nil.
Definition Post0 : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(* The statements of main from the first statement of the inner block matched by `first` (then the rest of the
   block), then main's final return. *)
Ltac main_from first :=
  let b := eval cbv delta [f_main] beta iota zeta in (fn_body f_main) in
  match b with
  | context [Ssequence (Ssequence ?s1 ?s2) ?rest] =>
      first s1;
      exact (Ssequence (Ssequence (Ssequence s1 s2) rest) (Sreturn (Some (Econst_int (Int.repr 0) tint))))
  end.

(* From the terminal's turn (`if (sequence || m->call == CALL_TERMINAL)`). *)
Definition s_terminal : statement :=
  ltac:(main_from ltac:(fun s => match s with Sifthenelse (Etempvar _sequence tuint) (Sset _t'42 _) _ => idtac end)).
Definition s_select : statement :=
  ltac:(main_from ltac:(fun s => match s with
    Ssequence (Sifthenelse (Etempvar _sequence tuint) (Sset _t'44 _) _) _ => idtac end)).
Definition s_cross : statement :=
  ltac:(main_from ltac:(fun s => match s with
    Ssequence (Sifthenelse (Etempvar _sequence tuint) (Sset _t'47 _) _) _ => idtac end)).
Definition s_scrub : statement :=
  ltac:(main_from ltac:(fun s => match s with
    Ssequence (Sifthenelse (Etempvar _sequence tuint) (Sset _t'50 _) _) _ => idtac end)).
Definition s_pub : statement :=
  ltac:(main_from ltac:(fun s => match s with
    Ssequence (Sifthenelse (Etempvar _sequence tuint) (Sset _t'53 _) _) _ => idtac end)).
Definition s_rescan : statement :=
  ltac:(main_from ltac:(fun s => match s with
    Ssequence (Ssequence (Sifthenelse (Etempvar _sequence tuint) (Sset _t'56 _) _) _) _ => idtac end)).

(* ---------------------------------------------------------------------- *)
(* main's state between the steps                                          *)
(* ---------------------------------------------------------------------- *)

Definition ptrs_ok (P: ptrs) : Prop :=
  isptr (p_manifest P) /\ isptr (p_decoded P) /\ isptr (p_usable P) /\ isptr (p_blocked P) /\
  isptr (p_reserved P) /\ isptr (p_terminal P) /\ isptr (p_states P) /\ isptr (p_publication P) /\
  isptr (p_rescan P) /\ isptr (p_records P) /\ isptr (p_decoder P).

(* The law's fields with the inputs y (the frame arguments, the objects no step writes) and the memory i_mem y, the
   record s; main's objects the same; sequence sq and status st. *)
Definition main_pre (gv: globals) (P: ptrs) (y: inputs) (s: lst) (sq st: Z) : environ -> mpred :=
  PROP ()
  LOCAL (temp _status (vi st); temp _sequence (vi sq); temp _m (gv _law);
         temp _manifest (p_manifest P); temp _decoded (p_decoded P); temp _usable (p_usable P);
         temp _blocked (p_blocked P); temp _reserved (p_reserved P); temp _terminal (p_terminal P);
         temp _states (p_states P); temp _publication (p_publication P); temp _rescan (p_rescan P);
         temp _records (p_records P); temp _decoder_record (p_decoder P); gvars gv)
  SEP (lfields (gv _law) y (p_states P) (i_mem y) s; objs y (i_mem y) P; TT).

Definition main_ok (P: ptrs) (y: inputs) (s: lst) (sq st: Z) : Prop :=
  inputs_ok y /\ lst_ok s /\ ptrs_ok P /\ (sq = 0 \/ sq = 1) /\ u32_ok st.

(* A tail of main from the statement c0 on, from main_pre with the facts Q: the inputs y are the next step's
   (their i_step), with the memory before it. *)
Definition tail_ok {Espec: OracleKind} (c0: statement) (Q: inputs -> lst -> Z -> Z -> Prop) : Prop :=
  forall gv P y s sq st, main_ok P y s sq st -> Q y s sq st ->
  forall Delta R c, Delta = Delta0 -> R = Post0 -> c = c0 ->
  semax Delta (main_pre gv P y s sq st) c R.

Definition at_step (f: func) (y: inputs) (s: lst) (sq st: Z) : Prop := i_step y = f.

(* Before the publication: in boot_allocate's sequence with every step OK so far, the scrub answered 1. *)
Definition pub_fact (y: inputs) (s: lst) (sq st: Z) : Prop :=
  i_step y = FPublicationResult /\ (sq = 1 -> st = 0 -> w_scrubbed s = 1).

(* ---------------------------------------------------------------------- *)
(* The objects at the unit's compspecs                                     *)
(* ---------------------------------------------------------------------- *)

Definition objs_cs (x: inputs) (mm: mem) (P: ptrs) : mpred :=
 (@data_at FrameSpecs.CS Ews t_manifest (map vl (i_manifest x)) (p_manifest P) *
  @data_at FrameSpecs.CS Ews t_state (map vl (i_decoded x)) (p_decoded P) *
  @data_at FrameSpecs.CS Ews t_bitmap (map vl (i_usable x)) (p_usable P) *
  @data_at FrameSpecs.CS Ews t_bitmap (map vl (i_blocked x)) (p_blocked P) *
  @data_at FrameSpecs.CS Ews t_bitmap (map vl (m_reserved mm)) (p_reserved P) *
  @data_at FrameSpecs.CS Ews t_terminal (map vl (m_terminal mm)) (p_terminal P) *
  @data_at FrameSpecs.CS Ews t_states (states_val (m_states mm)) (p_states P) *
  @data_at FrameSpecs.CS Ews t_publication (map vl (m_publication mm)) (p_publication P) *
  @data_at FrameSpecs.CS Ews t_rescan (map vl (m_rescan mm)) (p_rescan P) *
  @data_at FrameSpecs.CS Ews t_records (map vl [m_selected mm; m_selected_manifest mm; m_next mm]) (p_records P) *
  @data_at FrameSpecs.CS Ews tuint (vi (m_decoder mm)) (p_decoder P))%logic.

Lemma objs_to_cs: forall x mm P, objs x mm P = objs_cs x mm P.
Proof.
  intros. unfold objs, objs_cs, t_manifest, t_state, t_bitmap, t_terminal, t_publication, t_rescan, t_records.
  rewrite !(data_at_arr_cs LCS FrameSpecs.CS), (data_at_states_cs LCS FrameSpecs.CS),
    (data_at_uint_cs LCS FrameSpecs.CS).
  reflexivity.
Qed.

Lemma objs_cs_fold: forall x mm P,
 (@data_at FrameSpecs.CS Ews t_manifest (map vl (i_manifest x)) (p_manifest P) *
  @data_at FrameSpecs.CS Ews t_state (map vl (i_decoded x)) (p_decoded P) *
  @data_at FrameSpecs.CS Ews t_bitmap (map vl (i_usable x)) (p_usable P) *
  @data_at FrameSpecs.CS Ews t_bitmap (map vl (i_blocked x)) (p_blocked P) *
  @data_at FrameSpecs.CS Ews t_bitmap (map vl (m_reserved mm)) (p_reserved P) *
  @data_at FrameSpecs.CS Ews t_terminal (map vl (m_terminal mm)) (p_terminal P) *
  @data_at FrameSpecs.CS Ews t_states (states_val (m_states mm)) (p_states P) *
  @data_at FrameSpecs.CS Ews t_publication (map vl (m_publication mm)) (p_publication P) *
  @data_at FrameSpecs.CS Ews t_rescan (map vl (m_rescan mm)) (p_rescan P) *
  @data_at FrameSpecs.CS Ews t_records (map vl [m_selected mm; m_selected_manifest mm; m_next mm]) (p_records P) *
  @data_at FrameSpecs.CS Ews tuint (vi (m_decoder mm)) (p_decoder P))%logic
  |-- objs x mm P.
Proof. intros. rewrite objs_to_cs. apply derives_refl. Qed.

(* ---------------------------------------------------------------------- *)
(* The steps' inputs and what a run keeps                                  *)
(* ---------------------------------------------------------------------- *)

Lemma inputs_ok_with: forall y f m, inputs_ok y -> mem_ok m -> inputs_ok (with_step y f m).
Proof. intros y f m I M. unfold inputs_ok, with_step in *; cbn. tauto. Qed.

Lemma inputs_ok_here: forall y f, inputs_ok y -> inputs_ok (with_step y f (i_mem y)).
Proof. intros y f I. apply inputs_ok_with; auto. apply I. Qed.

(* The memory a step's run returns, against the memory before it: what the step does not write. *)
Lemma keeps_terminal: forall x m, i_step x = FTerminal -> keeps x m ->
  m = with_terminal (with_reserved (i_mem x) (m_reserved m)) (m_terminal m).
Proof. intros x m F K. unfold keeps in K. rewrite F in K. exact K. Qed.

Lemma keeps_select: forall x m, i_step x = FSelect -> keeps x m ->
  m = with_decoder (with_records (with_states (i_mem x) (m_states m)) (m_selected m) (m_selected_manifest m)
                                 (m_next m)) (m_decoder m).
Proof. intros x m F K. unfold keeps in K. rewrite F in K. exact K. Qed.

Lemma keeps_none: forall x m, (i_step x = FCrossCheck \/ i_step x = FScrub \/ i_step x = FPublicationCheck) ->
  keeps x m -> m = i_mem x.
Proof. intros x m F K. unfold keeps in K. destruct F as [F | [F | F]]; rewrite F in K; exact K. Qed.

Lemma keeps_publication: forall x m, i_step x = FPublicationResult -> keeps x m ->
  m = with_publication (i_mem x) (m_publication m).
Proof. intros x m F K. unfold keeps in K. rewrite F in K. exact K. Qed.

Lemma keeps_rescan: forall x m, i_step x = FRescan -> keeps x m ->
  m = with_decoder (with_rescan (with_state (i_mem x) 1 (Znth 1 (m_states m))) (m_rescan m)) (m_decoder m).
Proof. intros x m F K. unfold keeps in K. rewrite F in K. exact K. Qed.

(* The law's fields do not depend on the step of the inputs. *)
(* The memory m as the inputs of step f. *)
Definition next_at (y: inputs) (f: func) (m: mem) : inputs := with_step y f m.

Lemma lfields_with: forall q y f m sp mm s, lfields q (with_step y f m) sp mm s = lfields q y sp mm s.
Proof. reflexivity. Qed.

Lemma objs_with: forall y f m mm P, objs (with_step y f m) mm P = objs y mm P.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* Tactics                                                                 *)
(* ---------------------------------------------------------------------- *)

(* Enter a tail lemma: VST's canonical form of the goal, as start_function leaves it. *)
Ltac start_main_tail :=
  unfold Delta0, Post0;
  repeat match goal with
  | |- context [Sloop (Ssequence (Sifthenelse ?e Sskip Sbreak) ?s) Sskip] => fold (Swhile e s)
  | |- context [Ssequence ?s1 (Sloop (Ssequence (Sifthenelse ?e Sskip Sbreak) ?s2) ?s3) ] =>
      match s3 with
      | Sset ?i _ => match s1 with Sset ?i' _ => unify i i' | Sskip => idtac end
      end;
      fold (Sfor s1 e s2 s3)
  end;
  simplify_func_tycontext;
  abbreviate_semax.
