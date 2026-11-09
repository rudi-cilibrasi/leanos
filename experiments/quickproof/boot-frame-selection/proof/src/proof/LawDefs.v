(* Law frame_selection_exact: the law's oracle Ora_law (the harness's global `law`, field by field), as the oracle
   predicate of the protocol of FrameSpecs, and the specifications of the harness's helpers.

   The fields of struct law are of three kinds:
   - the step's inputs (Defs.inputs): take_next, the four frame arguments, the manifest, the decoded state, the
     usable and blocked bitmaps;
   - the model's memory (Defs.mem): reserved_expect, terminal_expect, states_expect, publication_expect,
     rescan_expect, selected_expect, manifest_expect, next_expect, decoder_expect;
   - the protocol, the record lst: call, running, step, expect, verdict, block, word, candidate, scan,
     manifest_status, manifest_error, free_words, candidate_manifest, first, first_manifest, second, answer,
     scrubbed;
   and `states`, the header's states pointer sp.
   The record is tied to the model's progress (J): while the step calls (Go g m) it is the stage g's (go_inv, the
   table of Defs), once it returned (Return st m) `expect` is EXPECT_NOTHING and `verdict` st.  main's own record of
   boot_allocate's sequence (call and scrubbed) is tied by seq_ok: the scrub step returned OK only with scrubbed 1,
   and the publication result runs only outside the sequence (call is not CALL_ALLOCATE) or with scrubbed 1. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosFrameSelection.harness.frame_selection_exact.code.
Require Import LeanosFrameSelection.proof.Defs.
Require Import LeanosFrameSelection.proof.FrameSpecs.
Require Import LeanosFrameSelection.proof.LawProg.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[export] Existing Instance LawProg.LCS.

Definition t_law := Tstruct _law__1 noattr.

(* EXPECT_* and STEP_* of harness/frame_selection_exact.h *)
Definition E_MANIFEST : Z := 0.
Definition E_FREE : Z := 1.
Definition E_FINISH : Z := 2.
Definition E_DECODE : Z := 3.
Definition E_CANDIDATE : Z := 4.
Definition E_CONSUME : Z := 5.
Definition E_SCRUB : Z := 6.
Definition E_AUTHORITY : Z := 7.
Definition E_NOTHING : Z := 8.

Definition ST_TERMINAL : Z := 0.
Definition ST_SELECT : Z := 1.
Definition ST_CROSS_CHECK : Z := 2.
Definition ST_SCRUB : Z := 3.
Definition ST_PUBLICATION_RESULT : Z := 4.
Definition ST_PUBLICATION_CHECK : Z := 5.
Definition ST_RESCAN : Z := 6.

(* The protocol's fields of struct law, in its order. *)
Record lst : Type := mk_lst {
  w_call: Z; w_running: Z; w_step: Z; w_expect: Z; w_verdict: Z;
  w_block: Z; w_word: Z; w_candidate: Z; w_scan: Z; w_ms: Z; w_me: Z;
  w_free: list Z; w_cm: Z; w_first: Z; w_fm: Z; w_second: Z; w_answer: list Z; w_scrubbed: Z }.

Ltac lst_cbn := cbn [w_call w_running w_step w_expect w_verdict w_block w_word w_candidate w_scan w_ms w_me
  w_free w_cm w_first w_fm w_second w_answer w_scrubbed] in *.

(* The record with one field changed. *)
Definition set_call s v := mk_lst v (w_running s) (w_step s) (w_expect s) (w_verdict s) (w_block s) (w_word s)
  (w_candidate s) (w_scan s) (w_ms s) (w_me s) (w_free s) (w_cm s) (w_first s) (w_fm s) (w_second s) (w_answer s)
  (w_scrubbed s).
Definition set_running s v := mk_lst (w_call s) v (w_step s) (w_expect s) (w_verdict s) (w_block s) (w_word s)
  (w_candidate s) (w_scan s) (w_ms s) (w_me s) (w_free s) (w_cm s) (w_first s) (w_fm s) (w_second s) (w_answer s)
  (w_scrubbed s).
Definition set_step s v := mk_lst (w_call s) (w_running s) v (w_expect s) (w_verdict s) (w_block s) (w_word s)
  (w_candidate s) (w_scan s) (w_ms s) (w_me s) (w_free s) (w_cm s) (w_first s) (w_fm s) (w_second s) (w_answer s)
  (w_scrubbed s).
Definition set_expect s v := mk_lst (w_call s) (w_running s) (w_step s) v (w_verdict s) (w_block s) (w_word s)
  (w_candidate s) (w_scan s) (w_ms s) (w_me s) (w_free s) (w_cm s) (w_first s) (w_fm s) (w_second s) (w_answer s)
  (w_scrubbed s).
(* stop(m, v) *)
Definition set_stop s v := mk_lst (w_call s) (w_running s) (w_step s) E_NOTHING v (w_block s) (w_word s)
  (w_candidate s) (w_scan s) (w_ms s) (w_me s) (w_free s) (w_cm s) (w_first s) (w_fm s) (w_second s) (w_answer s)
  (w_scrubbed s).
Definition set_block s v := mk_lst (w_call s) (w_running s) (w_step s) (w_expect s) (w_verdict s) v (w_word s)
  (w_candidate s) (w_scan s) (w_ms s) (w_me s) (w_free s) (w_cm s) (w_first s) (w_fm s) (w_second s) (w_answer s)
  (w_scrubbed s).
Definition set_word s v := mk_lst (w_call s) (w_running s) (w_step s) (w_expect s) (w_verdict s) (w_block s) v
  (w_candidate s) (w_scan s) (w_ms s) (w_me s) (w_free s) (w_cm s) (w_first s) (w_fm s) (w_second s) (w_answer s)
  (w_scrubbed s).
Definition set_candidate s v := mk_lst (w_call s) (w_running s) (w_step s) (w_expect s) (w_verdict s) (w_block s)
  (w_word s) v (w_scan s) (w_ms s) (w_me s) (w_free s) (w_cm s) (w_first s) (w_fm s) (w_second s) (w_answer s)
  (w_scrubbed s).
Definition set_scan s v := mk_lst (w_call s) (w_running s) (w_step s) (w_expect s) (w_verdict s) (w_block s)
  (w_word s) (w_candidate s) v (w_ms s) (w_me s) (w_free s) (w_cm s) (w_first s) (w_fm s) (w_second s) (w_answer s)
  (w_scrubbed s).
Definition set_ms s v := mk_lst (w_call s) (w_running s) (w_step s) (w_expect s) (w_verdict s) (w_block s)
  (w_word s) (w_candidate s) (w_scan s) v (w_me s) (w_free s) (w_cm s) (w_first s) (w_fm s) (w_second s)
  (w_answer s) (w_scrubbed s).
Definition set_me s v := mk_lst (w_call s) (w_running s) (w_step s) (w_expect s) (w_verdict s) (w_block s)
  (w_word s) (w_candidate s) (w_scan s) (w_ms s) v (w_free s) (w_cm s) (w_first s) (w_fm s) (w_second s)
  (w_answer s) (w_scrubbed s).
Definition set_free s v := mk_lst (w_call s) (w_running s) (w_step s) (w_expect s) (w_verdict s) (w_block s)
  (w_word s) (w_candidate s) (w_scan s) (w_ms s) (w_me s) v (w_cm s) (w_first s) (w_fm s) (w_second s)
  (w_answer s) (w_scrubbed s).
Definition set_cm s v := mk_lst (w_call s) (w_running s) (w_step s) (w_expect s) (w_verdict s) (w_block s)
  (w_word s) (w_candidate s) (w_scan s) (w_ms s) (w_me s) (w_free s) v (w_first s) (w_fm s) (w_second s)
  (w_answer s) (w_scrubbed s).
Definition set_first s v := mk_lst (w_call s) (w_running s) (w_step s) (w_expect s) (w_verdict s) (w_block s)
  (w_word s) (w_candidate s) (w_scan s) (w_ms s) (w_me s) (w_free s) (w_cm s) v (w_fm s) (w_second s)
  (w_answer s) (w_scrubbed s).
Definition set_fm s v := mk_lst (w_call s) (w_running s) (w_step s) (w_expect s) (w_verdict s) (w_block s)
  (w_word s) (w_candidate s) (w_scan s) (w_ms s) (w_me s) (w_free s) (w_cm s) (w_first s) v (w_second s)
  (w_answer s) (w_scrubbed s).
Definition set_second s v := mk_lst (w_call s) (w_running s) (w_step s) (w_expect s) (w_verdict s) (w_block s)
  (w_word s) (w_candidate s) (w_scan s) (w_ms s) (w_me s) (w_free s) (w_cm s) (w_first s) (w_fm s) v
  (w_answer s) (w_scrubbed s).
Definition set_answer s v := mk_lst (w_call s) (w_running s) (w_step s) (w_expect s) (w_verdict s) (w_block s)
  (w_word s) (w_candidate s) (w_scan s) (w_ms s) (w_me s) (w_free s) (w_cm s) (w_first s) (w_fm s) (w_second s)
  v (w_scrubbed s).
Definition set_scrubbed s v := mk_lst (w_call s) (w_running s) (w_step s) (w_expect s) (w_verdict s) (w_block s)
  (w_word s) (w_candidate s) (w_scan s) (w_ms s) (w_me s) (w_free s) (w_cm s) (w_first s) (w_fm s) (w_second s)
  (w_answer s) v.

Ltac set_unfold := unfold set_call, set_running, set_step, set_expect, set_stop, set_block, set_word, set_candidate,
  set_scan, set_ms, set_me, set_free, set_cm, set_first, set_fm, set_second, set_answer, set_scrubbed in *.

(* struct law, field by field: the step's inputs x, the states pointer sp, the model's memory mm and the record s. *)
Definition lfields (q: val) (x: inputs) (sp: val) (mm: mem) (s: lst) : mpred :=
 (field_at Ews t_law (DOT _call) (vi (w_call s)) q *
  field_at Ews t_law (DOT _take_next) (vi (i_take_next x)) q *
  field_at Ews t_law (DOT _selected) (vl (i_selected x)) q *
  field_at Ews t_law (DOT _selected_manifest) (vl (i_selected_manifest x)) q *
  field_at Ews t_law (DOT _published) (vl (i_published x)) q *
  field_at Ews t_law (DOT _next) (vl (i_next x)) q *
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

(* ---------------------------------------------------------------------- *)
(* The invariant                                                          *)
(* ---------------------------------------------------------------------- *)

(* Every field in its C type's range, the arrays of their lengths. *)
Definition lst_ok (s: lst) : Prop :=
  u32_ok (w_call s) /\ u32_ok (w_running s) /\ u32_ok (w_step s) /\ u32_ok (w_expect s) /\
  u32_ok (w_verdict s) /\ u64_ok (w_block s) /\ u64_ok (w_word s) /\ u64_ok (w_candidate s) /\
  u32_ok (w_scan s) /\ u64_ok (w_ms s) /\ u64_ok (w_me s) /\
  Zlength (w_free s) = BLOCKS /\ Forall u64_ok (w_free s) /\
  u64_ok (w_cm s) /\ u64_ok (w_first s) /\ u64_ok (w_fm s) /\ u64_ok (w_second s) /\
  Zlength (w_answer s) = 4 /\ Forall u64_ok (w_answer s) /\ u32_ok (w_scrubbed s).

(* The stage g's counters (the table of Defs). *)
Definition go_inv (x: inputs) (g: stage) (s: lst) : Prop :=
  match g with
  | ExpectManifest b ms me fw a =>
      w_expect s = E_MANIFEST /\ w_block s = b /\ 0 <= b < BLOCKS /\ w_word s = Zlength a + 1 /\
      Zlength a <= 2 /\ sublist 1 (Zlength a + 1) (w_answer s) = a /\ w_ms s = ms /\ w_me s = me /\
      Zlength fw = b /\ sublist 0 b (w_free s) = fw
  | ExpectFree b ms me fw =>
      w_expect s = E_FREE /\ w_block s = b /\ 0 <= b < BLOCKS /\ w_ms s = ms /\ w_me s = me /\
      Zlength fw = b /\ sublist 0 b (w_free s) = fw
  | ExpectFinish q ms me fw =>
      w_expect s = E_FINISH /\ w_word s = q /\ 0 <= q < TERMINAL_WORDS /\ w_ms s = ms /\ w_me s = me /\
      w_free s = fw
  | ExpectDecode c k f fm =>
      w_expect s = E_DECODE /\ w_step s = ST_SELECT /\ w_candidate s = c /\ 0 <= c < FRAMES /\ w_scan s = k /\
      (k = 0 \/ k = 1) /\ w_first s = f /\ w_fm s = fm /\ w_second s = FRAMES
  | ExpectCandidate c k f fm =>
      w_expect s = E_CANDIDATE /\ w_step s = ST_SELECT /\ w_candidate s = c /\ 0 <= c < FRAMES /\ w_scan s = k /\
      (k = 0 \/ k = 1) /\ w_first s = f /\ w_fm s = fm /\ w_second s = FRAMES
  | ExpectConsume c k f fm cm =>
      w_expect s = E_CONSUME /\ w_step s = ST_SELECT /\ w_candidate s = c /\ 0 <= c < FRAMES /\ w_scan s = k /\
      (k = 0 \/ k = 1) /\ w_first s = f /\ w_fm s = fm /\ w_second s = FRAMES /\ w_cm s = cm
  | ExpectScrub => w_expect s = E_SCRUB
  | ExpectAuthority q => w_expect s = E_AUTHORITY /\ w_word s = q /\ 0 <= q < PUBLICATION_WORDS
  | ExpectRescanDecode =>
      w_expect s = E_DECODE /\ w_step s = ST_RESCAN /\ w_candidate s = i_next x /\ w_scan s = 1
  | ExpectRescanCandidate =>
      w_expect s = E_CANDIDATE /\ w_step s = ST_RESCAN /\ w_candidate s = i_next x /\ w_scan s = 1
  end.

Definition ret_inv (st: Z) (s: lst) : Prop := w_expect s = E_NOTHING /\ w_verdict s = st.

(* main's record of boot_allocate's sequence. *)
Definition seq_ok (x: inputs) (p: progress) (s: lst) : Prop :=
  (i_step x = FPublicationResult -> w_call s <> 0 \/ w_scrubbed s = 1) /\
  (i_step x = FScrub -> forall m, p = Return S_OK m -> w_scrubbed s = 1).

Definition mem_of (p: progress) : mem := match p with Go _ m => m | Return _ m => m end.

Definition J (x: inputs) (p: progress) (s: lst) : Prop :=
  lst_ok s /\ seq_ok x p s /\
  match p with Go g _ => go_inv x g s | Return st _ => ret_inv st s end.

(* The law's oracle: the global `law`, both contexts, with the states at sp. *)
Definition Ora_law : ORA := fun gv dctx sctx sp x h =>
  EX p: progress, EX s: lst,
    !! (dctx = gv _law /\ sctx = gv _law /\ inputs_ok x /\ answers_ok h /\ run x (start x) h = Some p /\
        J x p s) &&
    lfields (gv _law) x sp (mem_of p) s.

(* ---------------------------------------------------------------------- *)
(* main's objects                                                          *)
(* ---------------------------------------------------------------------- *)

(* The pointers main mallocs. *)
Record ptrs : Type := mk_ptrs {
  p_manifest: val; p_decoded: val; p_usable: val; p_blocked: val; p_reserved: val; p_terminal: val;
  p_states: val; p_publication: val; p_rescan: val; p_records: val; p_decoder: val }.

Definition t_records := tarray tulong 3.

(* main's objects: the inputs of x, the memory mm. *)
Definition objs (x: inputs) (mm: mem) (P: ptrs) : mpred :=
 (data_at Ews t_manifest (map vl (i_manifest x)) (p_manifest P) *
  data_at Ews t_state (map vl (i_decoded x)) (p_decoded P) *
  data_at Ews t_bitmap (map vl (i_usable x)) (p_usable P) *
  data_at Ews t_bitmap (map vl (i_blocked x)) (p_blocked P) *
  data_at Ews t_bitmap (map vl (m_reserved mm)) (p_reserved P) *
  data_at Ews t_terminal (map vl (m_terminal mm)) (p_terminal P) *
  data_at Ews t_states (states_val (m_states mm)) (p_states P) *
  data_at Ews t_publication (map vl (m_publication mm)) (p_publication P) *
  data_at Ews t_rescan (map vl (m_rescan mm)) (p_rescan P) *
  data_at Ews t_records (map vl [m_selected mm; m_selected_manifest mm; m_next mm]) (p_records P) *
  data_at Ews tuint (vi (m_decoder mm)) (p_decoder P))%logic.

(* ---------------------------------------------------------------------- *)
(* The harness's helpers                                                   *)
(* ---------------------------------------------------------------------- *)

Definition any_u64_spec :=
  DECLARE _any_u64
  WITH u: unit
  PRE [ ] PROP () PARAMS () SEP ()
  POST [ tulong ] EX v: Z, PROP (u64_ok v) RETURN (vl v) SEP ().

Definition stop_spec :=
  DECLARE _stop
  WITH q: val, e0: val, v0: val, v: Z
  PRE [ tptr t_law, tuint ]
    PROP () PARAMS (q; vi v)
    SEP (field_at Ews t_law (DOT _expect) e0 q; field_at Ews t_law (DOT _verdict) v0 q)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (field_at Ews t_law (DOT _expect) (vi E_NOTHING) q; field_at Ews t_law (DOT _verdict) (vi v) q).

(* same_manifest(words), words holding the law's manifest. *)
Definition same_manifest_spec :=
  DECLARE _same_manifest
  WITH gv: globals, wp: val, ms: list Z, sh: share
  PRE [ tptr tulong ]
    PROP (readable_share sh; Zlength ms = MANIFEST_WORDS)
    PARAMS (wp) GLOBALS (gv)
    SEP (data_at sh t_manifest (map vl ms) wp; field_at Ews t_law (DOT _manifest) (map vl ms) (gv _law))
  POST [ tint ]
    PROP () RETURN (Vint Int.one)
    SEP (data_at sh t_manifest (map vl ms) wp; field_at Ews t_law (DOT _manifest) (map vl ms) (gv _law)).

(* select_done(m): the records' model from first, first_manifest and second, then stop(m, OK). *)
Definition select_done_spec :=
  DECLARE _select_done
  WITH q: val, f: Z, fm: Z, n: Z, se: val, me: val, ne: val, e0: val, v0: val
  PRE [ tptr t_law ]
    PROP () PARAMS (q)
    SEP (field_at Ews t_law (DOT _first) (vl f) q; field_at Ews t_law (DOT _first_manifest) (vl fm) q;
         field_at Ews t_law (DOT _second) (vl n) q;
         field_at Ews t_law (DOT _selected_expect) se q; field_at Ews t_law (DOT _manifest_expect) me q;
         field_at Ews t_law (DOT _next_expect) ne q;
         field_at Ews t_law (DOT _expect) e0 q; field_at Ews t_law (DOT _verdict) v0 q)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (field_at Ews t_law (DOT _first) (vl f) q; field_at Ews t_law (DOT _first_manifest) (vl fm) q;
         field_at Ews t_law (DOT _second) (vl n) q;
         field_at Ews t_law (DOT _selected_expect) (vl f) q; field_at Ews t_law (DOT _manifest_expect) (vl fm) q;
         field_at Ews t_law (DOT _next_expect) (vl n) q;
         field_at Ews t_law (DOT _expect) (vi E_NOTHING) q; field_at Ews t_law (DOT _verdict) (vi S_OK) q).

(* next_candidate(m), at candidate c: the next candidate, or after 4095 select_done. *)
Definition next_candidate_spec :=
  DECLARE _next_candidate
  WITH q: val, c: Z, f: Z, fm: Z, n: Z, se: val, me: val, ne: val, e0: val, v0: val
  PRE [ tptr t_law ]
    PROP (0 <= c < FRAMES) PARAMS (q)
    SEP (field_at Ews t_law (DOT _candidate) (vl c) q;
         field_at Ews t_law (DOT _first) (vl f) q; field_at Ews t_law (DOT _first_manifest) (vl fm) q;
         field_at Ews t_law (DOT _second) (vl n) q;
         field_at Ews t_law (DOT _selected_expect) se q; field_at Ews t_law (DOT _manifest_expect) me q;
         field_at Ews t_law (DOT _next_expect) ne q;
         field_at Ews t_law (DOT _expect) e0 q; field_at Ews t_law (DOT _verdict) v0 q)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (field_at Ews t_law (DOT _candidate) (vl (if c + 1 <? FRAMES then c + 1 else c)) q;
         field_at Ews t_law (DOT _first) (vl f) q; field_at Ews t_law (DOT _first_manifest) (vl fm) q;
         field_at Ews t_law (DOT _second) (vl n) q;
         field_at Ews t_law (DOT _selected_expect) (if c + 1 <? FRAMES then se else vl f) q;
         field_at Ews t_law (DOT _manifest_expect) (if c + 1 <? FRAMES then me else vl fm) q;
         field_at Ews t_law (DOT _next_expect) (if c + 1 <? FRAMES then ne else vl n) q;
         field_at Ews t_law (DOT _expect) (vi (if c + 1 <? FRAMES then E_DECODE else E_NOTHING)) q;
         field_at Ews t_law (DOT _verdict) (if c + 1 <? FRAMES then v0 else vi S_OK) q).

(* begin_*(m): the model's start of the step f, from the memory before it. *)
Definition begin_pre_post (name: ident) (f: func) :=
  DECLARE name
  WITH q: val, x: inputs, sp: val, s: lst
  PRE [ tptr t_law ]
    PROP (i_step x = f; inputs_ok x; lst_ok s; seq_ok x (start x) s)
    PARAMS (q)
    SEP (lfields q x sp (i_mem x) s)
  POST [ tvoid ]
    EX s': lst,
    PROP (J x (start x) s')
    RETURN ()
    SEP (lfields q x sp (i_mem x) s').

Definition begin_terminal_spec := begin_pre_post _begin_terminal FTerminal.
Definition begin_select_spec := begin_pre_post _begin_select FSelect.
Definition begin_cross_check_spec := begin_pre_post _begin_cross_check FCrossCheck.
Definition begin_scrub_spec := begin_pre_post _begin_scrub FScrub.
Definition begin_publication_result_spec := begin_pre_post _begin_publication_result FPublicationResult.
Definition begin_publication_check_spec := begin_pre_post _begin_publication_check FPublicationCheck.
Definition begin_rescan_spec := begin_pre_post _begin_rescan FRescan.

(* check_step(m, status, ...): the step returned (EXPECT_NOTHING, verdict status), main's objects hold the inputs
   and the law's model of memory. *)
Definition check_step_spec :=
  DECLARE _check_step
  WITH q: val, x: inputs, mm: mem, s: lst, P: ptrs, st: Z
  PRE [ tptr t_law, tuint, tptr tulong, tptr tulong, tptr tulong, tptr tulong, tptr tulong, tptr tulong,
        tptr (tarray tulong 41), tptr tulong, tptr tulong, tptr tulong, tptr tuint ]
    PROP (w_expect s = E_NOTHING; w_verdict s = st; inputs_ok x; mem_ok mm)
    PARAMS (q; vi st; p_manifest P; p_decoded P; p_usable P; p_blocked P; p_reserved P; p_terminal P;
            p_states P; p_publication P; p_rescan P; p_records P; p_decoder P)
    SEP (lfields q x (p_states P) mm s; objs x mm P)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (lfields q x (p_states P) mm s; objs x mm P).

(* The global variable of the harness, for the functions that use it. *)
Definition Vlaw : varspecs := [(_law, t_law)].
