(* Law handoff_decode_exact: the law's oracle Ora_law (the harness's global `law` as its fields, its copy_expect
   array and, for a call alone, its info_expect array), as the oracle predicate of the protocol of HandoffSpecs,
   and the specifications of the harness's helpers.

   The fields of struct law are of three kinds:
   - main's inputs, fixed during the call: call, magic, address, candidate (target x) and projection;
   - the model's memory (Defs.mem): total, the three bitmaps, the two states, at and extent_ok, with the copy
     (copy_expect's array);
   - the protocol, the record lst: running, records, expect, verdict, chunk, word, block, value, stream, answer.
   The record is tied to the model's progress (J): while the header calls (Go g m) it is the stage g's (go_inv:
   `expect` the stage's EXPECT_*, `chunk`, `block`, `value`, `stream` its counters, `answer` its answers so far,
   `word` their number), and once it returned (Return st m) `expect` is EXPECT_NOTHING and `verdict` st.  running,
   records and the counters of other stages are left unconstrained. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosHandoff.harness.handoff_decode_exact.code.
Require Import LeanosHandoff.proof.Defs.
Require Import LeanosHandoff.proof.HandoffSpecs.
Require Import LeanosHandoff.proof.LawProg.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[export] Existing Instance LawProg.LCS.

Definition t_law := Tstruct _law__1 noattr.

(* EXPECT_* and CALL_* of harness/handoff_decode_exact.h *)
Definition E_SIZE : Z := 0.
Definition E_STREAM_INIT : Z := 1.
Definition E_CHUNK : Z := 2.
Definition E_STREAM_STEP : Z := 3.
Definition E_DECODE_INIT : Z := 4.
Definition E_DECODE_STEP : Z := 5.
Definition E_RECORD : Z := 6.
Definition E_ENTRY : Z := 7.
Definition E_NOTHING : Z := 8.

Definition call_code (f: func) : Z :=
  match f with FAllocate => 0 | FCopy => 1 | FProjection => 2 | FCandidate => 3 end.

Definition proj_code (x: inputs) : Z := if projection x then 1 else 0.

(* The copy's words: 8192 for an allocation or a copy, none for a decoder alone. *)
Definition copy_len (x: inputs) : Z := match i_call x with FAllocate | FCopy => COPY_WORDS | _ => 0 end.

Definition is_alloc (x: inputs) : bool := match i_call x with FAllocate => true | _ => false end.

(* The calls whose callees write a copy: an allocation and a copy alone. *)
Definition has_copy (x: inputs) : bool := match i_call x with FAllocate | FCopy => true | _ => false end.

(* The protocol's fields of struct law, in its order. *)
Record lst : Type := mk_lst {
  w_running: Z; w_records: Z; w_expect: Z; w_verdict: Z;
  w_chunk: Z; w_word: Z; w_block: Z; w_value: Z;
  w_stream: list Z; w_answer: list Z }.

Ltac lst_cbn := cbn [w_running w_records w_expect w_verdict w_chunk w_word w_block w_value w_stream w_answer] in *.

(* struct law, field by field: the inputs x, the arrays' pointers ce (copy_expect) and ie (info_expect), the model's
   memory m and the record s. *)
Definition lfields (q: val) (x: inputs) (ce ie: val) (m: mem) (s: lst) : mpred :=
 (field_at Ews t_law (DOT _call) (vi (call_code (i_call x))) q *
  field_at Ews t_law (DOT _magic) (vi (i_magic x)) q *
  field_at Ews t_law (DOT _address) (vi (i_address x)) q *
  field_at Ews t_law (DOT _total) (vi (m_total m)) q *
  field_at Ews t_law (DOT _candidate) (vl (target x)) q *
  field_at Ews t_law (DOT _projection) (vi (proj_code x)) q *
  field_at Ews t_law (DOT _running) (vi (w_running s)) q *
  field_at Ews t_law (DOT _copy_expect) ce q *
  field_at Ews t_law (DOT _info_expect) ie q *
  field_at Ews t_law (DOT _usable_expect) (map vl (m_usable m)) q *
  field_at Ews t_law (DOT _blocked_expect) (map vl (m_blocked m)) q *
  field_at Ews t_law (DOT _reserved_expect) (map vl (m_reserved m)) q *
  field_at Ews t_law (DOT _states_expect) (states_val (m_states m)) q *
  field_at Ews t_law (DOT _at) (vi (m_at m)) q *
  field_at Ews t_law (DOT _extent_ok) (vi (Z.b2z (m_extent_ok m))) q *
  field_at Ews t_law (DOT _records) (vi (w_records s)) q *
  field_at Ews t_law (DOT _expect) (vi (w_expect s)) q *
  field_at Ews t_law (DOT _verdict) (vi (w_verdict s)) q *
  field_at Ews t_law (DOT _chunk) (vl (w_chunk s)) q *
  field_at Ews t_law (DOT _word) (vl (w_word s)) q *
  field_at Ews t_law (DOT _block) (vl (w_block s)) q *
  field_at Ews t_law (DOT _value) (vl (w_value s)) q *
  field_at Ews t_law (DOT _stream) (map vl (w_stream s)) q *
  field_at Ews t_law (DOT _answer) (map vl (w_answer s)) q)%logic.

(* The law's arrays: the copy (copy_expect) for an allocation or a copy alone, the words a decoder alone reads
   (info_expect) for a projection or a candidate alone (in an allocation info_expect is copy_expect).  main keeps
   the other one of its two expectation arrays itself (the callees do not touch it). *)
Definition info_obj (x: inputs) (ie: val) : mpred :=
  if has_copy x then emp else data_at Ews (tarray tulong (Zlength (i_info x))) (map vl (i_info x)) ie.

Definition arrays (x: inputs) (ce ie: val) (m: mem) : mpred :=
  ((if has_copy x then data_at Ews (tarray tulong COPY_WORDS) (map vl (m_copy m)) ce else emp) *
   info_obj x ie)%logic.

(* The pointers of the law's arrays.  The oracle's type (HandoffSpecs.ORA) has no place for them, and main
   compares through its own copies of the two pointers after the call; so the oracle pins the array it holds to the
   inputs: to the words of x that the model does not read for the call (i_info for an allocation or a copy, which
   decode the copy or nothing; i_copy for a decoder alone, which neither reads nor writes a copy), main choosing x
   with the pointer's encoding there (enc_ptr). *)
Definition enc_ptr (p: val) : list Z :=
  match p with Vptr b o => [Zpos b; Ptrofs.unsigned o] | _ => nil end.
Definition dec_ptr (l: list Z) : val := Vptr (Z.to_pos (Znth 0 l)) (Ptrofs.repr (Znth 1 l)).

Definition ptr_ok (x: inputs) (ce ie: val) : Prop :=
  (i_call x = FAllocate -> ie = ce) /\
  (if has_copy x then ce = dec_ptr (i_info x) else ie = dec_ptr (i_copy x)).

(* ---------------------------------------------------------------------- *)
(* The invariant                                                          *)
(* ---------------------------------------------------------------------- *)

(* Every field in its C type's range, the arrays of their lengths. *)
Definition lst_ok (s: lst) : Prop :=
  u32_ok (w_running s) /\ u32_ok (w_records s) /\ u32_ok (w_expect s) /\ u32_ok (w_verdict s) /\
  u64_ok (w_chunk s) /\ u64_ok (w_word s) /\ u64_ok (w_block s) /\ u64_ok (w_value s) /\
  Zlength (w_stream s) = 7 /\ Forall u64_ok (w_stream s) /\
  Zlength (w_answer s) = WORDS /\ Forall u64_ok (w_answer s).

Definition state_ok (r: list Z) : Prop := Zlength r = WORDS /\ Forall u64_ok r.

(* The model's memory: its words in range, its arrays of their lengths. *)
Definition mem_fit (x: inputs) (m: mem) : Prop :=
  u32_ok (m_total m) /\
  (has_copy x = true -> Zlength (m_copy m) = COPY_WORDS) /\ (has_copy x = true -> Forall u64_ok (m_copy m)) /\
  Zlength (m_usable m) = BLOCKS /\ Forall u64_ok (m_usable m) /\
  Zlength (m_blocked m) = BLOCKS /\ Forall u64_ok (m_blocked m) /\
  Zlength (m_reserved m) = BLOCKS /\ Forall u64_ok (m_reserved m) /\
  Zlength (m_states m) = 2 /\ state_ok (Znth 0 (m_states m)) /\ state_ok (Znth 1 (m_states m)) /\
  (m_at m = 0 \/ m_at m = 1).

(* What main guarantees of its inputs besides inputs_ok: for a decoder alone, the words it reads, total / 8 of them,
   of an extent that fits. *)
Definition x_fit (x: inputs) : Prop :=
  has_copy x = false -> Forall u64_ok (i_info x) /\ extent_fits (i_total x) /\ Zlength (i_info x) = i_total x / 8.

(* The copy's turn: an allocation or a copy, with an extent that fits. *)
Definition copy_ctx (x: inputs) (m: mem) : Prop :=
  (i_call x = FAllocate \/ i_call x = FCopy) /\ extent_fits (m_total m).

(* The decoder's turn: an allocation or a decoder alone, with an extent that fits and the words it decodes. *)
Definition dec_ctx (x: inputs) (m: mem) : Prop :=
  i_call x <> FCopy /\ extent_fits (m_total m) /\ m_total m / 8 <= Zlength (decoded x m).

(* The answers a so far: word is their number, and they are the first words of answer. *)
Definition prefix (s: lst) (a: list Z) : Prop :=
  w_word s = Zlength a /\ sublist 0 (Zlength a) (w_answer s) = a.

Definition go_inv (x: inputs) (g: stage) (m: mem) (s: lst) : Prop :=
  match g with
  | ExpectSize => w_expect s = E_SIZE /\ i_call x = FAllocate /\ i_address x < LIMIT
  | ExpectStreamInit a => w_expect s = E_STREAM_INIT /\ prefix s a /\ Zlength a < 7 /\ copy_ctx x m
  | ExpectChunk k st =>
      w_expect s = E_CHUNK /\ w_chunk s = k /\ w_stream s = st /\ 0 <= k /\ 8 * k < m_total m /\ copy_ctx x m
  | ExpectStreamStep k st c a =>
      w_expect s = E_STREAM_STEP /\ w_chunk s = k /\ w_stream s = st /\ w_value s = c /\ prefix s a /\
      Zlength a < 9 /\ 0 <= k /\ 8 * k < m_total m /\ copy_ctx x m
  | ExpectDecodeInit a => w_expect s = E_DECODE_INIT /\ prefix s a /\ Zlength a < WORDS /\ dec_ctx x m
  | ExpectDecodeStep k a =>
      w_expect s = E_DECODE_STEP /\ w_chunk s = k /\ w_value s = Znth k (decoded x m) /\ prefix s a /\
      Zlength a < WORDS /\ 0 <= k /\ 8 * k < m_total m /\ dec_ctx x m
  | ExpectRecord k =>
      w_expect s = E_RECORD /\ w_chunk s = k /\ 0 <= k /\ 8 * k < m_total m /\ dec_ctx x m /\
      1 <= Znth 11 (current m) <= ENTRIES
  | ExpectEntry k b a =>
      w_expect s = E_ENTRY /\ w_chunk s = k /\ w_block s = b /\ 0 <= b < BLOCKS /\ prefix s a /\ Zlength a < 4 /\
      0 <= k /\ 8 * k < m_total m /\ dec_ctx x m
  end.

Definition ret_inv (st: Z) (s: lst) : Prop := w_expect s = E_NOTHING /\ w_verdict s = st.

Definition mem_of (p: progress) : mem := match p with Go _ m => m | Return _ m => m end.

Definition J (x: inputs) (p: progress) (s: lst) : Prop :=
  lst_ok s /\ mem_fit x (mem_of p) /\
  match p with Go g m => go_inv x g m s | Return st _ => ret_inv st s end.

(* The law's oracle: the global `law`, the read's and the record's context, with its arrays. *)
Definition Ora_law : ORA := fun gv ctx rctx x h =>
  EX p: progress, EX s: lst, EX ce: val, EX ie: val,
    !! (ctx = gv _law /\ rctx = gv _law /\ inputs_ok x /\ x_fit x /\ run x (start x) h = Some p /\ J x p s /\
        ptr_ok x ce ie) &&
    (lfields (gv _law) x ce ie (mem_of p) s * arrays x ce ie (mem_of p))%logic.

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

Definition begin_stream_spec :=
  DECLARE _begin_stream
  WITH q: val, w0: val, e0: val
  PRE [ tptr t_law ]
    PROP () PARAMS (q)
    SEP (field_at Ews t_law (DOT _word) w0 q; field_at Ews t_law (DOT _expect) e0 q)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (field_at Ews t_law (DOT _word) (vl 0) q; field_at Ews t_law (DOT _expect) (vi E_STREAM_INIT) q).

(* begin_decode(m), at the decoder's turn with memory m: the model's begin_decode. *)
Definition begin_decode_spec :=
  DECLARE _begin_decode
  WITH q: val, x: inputs, ce: val, ie: val, m: mem, s: lst
  PRE [ tptr t_law ]
    PROP (inputs_ok x; lst_ok s; mem_fit x m; dec_ctx x m)
    PARAMS (q)
    SEP (lfields q x ce ie m s)
  POST [ tvoid ]
    EX s': lst,
    PROP (J x (begin_decode x m) s')
    RETURN ()
    SEP (lfields q x ce ie (mem_of (begin_decode x m)) s').

(* begin_chunk(m, k), the stream having accepted the chunks before k and carrying the record's stream. *)
Definition begin_chunk_spec :=
  DECLARE _begin_chunk
  WITH q: val, x: inputs, ce: val, ie: val, m: mem, s: lst, k: Z
  PRE [ tptr t_law, tulong ]
    PROP (inputs_ok x; lst_ok s; mem_fit x m; copy_ctx x m; 0 <= k <= COPY_WORDS)
    PARAMS (q; vl k)
    SEP (lfields q x ce ie m s)
  POST [ tvoid ]
    EX s': lst,
    PROP (J x (begin_chunk x k (w_stream s) m) s')
    RETURN ()
    SEP (lfields q x ce ie (mem_of (begin_chunk x k (w_stream s) m)) s').

(* decode_done(m), with memory m. *)
Definition decode_done_spec :=
  DECLARE _decode_done
  WITH q: val, x: inputs, ce: val, ie: val, m: mem, s: lst
  PRE [ tptr t_law ]
    PROP (inputs_ok x; lst_ok s; mem_fit x m; dec_ctx x m)
    PARAMS (q)
    SEP (lfields q x ce ie m s)
  POST [ tvoid ]
    EX s': lst,
    PROP (J x (decode_done x m) s')
    RETURN ()
    SEP (lfields q x ce ie m s').

(* begin_transition(m, k), the decoder having accepted the transitions before chunk k; the words decoded at ie. *)
Definition begin_transition_spec :=
  DECLARE _begin_transition
  WITH q: val, x: inputs, ce: val, ie: val, m: mem, s: lst, k: Z, sh: share
  PRE [ tptr t_law, tulong ]
    PROP (inputs_ok x; lst_ok s; mem_fit x m; dec_ctx x m; x_fit x; 0 <= k <= COPY_WORDS; readable_share sh)
    PARAMS (q; vl k)
    SEP (lfields q x ce ie m s; data_at sh (tarray tulong (Zlength (decoded x m))) (map vl (decoded x m)) ie)
  POST [ tvoid ]
    EX s': lst,
    PROP (J x (begin_transition x k m) s')
    RETURN ()
    SEP (lfields q x ce ie m s'; data_at sh (tarray tulong (Zlength (decoded x m))) (map vl (decoded x m)) ie).

(* The global variable of the harness, for the functions that use it. *)
Definition Vlaw : varspecs := [(_law, t_law)].
