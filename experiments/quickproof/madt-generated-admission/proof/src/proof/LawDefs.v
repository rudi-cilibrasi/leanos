(* Law admission_exact: the law's oracle (the harness's global `law` and its own copy of the copy's bytes), as the
   oracle predicate Ora_law of the protocol of MgaSpecs, and the specifications of the harness's helpers.

   The law's state is the record lst (the fields of struct law that change while the function runs); the fields
   that are main's inputs (call, length, executing) are functions of the inputs x, and `copy` points at the law's
   own copy, which holds i_bytes x.  The record is a function of the run of the model (J): while the function calls
   (Go g) the fields are the stage g's (go_inv: `expect` the stage's EXPECT_*, `at` its byte or offset, `state` its
   old state, `answer` its answers so far, `word` their number, `args` its arguments), and once it returned
   (Return (st, w)) they are what main's checks need (ret_inv: `expect` EXPECT_NOTHING, `verdict` st, and `id` the
   APIC ID w when there is one). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosMadtAdmission.harness.admission_exact.code.
Require Import LeanosMadtAdmission.proof.Defs.
Require Import LeanosMadtAdmission.proof.MgaSpecs.
Require Import LeanosMadtAdmission.proof.LawProg.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[export] Existing Instance LawProg.LCS.

Definition t_law := Tstruct _law__1 noattr.

(* EXPECT_* and CALL_* of harness/admission_exact.h *)
Definition E_ENVELOPE : Z := 0.
Definition E_ENTRIES : Z := 1.
Definition E_RESULT : Z := 2.
Definition E_NOTHING : Z := 3.

Definition call_code (f: func) : Z :=
  match f with FEnvelope => 0 | FEntries => 1 | FResult => 2 | FAdmission => 3 end.

(* The mutable fields of struct law (all but call, length, executing and copy), in its order. *)
Record lst : Type := mk_lst {
  ls_args: list Z; ls_expect: Z; ls_verdict: Z; ls_at: Z; ls_word: Z; ls_state: list Z; ls_answer: list Z;
  ls_id: Z }.

Ltac lst_cbn := cbn [ls_args ls_expect ls_verdict ls_at ls_word ls_state ls_answer ls_id] in *.

(* struct law, field by field: the inputs x, the law's copy at p, the record s. *)
Definition lfields (q p: val) (x: inputs) (s: lst) : mpred :=
 (field_at Ews t_law (DOT _call) (vi (call_code (i_call x))) q *
  field_at Ews t_law (DOT _length) (vi (i_length x)) q *
  field_at Ews t_law (DOT _executing) (vi (i_executing x)) q *
  field_at Ews t_law (DOT _copy) p q *
  field_at Ews t_law (DOT _args) (map vl (ls_args s)) q *
  field_at Ews t_law (DOT _expect) (vi (ls_expect s)) q *
  field_at Ews t_law (DOT _verdict) (vi (ls_verdict s)) q *
  field_at Ews t_law (DOT _at) (vl (ls_at s)) q *
  field_at Ews t_law (DOT _word) (vl (ls_word s)) q *
  field_at Ews t_law (DOT _state) (map vl (ls_state s)) q *
  field_at Ews t_law (DOT _answer) (map vl (ls_answer s)) q *
  field_at Ews t_law (DOT _id) (vl (ls_id s)) q)%logic.

(* Every field in its C type's range, the arrays of their lengths. *)
Definition lst_ok (s: lst) : Prop :=
  Zlength (ls_args s) = 10 /\ Forall u64_ok (ls_args s) /\ u32_ok (ls_expect s) /\ u32_ok (ls_verdict s) /\
  u64_ok (ls_at s) /\ u64_ok (ls_word s) /\ Zlength (ls_state s) = 12 /\ Forall u64_ok (ls_state s) /\
  Zlength (ls_answer s) = 16 /\ Forall u64_ok (ls_answer s) /\ u64_ok (ls_id s).

(* ---------------------------------------------------------------------- *)
(* The invariant                                                          *)
(* ---------------------------------------------------------------------- *)

(* While the function calls, in stage g. *)
Definition go_inv (x: inputs) (g: stage) (s: lst) : Prop :=
  match g with
  | ExpectEnvelope i st cur =>
      ls_expect s = E_ENVELOPE /\ i = ls_at s /\ st = sublist 0 3 (ls_state s) /\
      cur = sublist 0 (ls_word s) (ls_answer s) /\ 0 <= ls_word s < 7 /\ 0 <= ls_at s < i_length x /\
      ls_args s = i_args x
  | ExpectEntries k st cur =>
      ls_expect s = E_ENTRIES /\ k = ls_at s /\ st = ls_state s /\
      cur = sublist 0 (ls_word s) (ls_answer s) /\ 0 <= ls_word s < 16 /\ 0 <= ls_at s < i_length x /\
      ls_args s = i_args x
  | ExpectResult args cur =>
      ls_expect s = E_RESULT /\ args = ls_args s /\
      cur = sublist 0 (ls_word s) (ls_answer s) /\ 0 <= ls_word s < 4
  end.

(* Once the function returned o. *)
Definition ret_inv (o: outcome) (s: lst) : Prop :=
  ls_expect s = E_NOTHING /\ ls_verdict s = fst o /\
  match snd o with Some id => ls_id s = id | None => True end.

Definition Jp (x: inputs) (p: progress) (s: lst) : Prop :=
  match p with Go g => go_inv x g s | Return o => ret_inv o s end.

(* The record after the answers h. *)
Definition J (x: inputs) (h: list answer) (s: lst) : Prop :=
  match run x (start x) h with Some p => Jp x p s | None => False end.

(* The law's oracle: the global `law`, whose copy points at the law's own copy of the bytes. *)
Definition Ora_law : ORA := fun gv x h =>
  EX p: val, EX s: lst,
    !! (inputs_ok x /\ lst_ok s /\ J x h s) &&
    (lfields (gv _law) p x s * data_at Ews (tarray tuchar (i_length x)) (bytes_val (i_bytes x)) p)%logic.

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

(* begin_entries(m), envelope_done(m), entries_done(m): from the fields s to the progress the model's
   begin_entries, envelope_done and entries_done lead to (the first two keep the result's arguments). *)
Definition begin_entries_spec :=
  DECLARE _begin_entries
  WITH q: val, p: val, x: inputs, s: lst
  PRE [ tptr t_law ]
    PROP (inputs_ok x; lst_ok s; ls_args s = i_args x)
    PARAMS (q)
    SEP (lfields q p x s)
  POST [ tvoid ]
    EX s': lst,
    PROP (lst_ok s'; Jp x (begin_entries x) s'; ls_args s' = ls_args s)
    RETURN ()
    SEP (lfields q p x s').

Definition envelope_done_spec :=
  DECLARE _envelope_done
  WITH q: val, p: val, x: inputs, s: lst
  PRE [ tptr t_law ]
    PROP (inputs_ok x; lst_ok s; ls_args s = i_args x)
    PARAMS (q)
    SEP (lfields q p x s)
  POST [ tvoid ]
    EX s': lst,
    PROP (lst_ok s'; Jp x (envelope_done x (sublist 0 3 (ls_state s))) s'; ls_args s' = ls_args s)
    RETURN ()
    SEP (lfields q p x s').

Definition entries_done_spec :=
  DECLARE _entries_done
  WITH q: val, p: val, x: inputs, s: lst
  PRE [ tptr t_law ]
    PROP (inputs_ok x; lst_ok s; ls_args s = i_args x)
    PARAMS (q)
    SEP (lfields q p x s)
  POST [ tvoid ]
    EX s': lst,
    PROP (lst_ok s'; Jp x (entries_done x (ls_state s)) s')
    RETURN ()
    SEP (lfields q p x s').

(* The global variable of the harness, for the functions that use it. *)
Definition Vlaw : varspecs := [(_law, t_law)].
