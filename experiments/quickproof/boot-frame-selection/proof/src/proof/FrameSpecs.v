(* Specifications of the seven functions main calls (patch/frame_unit.c: frame_terminal, frame_select,
   frame_cross_check, frame_scrub_selected, frame_publication_result, frame_publication_check, frame_rescan) and of
   the eight callees of the header: the candidate decoder and the scrub, which it is given as function pointers,
   and the six Lean exports.  Under the unit's compspecs.

   The callees are specified by a protocol over an abstract oracle: `Ora gv dctx sctx sp x h` is the decoder, the
   scrub and the Lean behind a step's inputs x after they have answered the calls h, for the decoder's context
   dctx, the scrub's context sctx and the two decoder states at sp (states[0] at sp, states[1] at row_ptr sp 1:
   the rows the decoder may be given), in the global environment gv (the exports take no context, so an
   implementation may keep its state in globals, as the law's does in `law`, which it passes as both contexts).
   Each callee is asked only for the step's next call (Defs.next_call) and records its answer.  The protocol and
   the specifications are parameterized by Ora (a definition parameter: VST's WITH cannot range over mpred), and
   the law instantiates it with its own oracle.

   Each wrapper is one step of Defs, from the oracle before any call (the answers nil) to a complete run h of the
   step: `returns x h = Some (st, m)` (the law's EXPECT_NOTHING, with verdict st), it returns st, the objects it
   is given that no step writes hold the inputs' contents, and the others the outcome's memory m.  What the step
   is not given, main still holds as it was: Defs.returns_ok says that m keeps it (keeps), and that st is a status
   and m a memory of the model, for answers of their calls' kinds and ranges (answers_ok: the callees'
   postconditions give each answer's range, so an oracle can keep answers_ok h).  main composes the steps of
   boot_allocate's sequence by starting each step's inputs from the memory the previous step returned
   (Defs.allocate_next, whose inputs are again main's: Defs.inputs_ok_next).

   This file is the interface the law depends on.  The specifications of the header's seven functions, which the
   wrappers forward to, and Gprog are in InternalSpecs.v, which the body proofs may revise without touching this
   file. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require LeanosFrameSelection.units.Frame.
Require Import LeanosFrameSelection.frame.code.
Require Import LeanosFrameSelection.proof.Defs.

#[export] Instance CS : compspecs := LeanosFrameSelection.units.Frame.CS.
Definition Vprog : varspecs. mk_varspecs LeanosFrameSelection.frame.code.prog. Defined.

Definition vl (v: Z) : val := Vlong (Int64.repr v).
Definition vi (v: Z) : val := Vint (Int.repr v).

(* The objects: the manifest (18 words), a decoder state and the decoded state (41), a bitmap (64), the terminal
   result (9), the publication result and the rescan's record (5 each), the two states (uint64_t[2][41]). *)
Definition t_manifest := tarray tulong MANIFEST_WORDS.
Definition t_state := tarray tulong WORDS.
Definition t_bitmap := tarray tulong BLOCKS.
Definition t_terminal := tarray tulong TERMINAL_WORDS.
Definition t_publication := tarray tulong PUBLICATION_WORDS.
Definition t_rescan := tarray tulong RESCAN_WORDS.
Definition t_states := tarray t_state 2.
(* boot_frame_decode and boot_frame_scrub. *)
Definition t_decode : type := Tfunction (tptr tvoid :: tulong :: tptr tulong :: nil) tuint cc_default.
Definition t_scrub : type := Tfunction (tptr tvoid :: tulong :: nil) tuint cc_default.

(* The two states as they lie in memory, and states[k], STATE_BYTES (sizeof(uint64_t[41])) after states[k - 1]. *)
Definition states_val (ss: list (list Z)) : list (list val) := map (map vl) ss.
Definition STATE_BYTES : Z := 328.
Lemma sizeof_t_state : sizeof t_state = STATE_BYTES.
Proof. reflexivity. Qed.
Definition row_ptr (sp: val) (k: Z) : val := offset_val (STATE_BYTES * k) sp.

(* The two states are state 0 at sp and state 1 at row_ptr sp 1. *)
Lemma states_split (sh: share) (ss: list (list Z)) (sp: val) :
  Zlength ss = 2 -> field_compatible t_states nil sp ->
  data_at sh t_states (states_val ss) sp =
  (data_at sh t_state (map vl (Znth 0 ss)) sp * data_at sh t_state (map vl (Znth 1 ss)) (row_ptr sp 1))%logic.
Proof.
  intros L FC.
  destruct ss as [| s0 [| s1 [| ? ?]]]; try (rewrite !Zlength_cons, ?Zlength_nil in L; rep_lia);
    try (rewrite Zlength_nil in L; lia).
  unfold states_val. cbn [map].
  change [map vl s0; map vl s1] with ([map vl s0] ++ [map vl s1]).
  unfold t_states.
  rewrite (split2_data_at_Tarray_app 1 2 sh t_state [map vl s0] [map vl s1] sp) by reflexivity.
  rewrite !(data_at_singleton_array_eq sh t_state _ _ _ eq_refl).
  rewrite field_address0_offset by (apply arr_field_compatible0; auto; lia).
  reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* The oracle and the protocols of the eight callees.                     *)
(* ---------------------------------------------------------------------- *)

Definition ORA : Type := globals -> val -> val -> val -> inputs -> list answer -> mpred.

(* The candidate decoder, behind the function pointer `decode`: asked for the step's next decode after the
   answers h, of candidate c into state k (the row row_ptr sp k it is given, writable), it writes any 41 64-bit
   words ws there, answers any 32-bit status st and records both.  It is given what a decoder that checks its
   call needs (the law's compares state with law.states[law.scan] and context with &law): the row's memory, so
   the row pointer is valid, and that sp is a pointer, so an oracle may hold it in a record (law.states = sp) and
   load it; the context's memory, if any, is the oracle's (the law's holds struct law, both contexts). *)
Definition decode_spec (Ora: ORA) : funspec :=
  WITH gv: globals, dctx: val, sctx: val, sp: val, x: inputs, h: list answer, c: Z, k: Z, sh: share
  PRE [ tptr tvoid, tulong, tptr tulong ]
    PROP (next_call x h = Some (Decode c k); writable_share sh; isptr sp)
    PARAMS (dctx; vl c; row_ptr sp k)
    GLOBALS (gv)
    SEP (Ora gv dctx sctx sp x h; data_at_ sh t_state (row_ptr sp k))
  POST [ tuint ]
    EX st: Z, EX ws: list Z,
    PROP (u32_ok st; Zlength ws = WORDS; Forall u64_ok ws)
    RETURN (vi st)
    SEP (Ora gv dctx sctx sp x (h ++ [(Decode c k, Decoded st ws)]);
         data_at sh t_state (map vl ws) (row_ptr sp k)).

(* The scrub, behind the function pointer `scrub`: asked for the step's next scrub after the answers h, of
   frame f, it answers any 32-bit value and records it.  The context's memory, if any, is the oracle's. *)
Definition scrub_spec (Ora: ORA) : funspec :=
  WITH gv: globals, dctx: val, sctx: val, sp: val, x: inputs, h: list answer, f: Z
  PRE [ tptr tvoid, tulong ]
    PROP (next_call x h = Some (Scrub f))
    PARAMS (sctx; vl f)
    GLOBALS (gv)
    SEP (Ora gv dctx sctx sp x h)
  POST [ tuint ]
    EX v: Z,
    PROP (u32_ok v)
    RETURN (vi v)
    SEP (Ora gv dctx sctx sp x (h ++ [(Scrub f, Word v)])).

(* The six exports: each, asked for the step's next call after the answers h, answers any 64-bit value and
   records the answer. *)

(* leanos_boot_projection_manifest(block, m0, ..., m17, query): the manifest's words ms. *)
Definition manifest_spec (Ora: ORA) :=
  DECLARE _leanos_boot_projection_manifest
  WITH gv: globals, dctx: val, sctx: val, sp: val, x: inputs, h: list answer, b: Z, ms: list Z, q: Z
  PRE [
        tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong,
        tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong ]
    PROP (next_call x h = Some (Manifest b ms q))
    PARAMS (vl b;
            vl (Znth 0 ms); vl (Znth 1 ms); vl (Znth 2 ms); vl (Znth 3 ms); vl (Znth 4 ms); vl (Znth 5 ms);
            vl (Znth 6 ms); vl (Znth 7 ms); vl (Znth 8 ms); vl (Znth 9 ms); vl (Znth 10 ms); vl (Znth 11 ms);
            vl (Znth 12 ms); vl (Znth 13 ms); vl (Znth 14 ms); vl (Znth 15 ms); vl (Znth 16 ms); vl (Znth 17 ms);
            vl q)
    GLOBALS (gv)
    SEP (Ora gv dctx sctx sp x h)
  POST [ tulong ]
    EX v: Z,
    PROP (u64_ok v)
    RETURN (vl v)
    SEP (Ora gv dctx sctx sp x (h ++ [(Manifest b ms q, Word v)])).

(* leanos_boot_projection_free(usable, blocked, reserved). *)
Definition free_spec (Ora: ORA) :=
  DECLARE _leanos_boot_projection_free
  WITH gv: globals, dctx: val, sctx: val, sp: val, x: inputs, h: list answer, u: Z, bl: Z, r: Z
  PRE [ tulong, tulong, tulong ]
    PROP (next_call x h = Some (Free u bl r))
    PARAMS (vl u; vl bl; vl r)
    GLOBALS (gv)
    SEP (Ora gv dctx sctx sp x h)
  POST [ tulong ]
    EX v: Z,
    PROP (u64_ok v)
    RETURN (vl v)
    SEP (Ora gv dctx sctx sp x (h ++ [(Free u bl r, Word v)])).

(* leanos_boot_projection_finish(decode_status, decode_error, manifest_status, manifest_error, entry_count,
   highest, owner, query, w0, ..., w63): the 64 free words as one list fw. *)
Definition finish_spec (Ora: ORA) :=
  DECLARE _leanos_boot_projection_finish
  WITH gv: globals, dctx: val, sctx: val, sp: val, x: inputs, h: list answer,
       ds: Z, de: Z, ms: Z, me: Z, cnt: Z, hi: Z, own: Z, q: Z, fw: list Z
  PRE [
        tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong,
        tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong,
        tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong,
        tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong,
        tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong,
        tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong,
        tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong,
        tulong, tulong ]
    PROP (next_call x h = Some (Finish ds de ms me cnt hi own q fw))
    PARAMS (vl ds; vl de; vl ms; vl me; vl cnt; vl hi; vl own; vl q;
            vl (Znth 0 fw); vl (Znth 1 fw); vl (Znth 2 fw); vl (Znth 3 fw); vl (Znth 4 fw); vl (Znth 5 fw);
            vl (Znth 6 fw); vl (Znth 7 fw); vl (Znth 8 fw); vl (Znth 9 fw); vl (Znth 10 fw); vl (Znth 11 fw);
            vl (Znth 12 fw); vl (Znth 13 fw); vl (Znth 14 fw); vl (Znth 15 fw); vl (Znth 16 fw); vl (Znth 17 fw);
            vl (Znth 18 fw); vl (Znth 19 fw); vl (Znth 20 fw); vl (Znth 21 fw); vl (Znth 22 fw); vl (Znth 23 fw);
            vl (Znth 24 fw); vl (Znth 25 fw); vl (Znth 26 fw); vl (Znth 27 fw); vl (Znth 28 fw); vl (Znth 29 fw);
            vl (Znth 30 fw); vl (Znth 31 fw); vl (Znth 32 fw); vl (Znth 33 fw); vl (Znth 34 fw); vl (Znth 35 fw);
            vl (Znth 36 fw); vl (Znth 37 fw); vl (Znth 38 fw); vl (Znth 39 fw); vl (Znth 40 fw); vl (Znth 41 fw);
            vl (Znth 42 fw); vl (Znth 43 fw); vl (Znth 44 fw); vl (Znth 45 fw); vl (Znth 46 fw); vl (Znth 47 fw);
            vl (Znth 48 fw); vl (Znth 49 fw); vl (Znth 50 fw); vl (Znth 51 fw); vl (Znth 52 fw); vl (Znth 53 fw);
            vl (Znth 54 fw); vl (Znth 55 fw); vl (Znth 56 fw); vl (Znth 57 fw); vl (Znth 58 fw); vl (Znth 59 fw);
            vl (Znth 60 fw); vl (Znth 61 fw); vl (Znth 62 fw); vl (Znth 63 fw))
    GLOBALS (gv)
    SEP (Ora gv dctx sctx sp x h)
  POST [ tulong ]
    EX v: Z,
    PROP (u64_ok v)
    RETURN (vl v)
    SEP (Ora gv dctx sctx sp x (h ++ [(Finish ds de ms me cnt hi own q fw, Word v)])).

(* leanos_boot_manifest_candidate(frame, m0, ..., m17). *)
Definition candidate_spec (Ora: ORA) :=
  DECLARE _leanos_boot_manifest_candidate
  WITH gv: globals, dctx: val, sctx: val, sp: val, x: inputs, h: list answer, f: Z, ms: list Z
  PRE [
        tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong,
        tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong ]
    PROP (next_call x h = Some (Candidate f ms))
    PARAMS (vl f;
            vl (Znth 0 ms); vl (Znth 1 ms); vl (Znth 2 ms); vl (Znth 3 ms); vl (Znth 4 ms); vl (Znth 5 ms);
            vl (Znth 6 ms); vl (Znth 7 ms); vl (Znth 8 ms); vl (Znth 9 ms); vl (Znth 10 ms); vl (Znth 11 ms);
            vl (Znth 12 ms); vl (Znth 13 ms); vl (Znth 14 ms); vl (Znth 15 ms); vl (Znth 16 ms); vl (Znth 17 ms))
    GLOBALS (gv)
    SEP (Ora gv dctx sctx sp x h)
  POST [ tulong ]
    EX v: Z,
    PROP (u64_ok v)
    RETURN (vl v)
    SEP (Ora gv dctx sctx sp x (h ++ [(Candidate f ms, Word v)])).

(* leanos_boot_consume_exact_projection(current, candidate, decode_status, usable, blocked, manifest). *)
Definition consume_spec (Ora: ORA) :=
  DECLARE _leanos_boot_consume_exact_projection
  WITH gv: globals, dctx: val, sctx: val, sp: val, x: inputs, h: list answer,
       cur: Z, c: Z, ds: Z, u: Z, bl: Z, cm: Z
  PRE [ tulong, tulong, tulong, tulong, tulong, tulong ]
    PROP (next_call x h = Some (Consume cur c ds u bl cm))
    PARAMS (vl cur; vl c; vl ds; vl u; vl bl; vl cm)
    GLOBALS (gv)
    SEP (Ora gv dctx sctx sp x h)
  POST [ tulong ]
    EX v: Z,
    PROP (u64_ok v)
    RETURN (vl v)
    SEP (Ora gv dctx sctx sp x (h ++ [(Consume cur c ds u bl cm, Word v)])).

(* leanos_boot_authority_result(selected, rescanned, status, usable, blocked, manifest, scrubbed, query). *)
Definition authority_spec (Ora: ORA) :=
  DECLARE _leanos_boot_authority_result
  WITH gv: globals, dctx: val, sctx: val, sp: val, x: inputs, h: list answer,
       s: Z, t: Z, ds: Z, u: Z, bl: Z, sm: Z, sc: Z, q: Z
  PRE [ tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong ]
    PROP (next_call x h = Some (Authority s t ds u bl sm sc q))
    PARAMS (vl s; vl t; vl ds; vl u; vl bl; vl sm; vl sc; vl q)
    GLOBALS (gv)
    SEP (Ora gv dctx sctx sp x h)
  POST [ tulong ]
    EX v: Z,
    PROP (u64_ok v)
    RETURN (vl v)
    SEP (Ora gv dctx sctx sp x (h ++ [(Authority s t ds u bl sm sc q, Word v)])).

(* ---------------------------------------------------------------------- *)
(* The seven functions main calls.                                       *)
(* ---------------------------------------------------------------------- *)

(* Common to the seven: the step's inputs x (inputs_ok x), with i_step x the step and i_mem x the memory before
   it; the oracle before any call; separate objects, those no step writes readable (share rsh) and holding x's
   (i_manifest x, ...), the others writable (share wsh) unless the step only reads them, and holding i_mem x's.
   Each returns after its callees answered exactly the calls h of a complete run of the step (returns), with the
   run's status st and memory m: the objects no step writes still hold x's contents, and the others m's. *)

(* frame_terminal(manifest, decoded, usable, blocked, reserved, terminal), and boot_frame_terminal
   (InternalSpecs.v), which it forwards to. *)
Definition terminal_pre_post (Ora: ORA) (name: ident) :=
  DECLARE name
  WITH gv: globals, dctx: val, sctx: val, sp: val, x: inputs,
       mp: val, dp: val, up: val, bp: val, rp: val, tp: val, rsh: share, wsh: share
  PRE [ tptr tulong, tptr tulong, tptr tulong, tptr tulong, tptr tulong, tptr tulong ]
    PROP (i_step x = FTerminal; inputs_ok x; readable_share rsh; writable_share wsh)
    PARAMS (mp; dp; up; bp; rp; tp)
    GLOBALS (gv)
    SEP (Ora gv dctx sctx sp x nil;
         data_at rsh t_manifest (map vl (i_manifest x)) mp;
         data_at rsh t_state (map vl (i_decoded x)) dp;
         data_at rsh t_bitmap (map vl (i_usable x)) up;
         data_at rsh t_bitmap (map vl (i_blocked x)) bp;
         data_at wsh t_bitmap (map vl (m_reserved (i_mem x))) rp;
         data_at wsh t_terminal (map vl (m_terminal (i_mem x))) tp)
  POST [ tint ]
    EX h: list answer, EX st: Z, EX m: mem,
    PROP (returns x h = Some (st, m))
    RETURN (vi st)
    SEP (Ora gv dctx sctx sp x h;
         data_at rsh t_manifest (map vl (i_manifest x)) mp;
         data_at rsh t_state (map vl (i_decoded x)) dp;
         data_at rsh t_bitmap (map vl (i_usable x)) up;
         data_at rsh t_bitmap (map vl (i_blocked x)) bp;
         data_at wsh t_bitmap (map vl (m_reserved m)) rp;
         data_at wsh t_terminal (map vl (m_terminal m)) tp).

(* frame_select(decode, context, manifest, take_next, states, selected, selected_manifest, next, decoder_status),
   and boot_frame_select: the decoder (decode_spec) with its context dctx; the two states at sp, the oracle's;
   the selection's three records and the decoder record. *)
Definition select_pre_post (Ora: ORA) (name: ident) :=
  DECLARE name
  WITH gv: globals, decode: val, dctx: val, sctx: val, sp: val, x: inputs,
       mp: val, selp: val, smp: val, np: val, dsp: val, rsh: share, wsh: share
  PRE [ tptr t_decode, tptr tvoid, tptr tulong, tuint, tptr t_state, tptr tulong, tptr tulong, tptr tulong,
        tptr tuint ]
    PROP (i_step x = FSelect; inputs_ok x; readable_share rsh; writable_share wsh)
    PARAMS (decode; dctx; mp; vi (i_take_next x); sp; selp; smp; np; dsp)
    GLOBALS (gv)
    SEP (func_ptr' (decode_spec Ora) decode; Ora gv dctx sctx sp x nil;
         data_at rsh t_manifest (map vl (i_manifest x)) mp;
         data_at wsh t_states (states_val (m_states (i_mem x))) sp;
         data_at wsh tulong (vl (m_selected (i_mem x))) selp;
         data_at wsh tulong (vl (m_selected_manifest (i_mem x))) smp;
         data_at wsh tulong (vl (m_next (i_mem x))) np;
         data_at wsh tuint (vi (m_decoder (i_mem x))) dsp)
  POST [ tint ]
    EX h: list answer, EX st: Z, EX m: mem,
    PROP (returns x h = Some (st, m))
    RETURN (vi st)
    SEP (func_ptr' (decode_spec Ora) decode; Ora gv dctx sctx sp x h;
         data_at rsh t_manifest (map vl (i_manifest x)) mp;
         data_at wsh t_states (states_val (m_states m)) sp;
         data_at wsh tulong (vl (m_selected m)) selp;
         data_at wsh tulong (vl (m_selected_manifest m)) smp;
         data_at wsh tulong (vl (m_next m)) np;
         data_at wsh tuint (vi (m_decoder m)) dsp).

(* frame_cross_check(terminal, decoded, selected, state, selected_manifest), and boot_frame_cross_check: the
   frame S = i_selected x and its manifest answer A = i_selected_manifest x; state is state 0 (main passes
   states[0]), read only like the terminal result. *)
Definition cross_check_pre_post (Ora: ORA) (name: ident) :=
  DECLARE name
  WITH gv: globals, dctx: val, sctx: val, sp: val, x: inputs, tp: val, dp: val, p0: val, rsh: share
  PRE [ tptr tulong, tptr tulong, tulong, tptr tulong, tulong ]
    PROP (i_step x = FCrossCheck; inputs_ok x; readable_share rsh)
    PARAMS (tp; dp; vl (i_selected x); p0; vl (i_selected_manifest x))
    GLOBALS (gv)
    SEP (Ora gv dctx sctx sp x nil;
         data_at rsh t_terminal (map vl (m_terminal (i_mem x))) tp;
         data_at rsh t_state (map vl (i_decoded x)) dp;
         data_at rsh t_state (map vl (Znth 0 (m_states (i_mem x)))) p0)
  POST [ tint ]
    EX h: list answer, EX st: Z, EX m: mem,
    PROP (returns x h = Some (st, m))
    RETURN (vi st)
    SEP (Ora gv dctx sctx sp x h;
         data_at rsh t_terminal (map vl (m_terminal m)) tp;
         data_at rsh t_state (map vl (i_decoded x)) dp;
         data_at rsh t_state (map vl (Znth 0 (m_states m))) p0).

(* frame_scrub_selected(scrub, context, selected), and boot_frame_scrub_selected: the scrub (scrub_spec) with
   its context sctx, of the frame S. *)
Definition scrub_selected_pre_post (Ora: ORA) (name: ident) :=
  DECLARE name
  WITH gv: globals, scrub: val, dctx: val, sctx: val, sp: val, x: inputs
  PRE [ tptr t_scrub, tptr tvoid, tulong ]
    PROP (i_step x = FScrub; inputs_ok x)
    PARAMS (scrub; sctx; vl (i_selected x))
    GLOBALS (gv)
    SEP (func_ptr' (scrub_spec Ora) scrub; Ora gv dctx sctx sp x nil)
  POST [ tint ]
    EX h: list answer, EX st: Z, EX m: mem,
    PROP (returns x h = Some (st, m))
    RETURN (vi st)
    SEP (func_ptr' (scrub_spec Ora) scrub; Ora gv dctx sctx sp x h).

(* frame_publication_result(selected, state, selected_manifest, publication), and
   boot_frame_publication_result: state 0 (read only) and the publication result; it returns nothing, and its
   run returns OK. *)
Definition publication_result_pre_post (Ora: ORA) (name: ident) :=
  DECLARE name
  WITH gv: globals, dctx: val, sctx: val, sp: val, x: inputs, p0: val, pp: val, rsh: share, wsh: share
  PRE [ tulong, tptr tulong, tulong, tptr tulong ]
    PROP (i_step x = FPublicationResult; inputs_ok x; readable_share rsh; writable_share wsh)
    PARAMS (vl (i_selected x); p0; vl (i_selected_manifest x); pp)
    GLOBALS (gv)
    SEP (Ora gv dctx sctx sp x nil;
         data_at rsh t_state (map vl (Znth 0 (m_states (i_mem x)))) p0;
         data_at wsh t_publication (map vl (m_publication (i_mem x))) pp)
  POST [ tvoid ]
    EX h: list answer, EX m: mem,
    PROP (returns x h = Some (S_OK, m))
    RETURN ()
    SEP (Ora gv dctx sctx sp x h;
         data_at rsh t_state (map vl (Znth 0 (m_states m))) p0;
         data_at wsh t_publication (map vl (m_publication m)) pp).

(* frame_publication_check(selected, publication), and boot_frame_publication_check: the publication result,
   read only. *)
Definition publication_check_pre_post (Ora: ORA) (name: ident) :=
  DECLARE name
  WITH gv: globals, dctx: val, sctx: val, sp: val, x: inputs, pp: val, rsh: share
  PRE [ tulong, tptr tulong ]
    PROP (i_step x = FPublicationCheck; inputs_ok x; readable_share rsh)
    PARAMS (vl (i_selected x); pp)
    GLOBALS (gv)
    SEP (Ora gv dctx sctx sp x nil;
         data_at rsh t_publication (map vl (m_publication (i_mem x))) pp)
  POST [ tint ]
    EX h: list answer, EX st: Z, EX m: mem,
    PROP (returns x h = Some (st, m))
    RETURN (vi st)
    SEP (Ora gv dctx sctx sp x h;
         data_at rsh t_publication (map vl (m_publication m)) pp).

(* frame_rescan(decode, context, manifest, decoded, published, next, state, rescan, decoder_status), and
   boot_frame_rescan: the published frame P = i_published x and the next N = i_next x; state is state 1 of the
   oracle's states at the pointer sp (main passes states[1]), which the decoder writes; the rescan's record and
   the decoder record. *)
Definition rescan_pre_post (Ora: ORA) (name: ident) :=
  DECLARE name
  WITH gv: globals, decode: val, dctx: val, sctx: val, sp: val, x: inputs,
       mp: val, dp: val, rp: val, dsp: val, rsh: share, wsh: share
  PRE [ tptr t_decode, tptr tvoid, tptr tulong, tptr tulong, tulong, tulong, tptr tulong, tptr tulong,
        tptr tuint ]
    PROP (i_step x = FRescan; inputs_ok x; readable_share rsh; writable_share wsh; isptr sp)
    PARAMS (decode; dctx; mp; dp; vl (i_published x); vl (i_next x); row_ptr sp 1; rp; dsp)
    GLOBALS (gv)
    SEP (func_ptr' (decode_spec Ora) decode; Ora gv dctx sctx sp x nil;
         data_at rsh t_manifest (map vl (i_manifest x)) mp;
         data_at rsh t_state (map vl (i_decoded x)) dp;
         data_at wsh t_state (map vl (Znth 1 (m_states (i_mem x)))) (row_ptr sp 1);
         data_at wsh t_rescan (map vl (m_rescan (i_mem x))) rp;
         data_at wsh tuint (vi (m_decoder (i_mem x))) dsp)
  POST [ tint ]
    EX h: list answer, EX st: Z, EX m: mem,
    PROP (returns x h = Some (st, m))
    RETURN (vi st)
    SEP (func_ptr' (decode_spec Ora) decode; Ora gv dctx sctx sp x h;
         data_at rsh t_manifest (map vl (i_manifest x)) mp;
         data_at rsh t_state (map vl (i_decoded x)) dp;
         data_at wsh t_state (map vl (Znth 1 (m_states m))) (row_ptr sp 1);
         data_at wsh t_rescan (map vl (m_rescan m)) rp;
         data_at wsh tuint (vi (m_decoder m)) dsp).

Definition frame_terminal_spec Ora := terminal_pre_post Ora _frame_terminal.
Definition frame_select_spec Ora := select_pre_post Ora _frame_select.
Definition frame_cross_check_spec Ora := cross_check_pre_post Ora _frame_cross_check.
Definition frame_scrub_selected_spec Ora := scrub_selected_pre_post Ora _frame_scrub_selected.
Definition frame_publication_result_spec Ora := publication_result_pre_post Ora _frame_publication_result.
Definition frame_publication_check_spec Ora := publication_check_pre_post Ora _frame_publication_check.
Definition frame_rescan_spec Ora := rescan_pre_post Ora _frame_rescan.
