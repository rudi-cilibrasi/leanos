(* Specifications of the seven functions of include/boot_handoff_decode.h (static inline, each kept as a function
   by clightgen), and Gprog, the specifications the body proofs are stated against.  A starting point for the
   body proofs, which may revise them; the interface the law depends on (the oracle, the callees and the five
   wrappers) is HandoffSpecs.v.

   The functions the wrappers alone call have their wrapper's specification: boot_handoff_extent,
   boot_handoff_decode_candidate and boot_handoff_project.  The others are specified as one phase of main's run
   of Defs: from the progress the phase starts at, after the answers h, to the progress its result leads to,
   after the answers h ++ hs, with the model's memory m at the start:
   - boot_handoff_stream_copy: from the stream reset to copy_end x st (with_copy m c), the copy c;
   - boot_decode_reset: from the decoder reset to decode_init_done x a m, its 41 answers a;
   - boot_decode_transition: from chunk k's transition to decode_step_done x k a m, its 41 answers a;
   - boot_handoff_decode_projection: from begin_decode x m (its bitmaps not yet zeroed) to projection_end x st
     m', m' being m with the bitmaps and the states it leaves.
   The model's memory changes only through Defs' with_* functions, so what a phase leaves alone is plain. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import LeanosHandoff.handoff.code.
Require Import LeanosHandoff.proof.Defs.
Require Import LeanosHandoff.proof.HandoffSpecs.
#[local] Existing Instance HandoffSpecs.CS.

(* The model's memory of a run: three bitmaps of 64 words, two states of 41, the current one 0 or 1. *)
Definition mem_ok (m: mem) : Prop :=
  Zlength (m_usable m) = BLOCKS /\ Zlength (m_blocked m) = BLOCKS /\ Zlength (m_reserved m) = BLOCKS /\
  Zlength (m_states m) = 2 /\ Forall (fun s => Zlength s = WORDS) (m_states m) /\ (m_at m = 0 \/ m_at m = 1).

(* boot_handoff_extent: the specification of its wrapper handoff_extent. *)
Definition boot_extent_spec Ora := extent_pre_post Ora _boot_handoff_extent.

(* boot_handoff_stream_copy(read, context, magic, info_address, total, copy, length), where the model is at the
   stream reset with memory m, after the answers h; the copy has 8192 words, the length record (lold) anything.
   It returns st after the answers hs; the copy then holds c, and the length record the extent on OK. *)
Definition stream_copy_spec (Ora: ORA) :=
  DECLARE _boot_handoff_stream_copy
  WITH gv: globals, read: val, ctx: val, rctx: val, x: inputs, h: list answer, m: mem,
       cp: val, csh: share, lp: val, lsh: share, lold: val
  PRE [ tptr t_read, tptr tvoid, tuint, tuint, tuint, tptr tulong, tptr tuint ]
    PROP (inputs_ok x; extent_fits (m_total m); Zlength (m_copy m) = COPY_WORDS;
          run x (start x) h = Some (Go (ExpectStreamInit nil) m); writable_share csh; writable_share lsh)
    PARAMS (read; ctx; vi (i_magic x); vi (i_address x); vi (m_total m); cp; lp)
    GLOBALS (gv)
    SEP (func_ptr' (read_spec Ora) read; Ora gv ctx rctx x h;
         data_at csh (tarray tulong COPY_WORDS) (map vl (m_copy m)) cp; data_at lsh tuint lold lp)
  POST [ tint ]
    EX hs: list answer, EX st: Z, EX c: list Z,
    PROP (run x (start x) (h ++ hs) = Some (copy_end x st (with_copy m c)); status_ok st;
          Zlength c = COPY_WORDS)
    RETURN (vi st)
    SEP (func_ptr' (read_spec Ora) read; Ora gv ctx rctx x (h ++ hs);
         data_at csh (tarray tulong COPY_WORDS) (map vl c) cp;
         data_at lsh tuint (if st =? S_OK then vi (m_total m) else lold) lp).

(* boot_decode_reset(magic, info_address, total, target, state), where the model is at the decoder reset with
   memory m: the row `state` (states[0]) then holds the reset's 41 answers a. *)
Definition decode_reset_spec (Ora: ORA) :=
  DECLARE _boot_decode_reset
  WITH gv: globals, ctx: val, rctx: val, x: inputs, h: list answer, m: mem, p: val, sh: share
  PRE [ tuint, tuint, tuint, tulong, tptr tulong ]
    PROP (inputs_ok x; u32_ok (m_total m); run x (start x) h = Some (Go (ExpectDecodeInit nil) m);
          writable_share sh)
    PARAMS (vi (i_magic x); vi (i_address x); vi (m_total m); vl (target x); p)
    GLOBALS (gv)
    SEP (Ora gv ctx rctx x h; data_at_ sh t_state p)
  POST [ tvoid ]
    EX hs: list answer, EX a: list Z,
    PROP (run x (start x) (h ++ hs) = Some (decode_init_done x a m); Zlength a = WORDS; Forall u64_ok a)
    RETURN ()
    SEP (Ora gv ctx rctx x (h ++ hs); data_at sh t_state (map vl a) p).

(* boot_decode_transition(state, info_address, offset, chunk, terminal, next), where the model is at chunk k's
   transition with memory m: `state` is the current state (states[at]), `chunk` word k of the words decoded,
   `next` the other row (states[1 - at]), which then holds the transition's 41 answers a. *)
Definition decode_transition_spec (Ora: ORA) :=
  DECLARE _boot_decode_transition
  WITH gv: globals, ctx: val, rctx: val, x: inputs, h: list answer, m: mem, k: Z,
       sp: val, ssh: share, np: val, nsh: share
  PRE [ tptr tulong, tuint, tulong, tulong, tulong, tptr tulong ]
    PROP (inputs_ok x; run x (start x) h = Some (Go (ExpectDecodeStep k nil) m); 0 <= k; 8 * k < m_total m;
          u32_ok (m_total m); Zlength (current m) = WORDS; readable_share ssh; writable_share nsh)
    PARAMS (sp; vi (i_address x); vl (8 * k); vl (Znth k (decoded x m)); vl (terminal (m_total m) k); np)
    GLOBALS (gv)
    SEP (Ora gv ctx rctx x h; data_at ssh t_state (map vl (current m)) sp; data_at_ nsh t_state np)
  POST [ tvoid ]
    EX hs: list answer, EX a: list Z,
    PROP (run x (start x) (h ++ hs) = Some (decode_step_done x k a m); Zlength a = WORDS; Forall u64_ok a)
    RETURN ()
    SEP (Ora gv ctx rctx x (h ++ hs); data_at ssh t_state (map vl (current m)) sp;
         data_at nsh t_state (map vl a) np).

(* boot_handoff_decode_projection(magic, info_address, total, info, projection, states, current), where the
   model, after the answers h, begins the decoder with a projection (begin_decode, which zeroes the bitmaps) with
   memory m: `info` holds the words decoded (the copy in an allocation), the projection record (readable) names
   the record callback, its context rctx and the three bitmaps, and the state record holds anything (curold).
   It returns st after the answers hs, leaving the bitmaps u, b, r and the states ss, the current one ss[i] (a
   state of 64-bit words: the reset's or a transition's answers); the state record holds i on OK. *)
Definition decode_projection_spec (Ora: ORA) :=
  DECLARE _boot_handoff_decode_projection
  WITH gv: globals, ctx: val, rctx: val, record: val, x: inputs, h: list answer, m: mem, ip: val, ish: share,
       pp: val, psh: share, up: val, bp: val, rp: val, bsh: share, sp: val, ssh: share,
       curp: val, cursh: share, curold: val
  PRE [ tuint, tuint, tuint, tptr tulong, tptr t_projection, tptr t_state, tptr tuint ]
    PROP (inputs_ok x; projection x = true; extent_fits (m_total m); m_total m / 8 <= Zlength (decoded x m);
          mem_ok m; run x (start x) h = Some (begin_decode x m); is_pointer_or_null rctx;
          readable_share ish; readable_share psh; writable_share bsh; writable_share ssh; writable_share cursh)
    PARAMS (vi (i_magic x); vi (i_address x); vi (m_total m); ip; pp; sp; curp)
    GLOBALS (gv)
    SEP (func_ptr' (record_spec Ora) record; Ora gv ctx rctx x h;
         data_at ish (tarray tulong (Zlength (decoded x m))) (map vl (decoded x m)) ip;
         data_at psh t_projection (record, (rctx, (up, (bp, rp)))) pp;
         data_at bsh (tarray tulong BLOCKS) (map vl (m_usable m)) up;
         data_at bsh (tarray tulong BLOCKS) (map vl (m_blocked m)) bp;
         data_at bsh (tarray tulong BLOCKS) (map vl (m_reserved m)) rp;
         data_at ssh t_states (states_val (m_states m)) sp;
         data_at cursh tuint curold curp)
  POST [ tint ]
    EX hs: list answer, EX st: Z, EX u: list Z, EX b: list Z, EX r: list Z, EX ss: list (list Z), EX i: Z,
    PROP (run x (start x) (h ++ hs) = Some (projection_end x st (with_states (with_bitmaps m u b r) ss i));
          status_ok st; mem_ok (with_states (with_bitmaps m u b r) ss i); Forall u64_ok (Znth i ss))
    RETURN (vi st)
    SEP (func_ptr' (record_spec Ora) record; Ora gv ctx rctx x (h ++ hs);
         data_at ish (tarray tulong (Zlength (decoded x m))) (map vl (decoded x m)) ip;
         data_at psh t_projection (record, (rctx, (up, (bp, rp)))) pp;
         data_at bsh (tarray tulong BLOCKS) (map vl u) up;
         data_at bsh (tarray tulong BLOCKS) (map vl b) bp;
         data_at bsh (tarray tulong BLOCKS) (map vl r) rp;
         data_at ssh t_states (states_val ss) sp;
         data_at cursh tuint (if st =? S_OK then vi i else curold) curp).

(* boot_handoff_decode_candidate and boot_handoff_project: the specifications of their wrappers. *)
Definition boot_candidate_spec Ora := candidate_pre_post Ora _boot_handoff_decode_candidate.
Definition boot_project_spec Ora := project_pre_post Ora _boot_handoff_project.

Definition Gprog (Ora: ORA) : funspecs :=
  [stream_init_spec Ora; stream_step_spec Ora; decode_init_spec Ora; decode_step_spec Ora;
   projection_entry_spec Ora;
   boot_extent_spec Ora; stream_copy_spec Ora; decode_reset_spec Ora; decode_transition_spec Ora;
   decode_projection_spec Ora; boot_candidate_spec Ora; boot_project_spec Ora;
   extent_spec Ora; copy_spec Ora; projection_spec Ora; candidate_spec Ora; project_spec Ora].
