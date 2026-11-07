(* Specifications of the five functions main calls (patch/handoff_unit.c: handoff_extent, handoff_copy,
   handoff_projection, handoff_candidate, handoff_project) and of the seven callees of the header: the physical
   read and the projection's record, which it is given as function pointers, and the five Lean exports.  Under the
   unit's compspecs.

   The callees are specified by a protocol over an abstract oracle: `Ora gv ctx rctx x h` is the bootloader, the
   record and the Lean behind main's inputs x after they have answered the calls h, for the read's context ctx
   and the record's context rctx, in the global environment gv (the exports take no context, so an
   implementation may keep its state in globals, as the law's does in `law`, which it passes as both contexts).
   Each callee is asked only for the header's next call (Defs.next_call) and records its answer.  The protocol and
   the specifications are parameterized by Ora (a definition parameter: VST's WITH cannot range over mpred), and
   the law instantiates it with its own oracle.

   This file is the interface the law depends on.  The specifications of the header's seven functions, which the
   wrappers forward to, and Gprog are in InternalSpecs.v, which the body proofs may revise without touching this
   file. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require LeanosHandoff.units.Handoff.
Require Import LeanosHandoff.handoff.code.
Require Import LeanosHandoff.proof.Defs.

#[export] Instance CS : compspecs := LeanosHandoff.units.Handoff.CS.
Definition Vprog : varspecs. mk_varspecs LeanosHandoff.handoff.code.prog. Defined.

Definition u64_ok (v: Z) : Prop := 0 <= v <= Int64.max_unsigned.
Definition u32_ok (v: Z) : Prop := 0 <= v <= Int.max_unsigned.

Definition vl (v: Z) : val := Vlong (Int64.repr v).
Definition vi (v: Z) : val := Vint (Int.repr v).

(* struct boot_projection_storage: record, context, usable, blocked, reserved. *)
Definition t_projection := Tstruct _boot_projection_storage noattr.
(* boot_handoff_read and boot_projection_record. *)
Definition t_read : type := Tfunction (tptr tvoid :: tulong :: nil) tulong cc_default.
Definition t_record : type :=
  Tfunction (tptr tvoid :: tulong :: tulong :: tulong :: tulong :: nil) tvoid cc_default.
(* A decoder state, and the two of them (uint64_t states[2][BOOT_DECODE_WORDS]). *)
Definition t_state := tarray tulong WORDS.
Definition t_states := tarray t_state 2.

(* The two states as they lie in memory. *)
Definition states_val (ss: list (list Z)) : list (list val) := map (map vl) ss.

(* The inputs main may choose: 32-bit magic, address, extent and records, a 64-bit candidate, three bitmaps of
   64 words and two states of 41.  (The copy's and the decoded words' lengths depend on the call: each
   specification states the ones it takes.) *)
Definition inputs_ok (x: inputs) : Prop :=
  u32_ok (i_magic x) /\ u32_ok (i_address x) /\ u32_ok (i_total x) /\ u64_ok (i_candidate x) /\
  Zlength (i_usable x) = BLOCKS /\ Zlength (i_blocked x) = BLOCKS /\ Zlength (i_reserved x) = BLOCKS /\
  Zlength (i_states x) = 2 /\ Forall (fun s => Zlength s = WORDS) (i_states x) /\
  u32_ok (i_total_record x) /\ u32_ok (i_length_record x) /\ u32_ok (i_current_record x).

(* ---------------------------------------------------------------------- *)
(* The oracle and the protocols of the seven callees.                    *)
(* ---------------------------------------------------------------------- *)

Definition ORA : Type := globals -> val -> val -> inputs -> list answer -> mpred.

(* The physical read, behind the function pointer `read`: asked for the header's next read after the answers h,
   it answers any 64-bit value and records it. *)
Definition read_spec (Ora: ORA) : funspec :=
  WITH gv: globals, ctx: val, rctx: val, x: inputs, h: list answer, a: Z
  PRE [ tptr tvoid, tulong ]
    PROP (next_call x h = Some (Read a))
    PARAMS (ctx; vl a)
    GLOBALS (gv)
    SEP (Ora gv ctx rctx x h)
  POST [ tulong ]
    EX v: Z,
    PROP (u64_ok v)
    RETURN (vl v)
    SEP (Ora gv ctx rctx x (h ++ [(Read a, v)])).

(* The projection's record, behind projection->record with projection->context: asked for the header's next
   call, it records it (the answer 0, as it returns nothing). *)
Definition record_spec (Ora: ORA) : funspec :=
  WITH gv: globals, ctx: val, rctx: val, x: inputs, h: list answer, slot: Z, base: Z, len: Z, kind: Z
  PRE [ tptr tvoid, tulong, tulong, tulong, tulong ]
    PROP (next_call x h = Some (Record slot base len kind))
    PARAMS (rctx; vl slot; vl base; vl len; vl kind)
    GLOBALS (gv)
    SEP (Ora gv ctx rctx x h)
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (Ora gv ctx rctx x (h ++ [(Record slot base len kind, 0)])).

(* The five exports: each, asked for the header's next call after the answers h, answers any 64-bit value and
   records the answer. *)
Definition stream_init_spec (Ora: ORA) :=
  DECLARE _leanos_boot_handoff_stream_init
  WITH gv: globals, ctx: val, rctx: val, x: inputs, h: list answer, mg: Z, ad: Z, t: Z, id: Z, q: Z
  PRE [ tulong, tulong, tulong, tulong, tulong ]
    PROP (next_call x h = Some (StreamInit mg ad t id q))
    PARAMS (vl mg; vl ad; vl t; vl id; vl q)
    GLOBALS (gv)
    SEP (Ora gv ctx rctx x h)
  POST [ tulong ]
    EX v: Z,
    PROP (u64_ok v)
    RETURN (vl v)
    SEP (Ora gv ctx rctx x (h ++ [(StreamInit mg ad t id q, v)])).

(* The stream transition of the carried state st (seven words). *)
Definition stream_step_spec (Ora: ORA) :=
  DECLARE _leanos_boot_handoff_stream_step
  WITH gv: globals, ctx: val, rctx: val, x: inputs, h: list answer, st: list Z,
       id: Z, off: Z, cnt: Z, ch: Z, term: Z, q: Z
  PRE [ tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong ]
    PROP (next_call x h = Some (StreamStep st id off cnt ch term q))
    PARAMS (vl (Znth 0 st); vl (Znth 1 st); vl (Znth 2 st); vl (Znth 3 st); vl (Znth 4 st); vl (Znth 5 st);
            vl (Znth 6 st); vl id; vl off; vl cnt; vl ch; vl term; vl q)
    GLOBALS (gv)
    SEP (Ora gv ctx rctx x h)
  POST [ tulong ]
    EX v: Z,
    PROP (u64_ok v)
    RETURN (vl v)
    SEP (Ora gv ctx rctx x (h ++ [(StreamStep st id off cnt ch term q, v)])).

Definition decode_init_spec (Ora: ORA) :=
  DECLARE _leanos_boot_decode_init_v5
  WITH gv: globals, ctx: val, rctx: val, x: inputs, h: list answer, mg: Z, ad: Z, t: Z, tg: Z, q: Z
  PRE [ tulong, tulong, tulong, tulong, tulong ]
    PROP (next_call x h = Some (DecodeInit mg ad t tg q))
    PARAMS (vl mg; vl ad; vl t; vl tg; vl q)
    GLOBALS (gv)
    SEP (Ora gv ctx rctx x h)
  POST [ tulong ]
    EX v: Z,
    PROP (u64_ok v)
    RETURN (vl v)
    SEP (Ora gv ctx rctx x (h ++ [(DecodeInit mg ad t tg q, v)])).

(* The decoder transition of the old state s (all 41 words: the call names the state; the export is passed
   words 0..18 and 23..38 of it, as boot_decode_transition loads them). *)
Definition decode_step_spec (Ora: ORA) :=
  DECLARE _leanos_boot_decode_step_v5
  WITH gv: globals, ctx: val, rctx: val, x: inputs, h: list answer, s: list Z,
       id: Z, off: Z, ch: Z, term: Z, q: Z
  PRE [ tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong,
        tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong,
        tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong,
        tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong ]
    PROP (next_call x h = Some (DecodeStep s id off ch term q))
    PARAMS (vl (Znth 0 s); vl (Znth 1 s); vl (Znth 2 s); vl (Znth 3 s); vl (Znth 4 s); vl (Znth 5 s);
            vl (Znth 6 s); vl (Znth 7 s); vl (Znth 8 s); vl (Znth 9 s); vl (Znth 10 s); vl (Znth 11 s);
            vl (Znth 12 s); vl (Znth 13 s); vl (Znth 14 s); vl (Znth 15 s); vl (Znth 16 s); vl (Znth 17 s);
            vl (Znth 18 s);
            vl (Znth 23 s); vl (Znth 24 s); vl (Znth 25 s); vl (Znth 26 s); vl (Znth 27 s); vl (Znth 28 s);
            vl (Znth 29 s); vl (Znth 30 s); vl (Znth 31 s); vl (Znth 32 s); vl (Znth 33 s); vl (Znth 34 s);
            vl (Znth 35 s); vl (Znth 36 s); vl (Znth 37 s); vl (Znth 38 s);
            vl id; vl off; vl ch; vl term; vl q)
    GLOBALS (gv)
    SEP (Ora gv ctx rctx x h)
  POST [ tulong ]
    EX v: Z,
    PROP (u64_ok v)
    RETURN (vl v)
    SEP (Ora gv ctx rctx x (h ++ [(DecodeStep s id off ch term q, v)])).

Definition projection_entry_spec (Ora: ORA) :=
  DECLARE _leanos_boot_projection_entry
  WITH gv: globals, ctx: val, rctx: val, x: inputs, h: list answer, bs: Z, ln: Z, kd: Z, blk: Z, us: Z, bl: Z,
       q: Z
  PRE [ tulong, tulong, tulong, tulong, tulong, tulong, tulong ]
    PROP (next_call x h = Some (Entry bs ln kd blk us bl q))
    PARAMS (vl bs; vl ln; vl kd; vl blk; vl us; vl bl; vl q)
    GLOBALS (gv)
    SEP (Ora gv ctx rctx x h)
  POST [ tulong ]
    EX v: Z,
    PROP (u64_ok v)
    RETURN (vl v)
    SEP (Ora gv ctx rctx x (h ++ [(Entry bs ln kd blk us bl q, v)])).

(* ---------------------------------------------------------------------- *)
(* The five functions main calls.                                        *)
(* ---------------------------------------------------------------------- *)

(* Common to the five: main's inputs x, with i_call x the call; the oracle before the call (an allocation's
   second call, after the answers of its first); separate objects, each writable unless said otherwise and
   holding x's prior contents.  Each returns after its callees answered exactly the calls h of a complete run
   (returns: the law's EXPECT_NOTHING) whose outcome is (st, m): it returns st, every object it is given holds
   m's contents, its record the outcome's (Defs.out_*_record), and m keeps what the function is not given
   (Defs.keeps), which main compares too.  Only handoff_extent, an allocation's first call, returns before the
   run is complete: on OK it leaves the model at after_extent, where handoff_project starts (Defs.extent_end). *)

(* handoff_extent(read, context, magic, info_address, total), and boot_handoff_extent (InternalSpecs.v), which it
   forwards to: the first call of an allocation.  On OK the model is at the copy's start with the extent T it
   wrote (after_extent), and T fits a copy; otherwise the call returned st with nothing written. *)
Definition extent_pre_post (Ora: ORA) (name: ident) :=
  DECLARE name
  WITH gv: globals, read: val, ctx: val, rctx: val, x: inputs, tp: val, tsh: share
  PRE [ tptr t_read, tptr tvoid, tuint, tuint, tptr tuint ]
    PROP (i_call x = FAllocate; inputs_ok x; writable_share tsh)
    PARAMS (read; ctx; vi (i_magic x); vi (i_address x); tp)
    GLOBALS (gv)
    SEP (func_ptr' (read_spec Ora) read; Ora gv ctx rctx x nil; data_at tsh tuint (vi (i_total_record x)) tp)
  POST [ tint ]
    EX h: list answer, EX st: Z, EX T: Z,
    PROP (run x (start x) h = Some (extent_end x st T); status_ok st; st = S_OK -> extent_fits T)
    RETURN (vi st)
    SEP (func_ptr' (read_spec Ora) read; Ora gv ctx rctx x h;
         data_at tsh tuint (vi (if st =? S_OK then T else i_total_record x)) tp).

(* handoff_project(read, context, magic, info_address, total, copy, projection, states, current), and
   boot_handoff_project, which it forwards to: an allocation's second call, with the extent T the first wrote,
   after its answers h.  The projection record (readable) names the record callback, its context rctx and the
   three bitmaps; the copy has 8192 words.  rctx is a pointer or null, as a void * the body loads from the
   record must be (the law passes &law). *)
Definition project_pre_post (Ora: ORA) (name: ident) :=
  DECLARE name
  WITH gv: globals, read: val, ctx: val, rctx: val, record: val, x: inputs, h: list answer, T: Z,
       cp: val, csh: share, pp: val, psh: share, up: val, bp: val, rp: val, bsh: share, sp: val, ssh: share,
       curp: val, cursh: share
  PRE [ tptr t_read, tptr tvoid, tuint, tuint, tuint, tptr tulong, tptr t_projection, tptr t_state, tptr tuint ]
    PROP (i_call x = FAllocate; inputs_ok x; Zlength (i_copy x) = COPY_WORDS;
          run x (start x) h = Some (after_extent x T); extent_fits T; is_pointer_or_null rctx;
          writable_share csh; readable_share psh; writable_share bsh; writable_share ssh; writable_share cursh)
    PARAMS (read; ctx; vi (i_magic x); vi (i_address x); vi T; cp; pp; sp; curp)
    GLOBALS (gv)
    SEP (func_ptr' (read_spec Ora) read; func_ptr' (record_spec Ora) record; Ora gv ctx rctx x h;
         data_at csh (tarray tulong COPY_WORDS) (map vl (i_copy x)) cp;
         data_at psh t_projection (record, (rctx, (up, (bp, rp)))) pp;
         data_at bsh (tarray tulong BLOCKS) (map vl (i_usable x)) up;
         data_at bsh (tarray tulong BLOCKS) (map vl (i_blocked x)) bp;
         data_at bsh (tarray tulong BLOCKS) (map vl (i_reserved x)) rp;
         data_at ssh t_states (states_val (i_states x)) sp;
         data_at cursh tuint (vi (i_current_record x)) curp)
  POST [ tint ]
    EX h': list answer, EX st: Z, EX m: mem,
    PROP (returns x h' = Some (st, m); keeps x (with_extent (initial x) T) m)
    RETURN (vi st)
    SEP (func_ptr' (read_spec Ora) read; func_ptr' (record_spec Ora) record; Ora gv ctx rctx x h';
         data_at csh (tarray tulong COPY_WORDS) (map vl (m_copy m)) cp;
         data_at psh t_projection (record, (rctx, (up, (bp, rp)))) pp;
         data_at bsh (tarray tulong BLOCKS) (map vl (m_usable m)) up;
         data_at bsh (tarray tulong BLOCKS) (map vl (m_blocked m)) bp;
         data_at bsh (tarray tulong BLOCKS) (map vl (m_reserved m)) rp;
         data_at ssh t_states (states_val (m_states m)) sp;
         data_at cursh tuint (vi (out_current_record x st m)) curp).

(* handoff_copy(read, context, magic, info_address, total, copy, length): a copy alone, of an extent that fits,
   into a copy of 8192 words. *)
Definition copy_spec (Ora: ORA) :=
  DECLARE _handoff_copy
  WITH gv: globals, read: val, ctx: val, rctx: val, x: inputs, cp: val, csh: share, lp: val, lsh: share
  PRE [ tptr t_read, tptr tvoid, tuint, tuint, tuint, tptr tulong, tptr tuint ]
    PROP (i_call x = FCopy; inputs_ok x; extent_fits (i_total x); Zlength (i_copy x) = COPY_WORDS;
          writable_share csh; writable_share lsh)
    PARAMS (read; ctx; vi (i_magic x); vi (i_address x); vi (i_total x); cp; lp)
    GLOBALS (gv)
    SEP (func_ptr' (read_spec Ora) read; Ora gv ctx rctx x nil;
         data_at csh (tarray tulong COPY_WORDS) (map vl (i_copy x)) cp;
         data_at lsh tuint (vi (i_length_record x)) lp)
  POST [ tint ]
    EX h: list answer, EX st: Z, EX m: mem,
    PROP (returns x h = Some (st, m); keeps x (initial x) m)
    RETURN (vi st)
    SEP (func_ptr' (read_spec Ora) read; Ora gv ctx rctx x h;
         data_at csh (tarray tulong COPY_WORDS) (map vl (m_copy m)) cp;
         data_at lsh tuint (vi (out_length_record x st m)) lp).

(* handoff_projection(magic, info_address, total, info, projection, states, current): a projection alone, of an
   extent that fits, over i_total x / 8 words (readable). *)
Definition projection_spec (Ora: ORA) :=
  DECLARE _handoff_projection
  WITH gv: globals, ctx: val, rctx: val, record: val, x: inputs, ip: val, ish: share,
       pp: val, psh: share, up: val, bp: val, rp: val, bsh: share, sp: val, ssh: share, curp: val, cursh: share
  PRE [ tuint, tuint, tuint, tptr tulong, tptr t_projection, tptr t_state, tptr tuint ]
    PROP (i_call x = FProjection; inputs_ok x; extent_fits (i_total x); Zlength (i_info x) = i_total x / 8;
          is_pointer_or_null rctx; readable_share ish; readable_share psh; writable_share bsh; writable_share ssh; writable_share cursh)
    PARAMS (vi (i_magic x); vi (i_address x); vi (i_total x); ip; pp; sp; curp)
    GLOBALS (gv)
    SEP (func_ptr' (record_spec Ora) record; Ora gv ctx rctx x nil;
         data_at ish (tarray tulong (i_total x / 8)) (map vl (i_info x)) ip;
         data_at psh t_projection (record, (rctx, (up, (bp, rp)))) pp;
         data_at bsh (tarray tulong BLOCKS) (map vl (i_usable x)) up;
         data_at bsh (tarray tulong BLOCKS) (map vl (i_blocked x)) bp;
         data_at bsh (tarray tulong BLOCKS) (map vl (i_reserved x)) rp;
         data_at ssh t_states (states_val (i_states x)) sp;
         data_at cursh tuint (vi (i_current_record x)) curp)
  POST [ tint ]
    EX h: list answer, EX st: Z, EX m: mem,
    PROP (returns x h = Some (st, m); keeps x (initial x) m)
    RETURN (vi st)
    SEP (func_ptr' (record_spec Ora) record; Ora gv ctx rctx x h;
         data_at ish (tarray tulong (i_total x / 8)) (map vl (i_info x)) ip;
         data_at psh t_projection (record, (rctx, (up, (bp, rp)))) pp;
         data_at bsh (tarray tulong BLOCKS) (map vl (m_usable m)) up;
         data_at bsh (tarray tulong BLOCKS) (map vl (m_blocked m)) bp;
         data_at bsh (tarray tulong BLOCKS) (map vl (m_reserved m)) rp;
         data_at ssh t_states (states_val (m_states m)) sp;
         data_at cursh tuint (vi (out_current_record x st m)) curp).

(* handoff_candidate(magic, info_address, total, candidate, info, states, current), and
   boot_handoff_decode_candidate, which it forwards to: a candidate alone, likewise without a projection. *)
Definition candidate_pre_post (Ora: ORA) (name: ident) :=
  DECLARE name
  WITH gv: globals, ctx: val, rctx: val, x: inputs, ip: val, ish: share, sp: val, ssh: share,
       curp: val, cursh: share
  PRE [ tuint, tuint, tuint, tulong, tptr tulong, tptr t_state, tptr tuint ]
    PROP (i_call x = FCandidate; inputs_ok x; extent_fits (i_total x); Zlength (i_info x) = i_total x / 8;
          readable_share ish; writable_share ssh; writable_share cursh)
    PARAMS (vi (i_magic x); vi (i_address x); vi (i_total x); vl (i_candidate x); ip; sp; curp)
    GLOBALS (gv)
    SEP (Ora gv ctx rctx x nil;
         data_at ish (tarray tulong (i_total x / 8)) (map vl (i_info x)) ip;
         data_at ssh t_states (states_val (i_states x)) sp;
         data_at cursh tuint (vi (i_current_record x)) curp)
  POST [ tint ]
    EX h: list answer, EX st: Z, EX m: mem,
    PROP (returns x h = Some (st, m); keeps x (initial x) m)
    RETURN (vi st)
    SEP (Ora gv ctx rctx x h;
         data_at ish (tarray tulong (i_total x / 8)) (map vl (i_info x)) ip;
         data_at ssh t_states (states_val (m_states m)) sp;
         data_at cursh tuint (vi (out_current_record x st m)) curp).

Definition extent_spec Ora := extent_pre_post Ora _handoff_extent.
Definition project_spec Ora := project_pre_post Ora _handoff_project.
Definition candidate_spec Ora := candidate_pre_post Ora _handoff_candidate.
