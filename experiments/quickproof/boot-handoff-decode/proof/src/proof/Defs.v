(* Pure definitions shared by every proof of leanos_handoff (include/boot_handoff_decode.h, through the wrapper
   unit patch/handoff_unit.c): the four calls main may make (an allocation, a copy alone, a projection alone, a
   candidate alone) as one state machine over the answers of the header's callees: the physical read, the
   projection's record and the five Lean exports.  No program here.

   The model follows the first comment of harness/handoff_decode_exact.c (the law's claim) clause by clause, and
   its stages are the law's `expect` with its counters (harness/handoff_decode_exact.h):

     stage                        law
     ExpectSize                   EXPECT_SIZE
     ExpectStreamInit a           EXPECT_STREAM_INIT, word = |a|, answer[0 .. word) = a
     ExpectChunk k st             EXPECT_CHUNK, chunk = k, stream = st
     ExpectStreamStep k st c a    EXPECT_STREAM_STEP, chunk = k, stream = st, value = c, word = |a|, answer = a ..
     ExpectDecodeInit a           EXPECT_DECODE_INIT, word = |a|, answer = a ..
     ExpectDecodeStep k a         EXPECT_DECODE_STEP, chunk = k, value = word k decoded, word = |a|, answer = a ..
     ExpectRecord k               EXPECT_RECORD, chunk = k
     ExpectEntry k b a            EXPECT_ENTRY, chunk = k, block = b, word = |a|, answer = a ..
     Return st m                  EXPECT_NOTHING, verdict = st

   and the model's mem is the law's model of memory: total, extent_ok, copy_expect, usable_expect,
   blocked_expect, reserved_expect, states_expect and at.  So each callee of the harness moves the law's record
   exactly as `step` moves the model, and `main`'s final comparisons read the model's outcome.

   What the calls and the status depend on: the answers and the scalar inputs (the call, the magic, the address,
   the extent of a call alone, the candidate), never what memory held before, except where that memory was
   itself written from the answers first:
   - the decoder's chunk argument is word k of the words decoded: in an allocation, the copy's word k, which the
     stream wrote from chunk k as read (the EXPOSED check makes it answer 7 too); alone, the input list i_info;
   - the decoder's state words are the reset's or the last transition's answers;
   - the block projection's usable and blocked arguments are the current bitmap words, which the decoder zeroed
     before its reset and then wrote from the projection's answers.
   The prior contents show only in what the run leaves behind (`mem`).

   Words are Z values in their C type's range: uint64_t, and uint32_t for the magic, the address, the extents and
   the records (the specifications, HandoffSpecs.inputs_ok, state the ranges).  The C's integer details:
   - offsets are uint64_t: chunk k is at offset 8k, read at the address + 8k ((uint64_t)info_address + offset),
     and the loops run while 8k < T, none at all for an extent of 0;
   - the size read is (uint32_t)read(...): the answer mod 2^32;
   - 16 MiB - address is computed in uint32_t, after the POINTER_HIGH check (so it does not wrap);
   - terminal = (offset + 8 == total), the record's slot = word 11 - 1 (after COUNT_ZERO), `1u - at`: none wraps.

   One check of the C cannot fail, and the model leaves it out: COPY_LENGTH in boot_handoff_project (the copy
   writes the extent to `length` exactly on OK).  The body proof shows it passes.  The law does not name it.
   The stream's final checks (stream_final) are the law's, so the model keeps them, though STREAM_INCOMPLETE_OFFSET
   cannot fail either (every accepted chunk's word 5 is its end, and the reset's is 0), and
   STREAM_INCOMPLETE_STATUS fails only for an extent of 0 (the reset's word 1 is 0). *)
Require Import VST.floyd.proofauto.
Local Open Scope Z_scope.
Local Open Scope bool_scope.   (* && and || are andb and orb here, not VST's andp and orp *)

(* ---------------------------------------------------------------------- *)
(* The statuses and the constants.                                        *)
(* ---------------------------------------------------------------------- *)

(* enum boot_handoff_status, in order: the statuses of the header without the prefix BOOT_HANDOFF_. *)
Definition S_OK : Z := 0.
Definition S_MAGIC : Z := 1.
Definition S_POINTER_ALIGNMENT : Z := 2.
Definition S_POINTER_LOW : Z := 3.
Definition S_POINTER_HIGH : Z := 4.
Definition S_BOUNDS_SMALL : Z := 5.
Definition S_BOUNDS_LARGE : Z := 6.
Definition S_BOUNDS_ALIGNMENT : Z := 7.
Definition S_BOUNDS_LIMIT : Z := 8.
Definition S_STREAM_INIT_VERSION : Z := 9.
Definition S_STREAM_INIT_STATUS : Z := 10.
Definition S_STREAM_INIT_ERROR : Z := 11.
Definition S_STREAM_INIT_IDENTITY : Z := 12.
Definition S_STREAM_INIT_EXTENT : Z := 13.
Definition S_STREAM_INIT_OFFSET : Z := 14.
Definition S_STREAM_STEP_VERSION : Z := 15.
Definition S_STREAM_STEP_ERROR : Z := 16.
Definition S_STREAM_STEP_IDENTITY : Z := 17.
Definition S_STREAM_STEP_EXTENT : Z := 18.
Definition S_STREAM_STEP_OFFSET : Z := 19.
Definition S_STREAM_STEP_COUNT : Z := 20.
Definition S_STREAM_STEP_EXPOSED : Z := 21.
Definition S_STREAM_STEP_STATUS : Z := 22.
Definition S_STREAM_INCOMPLETE_STATUS : Z := 23.
Definition S_STREAM_INCOMPLETE_OFFSET : Z := 24.
Definition S_COPY_LENGTH : Z := 25.
Definition S_DECODE_INIT_VERSION : Z := 26.
Definition S_DECODE_INIT_STATUS : Z := 27.
Definition S_DECODE_INIT_ERROR : Z := 28.
Definition S_DECODE_INIT_IDENTITY : Z := 29.
Definition S_DECODE_INIT_EXTENT : Z := 30.
Definition S_DECODE_INIT_OFFSET : Z := 31.
Definition S_DECODE_INIT_TARGET : Z := 32.
Definition S_DECODE_INIT_TAG_COUNT : Z := 33.
Definition S_DECODE_INIT_ROOT_STATUS : Z := 34.
Definition S_PROJECTION_COUNT_ZERO : Z := 35.
Definition S_PROJECTION_COUNT_LARGE : Z := 36.
Definition S_PROJECTION_ENTRY_STATUS : Z := 37.
Definition S_PROJECTION_ENTRY_ERROR : Z := 38.
Definition S_DECODE_INCOMPLETE_STATUS : Z := 39.
Definition S_DECODE_INCOMPLETE_OFFSET : Z := 40.
Definition S_DECODE_INCOMPLETE_PHASE : Z := 41.
Definition S_DECODE_REJECTED_STATUS : Z := 42.
Definition S_DECODE_REJECTED_ERROR : Z := 43.
Definition S_AUTHORITY_INIT_VERSION : Z := 44.
Definition S_AUTHORITY_INIT_STATUS : Z := 45.
Definition S_AUTHORITY_INIT_ERROR : Z := 46.
Definition S_AUTHORITY_INIT_IDENTITY : Z := 47.
Definition S_AUTHORITY_INIT_EXTENT : Z := 48.
Definition S_AUTHORITY_INIT_OFFSET : Z := 49.
Definition S_AUTHORITY_INIT_TARGET : Z := 50.
Definition S_AUTHORITY_INIT_TAG_COUNT : Z := 51.
Definition S_AUTHORITY_INIT_ROOT_STATUS : Z := 52.
Definition S_AUTHORITY_REJECTED_STATUS : Z := 53.
Definition S_AUTHORITY_REJECTED_ERROR : Z := 54.
Definition S_AUTHORITY_REJECTED_OFFSET : Z := 55.
Definition S_AUTHORITY_REJECTED_PHASE : Z := 56.
Definition S_AUTHORITY_REJECTED_TARGET : Z := 57.

(* The header's constants, as notations so that lia and the list tactics see the numbers. *)
Notation MAGIC := 920085129%Z (only parsing).    (* BOOT_HANDOFF_MULTIBOOT2_MAGIC, 0x36d76289 *)
Notation PAGE_BYTES := 4096%Z (only parsing).    (* BOOT_HANDOFF_PAGE_BYTES *)
Notation LIMIT := 16777216%Z (only parsing).     (* BOOT_HANDOFF_ACCESSIBLE_LIMIT, 16 MiB *)
Notation MAX_BYTES := 65536%Z (only parsing).    (* BOOT_HANDOFF_MAX_BYTES *)
Notation COPY_WORDS := 8192%Z (only parsing).    (* BOOT_HANDOFF_MAX_WORDS, the copy's words *)
Notation WORDS := 41%Z (only parsing).           (* BOOT_DECODE_WORDS, a decoder state's words *)
Notation ENTRIES := 256%Z (only parsing).        (* BOOT_PROJECTION_ENTRIES *)
Notation BLOCKS := 64%Z (only parsing).          (* BOOT_PROJECTION_BLOCKS, a bitmap's words *)

(* ---------------------------------------------------------------------- *)
(* The inputs.                                                            *)
(* ---------------------------------------------------------------------- *)

(* The function main calls (CALL_ALLOCATE .. CALL_CANDIDATE): handoff_extent then handoff_project,
   handoff_copy, handoff_projection, handoff_candidate. *)
Inductive func : Type := FAllocate | FCopy | FProjection | FCandidate.

(* Everything main chooses: the call; the magic and the information's address; the extent of a call alone (an
   allocation's comes from its size read); the candidate (the target frame of a candidate alone); the words a
   decoder alone reads (total / 8 of them); and what the storage holds before the call: the copy (8192 words,
   for an allocation or a copy), the three bitmaps (64 words each), the two decoder states (2 x 41 words) and
   the three records (the extent, the copy's length and the state's index). *)
Record inputs : Type := mk_inputs {
  i_call: func;
  i_magic: Z; i_address: Z; i_total: Z; i_candidate: Z;
  i_info: list Z;
  i_copy: list Z; i_usable: list Z; i_blocked: list Z; i_reserved: list Z; i_states: list (list Z);
  i_total_record: Z; i_length_record: Z; i_current_record: Z }.

(* The decoder builds a projection (law.projection): in an allocation and a projection alone. *)
Definition projection (x: inputs) : bool :=
  match i_call x with FAllocate | FProjection => true | FCopy | FCandidate => false end.

(* The decoder's target frame (law.candidate): the candidate for a candidate alone, 0 with a projection. *)
Definition target (x: inputs) : Z := match i_call x with FCandidate => i_candidate x | _ => 0 end.

Definition is_copy (x: inputs) : bool := match i_call x with FCopy => true | _ => false end.

(* ---------------------------------------------------------------------- *)
(* Calls and answers.                                                     *)
(* ---------------------------------------------------------------------- *)

(* A call of the header to one of its callees, with its arguments. *)
Inductive call : Type :=
  (* read(context, physical_address) *)
  | Read (address: Z)
  (* leanos_boot_handoff_stream_init(magic, info_address, total_bytes, stream_identity, query) *)
  | StreamInit (magic address total identity query: Z)
  (* leanos_boot_handoff_stream_step(state[0..6], stream_identity, offset, count, chunk, terminal, query) *)
  | StreamStep (state: list Z) (identity offset count chunk terminal query: Z)
  (* leanos_boot_decode_init_v5(magic, address, extent, target, query) *)
  | DecodeInit (magic address total target query: Z)
  (* leanos_boot_decode_step_v5(state[0..18], state[23..38], stream_identity, stream_offset, chunk, terminal,
     query): the transition of the old state `state`, all 41 of its words; the export is passed the 35 words
     0..18 and 23..38 of it (HandoffSpecs.decode_step_spec) *)
  | DecodeStep (state: list Z) (identity offset chunk terminal query: Z)
  (* projection->record(projection->context, slot, base, length, kind) *)
  | Record (slot base length kind: Z)
  (* leanos_boot_projection_entry(base, length, kind, block, usable, blocked, query) *)
  | Entry (base length kind block usable blocked query: Z).

(* One answered call: the call and the value the callee returned (0 for the record, which returns nothing). *)
Definition answer : Type := (call * Z)%type.

Definition call_eq_dec (a b: call) : {a = b} + {a <> b}.
Proof. decide equality; first [ apply Z.eq_dec | apply (list_eq_dec Z.eq_dec) ]. Defined.

(* ---------------------------------------------------------------------- *)
(* The model of memory.                                                   *)
(* ---------------------------------------------------------------------- *)

(* What the law keeps of memory (struct law): the extent (total: the input's, or for an allocation the size
   read's once the bounds accept it) and whether the bounds accepted one (extent_ok); the copy (copy_expect); the
   usable, blocked and reserved bitmaps; the decoder's two states (states_expect) and the index of the current
   one (at). *)
Record mem : Type := mk_mem {
  m_total: Z; m_extent_ok: bool;
  m_copy: list Z;
  m_usable: list Z; m_blocked: list Z; m_reserved: list Z;
  m_states: list (list Z); m_at: Z }.

(* Before the call (main sets law.at to 0). *)
Definition initial (x: inputs) : mem :=
  mk_mem (i_total x) false (i_copy x) (i_usable x) (i_blocked x) (i_reserved x) (i_states x) 0.

(* The size read's extent T, accepted. *)
Definition with_extent (m: mem) (T: Z) : mem :=
  mk_mem T true (m_copy m) (m_usable m) (m_blocked m) (m_reserved m) (m_states m) (m_at m).
(* The copy c. *)
Definition with_copy (m: mem) (c: list Z) : mem :=
  mk_mem (m_total m) (m_extent_ok m) c (m_usable m) (m_blocked m) (m_reserved m) (m_states m) (m_at m).
(* The bitmaps u, b, r. *)
Definition with_bitmaps (m: mem) (u b r: list Z) : mem :=
  mk_mem (m_total m) (m_extent_ok m) (m_copy m) u b r (m_states m) (m_at m).
(* The states ss, the current one ss[i]. *)
Definition with_states (m: mem) (ss: list (list Z)) (i: Z) : mem :=
  mk_mem (m_total m) (m_extent_ok m) (m_copy m) (m_usable m) (m_blocked m) (m_reserved m) ss i.

(* The decoder's current state, states[at]. *)
Definition current (m: mem) : list Z := Znth (m_at m) (m_states m).

(* The words the decoder reads (law.info_expect): the copy in an allocation, the input's words alone. *)
Definition decoded (x: inputs) (m: mem) : list Z :=
  match i_call x with FAllocate => m_copy m | _ => i_info x end.

(* A bitmap of zeros. *)
Definition zeros : list Z := Zrepeat 0 BLOCKS.

(* ---------------------------------------------------------------------- *)
(* The checks, each the first status that applies, or OK.                 *)
(* ---------------------------------------------------------------------- *)

(* The terminal marker of chunk k of an extent T: 1 at the last chunk, 0 before. *)
Definition terminal (T k: Z) : Z := if 8 * k + 8 =? T then 1 else 0.

(* boot_handoff_extent before its read: the magic, then the address. *)
Definition pointer_check (x: inputs) : Z :=
  if negb (i_magic x =? MAGIC) then S_MAGIC
  else if negb (i_address x mod 8 =? 0) then S_POINTER_ALIGNMENT
  else if i_address x <? PAGE_BYTES then S_POINTER_LOW
  else if LIMIT <=? i_address x then S_POINTER_HIGH
  else S_OK.

(* The extent T the size read declares (the low 32 bits of its answer). *)
Definition bounds_check (x: inputs) (T: Z) : Z :=
  if T <? 16 then S_BOUNDS_SMALL
  else if MAX_BYTES <? T then S_BOUNDS_LARGE
  else if negb (T mod 8 =? 0) then S_BOUNDS_ALIGNMENT
  else if LIMIT - i_address x <? T then S_BOUNDS_LIMIT
  else S_OK.

(* The stream reset's words 0..5 (a: its seven answers), for the extent T. *)
Definition stream_init_check (x: inputs) (T: Z) (a: list Z) : Z :=
  if negb (Znth 0 a =? 2) then S_STREAM_INIT_VERSION
  else if negb (Znth 1 a =? 0) then S_STREAM_INIT_STATUS
  else if negb (Znth 2 a =? 0) then S_STREAM_INIT_ERROR
  else if negb (Znth 3 a =? i_address x) then S_STREAM_INIT_IDENTITY
  else if negb (Znth 4 a =? T) then S_STREAM_INIT_EXTENT
  else if negb (Znth 5 a =? 0) then S_STREAM_INIT_OFFSET
  else S_OK.

(* Chunk k's transition (a: its nine answers), the chunk c as read. *)
Definition stream_step_check (x: inputs) (T k c: Z) (a: list Z) : Z :=
  if negb (Znth 0 a =? 2) then S_STREAM_STEP_VERSION
  else if negb (Znth 2 a =? 0) then S_STREAM_STEP_ERROR
  else if negb (Znth 3 a =? i_address x) then S_STREAM_STEP_IDENTITY
  else if negb (Znth 4 a =? T) then S_STREAM_STEP_EXTENT
  else if negb (Znth 5 a =? 8 * k + 8) then S_STREAM_STEP_OFFSET
  else if negb (Znth 8 a =? 8) then S_STREAM_STEP_COUNT
  else if negb (Znth 7 a =? c) then S_STREAM_STEP_EXPOSED
  else if negb (Znth 1 a =? terminal T k) then S_STREAM_STEP_STATUS
  else S_OK.

(* After the last chunk, the carried state st. *)
Definition stream_final (T: Z) (st: list Z) : Z :=
  if negb (Znth 1 st =? 1) then S_STREAM_INCOMPLETE_STATUS
  else if negb (Znth 5 st =? T) then S_STREAM_INCOMPLETE_OFFSET
  else S_OK.

(* A status prefixed DECODE_ with a projection, AUTHORITY_ for a candidate. *)
Definition by_call (x: inputs) (decode authority: Z) : Z := if projection x then decode else authority.

(* The decoder reset's words (a: its 41 answers). *)
Definition decode_init_check (x: inputs) (T: Z) (a: list Z) : Z :=
  if negb (Znth 0 a =? 5) then by_call x S_DECODE_INIT_VERSION S_AUTHORITY_INIT_VERSION
  else if negb (Znth 1 a =? 0) then by_call x S_DECODE_INIT_STATUS S_AUTHORITY_INIT_STATUS
  else if negb (Znth 2 a =? 0) then by_call x S_DECODE_INIT_ERROR S_AUTHORITY_INIT_ERROR
  else if negb (Znth 3 a =? i_address x) then by_call x S_DECODE_INIT_IDENTITY S_AUTHORITY_INIT_IDENTITY
  else if negb (Znth 4 a =? T) then by_call x S_DECODE_INIT_EXTENT S_AUTHORITY_INIT_EXTENT
  else if negb (Znth 5 a =? 0) then by_call x S_DECODE_INIT_OFFSET S_AUTHORITY_INIT_OFFSET
  else if negb (Znth 16 a =? target x) then by_call x S_DECODE_INIT_TARGET S_AUTHORITY_INIT_TARGET
  else if negb (Znth 18 a =? 0) then by_call x S_DECODE_INIT_TAG_COUNT S_AUTHORITY_INIT_TAG_COUNT
  else if negb (Znth 30 a =? 0) then by_call x S_DECODE_INIT_ROOT_STATUS S_AUTHORITY_INIT_ROOT_STATUS
  else S_OK.

(* An entry event's count, word 11 of the state s. *)
Definition event_check (s: list Z) : Z :=
  if Znth 11 s =? 0 then S_PROJECTION_COUNT_ZERO
  else if ENTRIES <? Znth 11 s then S_PROJECTION_COUNT_LARGE
  else S_OK.

(* A block projection's words 1 and 2 (a: its answers to words 1..4). *)
Definition entry_check (a: list Z) : Z :=
  if negb (Znth 0 a =? 1) then S_PROJECTION_ENTRY_STATUS
  else if negb (Znth 1 a =? 0) then S_PROJECTION_ENTRY_ERROR
  else S_OK.

(* With a projection, the final state s whose error (word 2) is 0. *)
Definition incomplete_check (T: Z) (s: list Z) : Z :=
  if negb (Znth 1 s =? 1) then S_DECODE_INCOMPLETE_STATUS
  else if negb (Znth 5 s =? T) then S_DECODE_INCOMPLETE_OFFSET
  else if negb (Znth 7 s =? 7) then S_DECODE_INCOMPLETE_PHASE
  else S_OK.

(* boot_handoff_project after the decoder returned OK, the final state s. *)
Definition rejected_check (s: list Z) : Z :=
  if negb (Znth 1 s =? 1) then S_DECODE_REJECTED_STATUS
  else if negb (Znth 2 s =? 0) then S_DECODE_REJECTED_ERROR
  else S_OK.

(* For a candidate, the final state s. *)
Definition authority_check (x: inputs) (T: Z) (s: list Z) : Z :=
  if negb (Znth 1 s =? 1) then S_AUTHORITY_REJECTED_STATUS
  else if negb (Znth 2 s =? 0) then S_AUTHORITY_REJECTED_ERROR
  else if negb (Znth 5 s =? T) then S_AUTHORITY_REJECTED_OFFSET
  else if negb (Znth 7 s =? 7) then S_AUTHORITY_REJECTED_PHASE
  else if negb (Znth 16 s =? i_candidate x) then S_AUTHORITY_REJECTED_TARGET
  else S_OK.

(* ---------------------------------------------------------------------- *)
(* The machine.                                                           *)
(* ---------------------------------------------------------------------- *)

(* Where the header is between calls (the law's `expect` with its counters; see the table above).  a holds the
   answers to the current reset, transition or block projection so far; k is a chunk, b a block. *)
Inductive stage : Type :=
  | ExpectSize
  | ExpectStreamInit (a: list Z)
  | ExpectChunk (k: Z) (st: list Z)
  | ExpectStreamStep (k: Z) (st: list Z) (c: Z) (a: list Z)
  | ExpectDecodeInit (a: list Z)
  | ExpectDecodeStep (k: Z) (a: list Z)
  | ExpectRecord (k: Z)
  | ExpectEntry (k b: Z) (a: list Z).

(* Calling again, with the model of memory m; or returned with the status st, leaving m. *)
Inductive progress : Type :=
  | Go (s: stage) (m: mem)
  | Return (st: Z) (m: mem).

(* The decoder. *)

(* Where boot_handoff_decode_projection's status st leads: on OK an allocation's boot_handoff_project checks the
   final state (decode-rejected), and a projection alone returns OK; otherwise the function returns st. *)
Definition projection_end (x: inputs) (st: Z) (m: mem) : progress :=
  if negb (st =? S_OK) then Return st m
  else match i_call x with
       | FAllocate => Return (rejected_check (current m)) m
       | _ => Return S_OK m
       end.

(* After the last chunk, or the transition that stopped the decoder, with its current state s: with a
   projection, decode-incomplete when s's error (word 2) is 0, then projection_end; for a candidate,
   authority-rejected. *)
Definition decode_done (x: inputs) (m: mem) : progress :=
  let s := current m in
  if projection x
  then projection_end x (if Znth 2 s =? 0 then incomplete_check (m_total m) s else S_OK) m
  else Return (authority_check x (m_total m) s) m.

(* Chunk k's transition, while 8k is below the extent; else the end. *)
Definition begin_transition (x: inputs) (k: Z) (m: mem) : progress :=
  if 8 * k <? m_total m then Go (ExpectDecodeStep k nil) m else decode_done x m.

(* After the four answers a of block b's projection of chunk k's entry event: the checks, then word b of the
   usable and blocked bitmaps is answers 3 and 4; then the next block, or after block 63 the next chunk. *)
Definition entry_done (x: inputs) (k b: Z) (a: list Z) (m: mem) : progress :=
  let st := entry_check a in
  if negb (st =? S_OK) then Return st m
  else
    let m := with_bitmaps m (upd_Znth b (m_usable m) (Znth 2 a)) (upd_Znth b (m_blocked m) (Znth 3 a))
                          (m_reserved m) in
    if b + 1 <? BLOCKS then Go (ExpectEntry k (b + 1) nil) m else begin_transition x (k + 1) m.

(* After the 41 answers a of chunk k's transition: they go to the other of the two states, which becomes the
   current one.  The decoder stops when its error (word 2) is not 0; with a projection, an entry event (word 19
   is 1) has its count checked and is then recorded; else the next chunk. *)
Definition decode_step_done (x: inputs) (k: Z) (a: list Z) (m: mem) : progress :=
  let n := 1 - m_at m in
  let m := with_states m (upd_Znth n (m_states m) a) n in
  if negb (Znth 2 a =? 0) then decode_done x m
  else if projection x && (Znth 19 a =? 1) then
    let st := event_check a in
    if st =? S_OK then Go (ExpectRecord k) m else Return st m
  else begin_transition x (k + 1) m.

(* After the 41 answers a of the decoder reset: they go to state 0, the current one; the checks; chunk 0. *)
Definition decode_init_done (x: inputs) (a: list Z) (m: mem) : progress :=
  let m := with_states m (upd_Znth 0 (m_states m) a) 0 in
  let st := decode_init_check x (m_total m) a in
  if st =? S_OK then begin_transition x 0 m else Return st m.

(* The decoder's turn: with a projection its bitmaps are zeroed first; then the reset. *)
Definition begin_decode (x: inputs) (m: mem) : progress :=
  Go (ExpectDecodeInit nil) (if projection x then with_bitmaps m zeros zeros zeros else m).

(* The copy. *)

(* Where boot_handoff_stream_copy's status st leads: on OK a copy alone returns OK and an allocation's decoder
   begins; otherwise the function returns st. *)
Definition copy_end (x: inputs) (st: Z) (m: mem) : progress :=
  if negb (st =? S_OK) then Return st m
  else match i_call x with
       | FCopy => Return S_OK m
       | _ => begin_decode x m
       end.

(* The stream accepted every chunk before chunk k, carrying the state st: read chunk k while 8k is below the
   extent; else the stream's final checks. *)
Definition begin_chunk (x: inputs) (k: Z) (st: list Z) (m: mem) : progress :=
  if 8 * k <? m_total m then Go (ExpectChunk k st) m else copy_end x (stream_final (m_total m) st) m.

(* After the nine answers a of chunk k's transition, the chunk c as read: the checks; then chunk k goes to word
   k of the copy, and the next chunk carries words 0..6 of a. *)
Definition stream_step_done (x: inputs) (k: Z) (c: Z) (a: list Z) (m: mem) : progress :=
  let st := stream_step_check x (m_total m) k c a in
  if st =? S_OK then begin_chunk x (k + 1) (sublist 0 7 a) (with_copy m (upd_Znth k (m_copy m) c))
  else Return st m.

(* After the seven answers a of the stream reset: the checks; then chunk 0, carrying a. *)
Definition stream_init_done (x: inputs) (a: list Z) (m: mem) : progress :=
  let st := stream_init_check x (m_total m) a in
  if st =? S_OK then begin_chunk x 0 a m else Return st m.

(* The extent. *)

(* After the size read, its low 32 bits T: the bounds, then the copy with T as the extent. *)
Definition size_done (x: inputs) (T: Z) (m: mem) : progress :=
  let st := bounds_check x T in
  if st =? S_OK then Go (ExpectStreamInit nil) (with_extent m T) else Return st m.

(* Before the first call: an allocation's magic and address checks, then its size read; a copy's stream reset;
   a decoder's begin. *)
Definition start (x: inputs) : progress :=
  match i_call x with
  | FAllocate =>
      let st := pointer_check x in
      if st =? S_OK then Go ExpectSize (initial x) else Return st (initial x)
  | FCopy => Go (ExpectStreamInit nil) (initial x)
  | FProjection | FCandidate => begin_decode x (initial x)
  end.

(* The call the header makes in stage s with memory m: the query word is the number of answers so far (word + 1
   for a block projection, whose words are 1..4). *)
Definition expected (x: inputs) (s: stage) (m: mem) : call :=
  let T := m_total m in
  match s with
  | ExpectSize => Read (i_address x)
  | ExpectStreamInit a => StreamInit (i_magic x) (i_address x) T (i_address x) (Zlength a)
  | ExpectChunk k _ => Read (i_address x + 8 * k)
  | ExpectStreamStep k st c a => StreamStep st (i_address x) (8 * k) 8 c (terminal T k) (Zlength a)
  | ExpectDecodeInit a => DecodeInit (i_magic x) (i_address x) T (target x) (Zlength a)
  | ExpectDecodeStep k a =>
      DecodeStep (current m) (i_address x) (8 * k) (Znth k (decoded x m)) (terminal T k) (Zlength a)
  | ExpectRecord _ =>
      let s := current m in Record (Znth 11 s - 1) (Znth 20 s) (Znth 21 s) (Znth 22 s)
  | ExpectEntry _ b a =>
      let s := current m in
      Entry (Znth 20 s) (Znth 21 s) (Znth 22 s) b (Znth b (m_usable m)) (Znth b (m_blocked m)) (Zlength a + 1)
  end.

(* One answer v in stage s with memory m. *)
Definition step (x: inputs) (s: stage) (m: mem) (v: Z) : progress :=
  match s with
  | ExpectSize => size_done x (v mod 2 ^ 32) m
  | ExpectStreamInit a =>
      let a := a ++ [v] in if Zlength a <? 7 then Go (ExpectStreamInit a) m else stream_init_done x a m
  | ExpectChunk k st => Go (ExpectStreamStep k st v nil) m
  | ExpectStreamStep k st c a =>
      let a := a ++ [v] in
      if Zlength a <? 9 then Go (ExpectStreamStep k st c a) m else stream_step_done x k c a m
  | ExpectDecodeInit a =>
      let a := a ++ [v] in if Zlength a <? WORDS then Go (ExpectDecodeInit a) m else decode_init_done x a m
  | ExpectDecodeStep k a =>
      let a := a ++ [v] in
      if Zlength a <? WORDS then Go (ExpectDecodeStep k a) m else decode_step_done x k a m
  | ExpectRecord k => Go (ExpectEntry k 0 nil) m
  | ExpectEntry k b a =>
      let a := a ++ [v] in if Zlength a <? 4 then Go (ExpectEntry k b a) m else entry_done x k b a m
  end.

(* The header after the answers h from progress p: Some (Go s m) while it would call again, Some (Return st m)
   when it returned after the last answer (or before any), None when h is not its sequence of calls. *)
Fixpoint run (x: inputs) (p: progress) (h: list answer) : option progress :=
  match h with
  | nil => Some p
  | (c, v) :: rest =>
    match p with
    | Go s m => if call_eq_dec c (expected x s m) then run x (step x s m v) rest else None
    | Return _ _ => None
    end
  end.

(* The call the header makes after the answers h, if it calls again. *)
Definition next_call (x: inputs) (h: list answer) : option call :=
  match run x (start x) h with Some (Go s m) => Some (expected x s m) | _ => None end.

(* The status and memory when the function main called returns after the answers h. *)
Definition returns (x: inputs) (h: list answer) : option (Z * mem) :=
  match run x (start x) h with Some (Return st m) => Some (st, m) | _ => None end.

(* ---------------------------------------------------------------------- *)
(* The outcome.                                                           *)
(* ---------------------------------------------------------------------- *)

(* The records after a return with status st and memory m, as main checks them: the extent once the bounds
   accept it (an allocation), the copy's length on a copy alone that returns OK, the state's index on OK for
   every call but a copy; each keeps its prior value otherwise. *)
Definition out_total_record (x: inputs) (m: mem) : Z :=
  if m_extent_ok m then m_total m else i_total_record x.
Definition out_length_record (x: inputs) (st: Z) (m: mem) : Z :=
  if is_copy x && (st =? S_OK) then m_total m else i_length_record x.
Definition out_current_record (x: inputs) (st: Z) (m: mem) : Z :=
  if negb (is_copy x) && (st =? S_OK) then m_at m else i_current_record x.

(* What a function leaves of the model's memory as it found it, from m0 to m: the extent (only the size read
   sets one), and what the function is not given: the bitmaps and the states for a copy alone, the copy for a
   decoder alone, and the bitmaps for a candidate too.  main compares these with the objects it did not pass. *)
Definition keeps (x: inputs) (m0 m: mem) : Prop :=
  m_total m = m_total m0 /\ m_extent_ok m = m_extent_ok m0 /\
  match i_call x with
  | FAllocate => True
  | FCopy =>
      m_usable m = m_usable m0 /\ m_blocked m = m_blocked m0 /\ m_reserved m = m_reserved m0 /\
      m_states m = m_states m0 /\ m_at m = m_at m0
  | FProjection => m_copy m = m_copy m0
  | FCandidate =>
      m_copy m = m_copy m0 /\ m_usable m = m_usable m0 /\ m_blocked m = m_blocked m0 /\
      m_reserved m = m_reserved m0
  end.

(* An allocation is two calls in main.  Where the first, boot_handoff_extent, leaves the model when it returns
   st, T being the extent it wrote on OK: at the stream reset with the extent T (after_extent), the second call's
   start; or returned with st, memory untouched. *)
Definition after_extent (x: inputs) (T: Z) : progress := Go (ExpectStreamInit nil) (with_extent (initial x) T).

Definition extent_end (x: inputs) (st T: Z) : progress :=
  if st =? S_OK then after_extent x T else Return st (initial x).

(* An extent a copy may take: a multiple of 8 up to 64 KiB (0 included). *)
Definition extent_fits (T: Z) : Prop := 0 <= T <= MAX_BYTES /\ T mod 8 = 0.

(* A status of enum boot_handoff_status. *)
Definition status_ok (st: Z) : Prop := 0 <= st <= S_AUTHORITY_REJECTED_TARGET.

(* ---------------------------------------------------------------------- *)
(* How the machine moves (for the body proofs and the law's oracle).      *)
(* ---------------------------------------------------------------------- *)

Lemma run_app (x: inputs) (p: progress) (h1 h2: list answer) :
  run x p (h1 ++ h2) = match run x p h1 with Some q => run x q h2 | None => None end.
Proof.
  revert p; induction h1 as [| [c v] rest IH]; intros p; simpl; [reflexivity |].
  destruct p as [s m | st m]; [| reflexivity].
  destruct (call_eq_dec c (expected x s m)); [apply IH | reflexivity].
Qed.

(* Answering the expected call of stage s with v moves to step x s m v. *)
Lemma run_snoc (x: inputs) (p: progress) (h: list answer) (s: stage) (m: mem) (v: Z) :
  run x p h = Some (Go s m) -> run x p (h ++ [(expected x s m, v)]) = Some (step x s m v).
Proof.
  intros E. rewrite run_app, E. simpl.
  destruct (call_eq_dec (expected x s m) (expected x s m)); [reflexivity | contradiction].
Qed.

Lemma next_call_go (x: inputs) (h: list answer) (s: stage) (m: mem) :
  run x (start x) h = Some (Go s m) -> next_call x h = Some (expected x s m).
Proof. unfold next_call. intros E. rewrite E. reflexivity. Qed.

Lemma next_call_run (x: inputs) (h: list answer) (c: call) :
  next_call x h = Some c -> exists s m, run x (start x) h = Some (Go s m) /\ c = expected x s m.
Proof.
  unfold next_call. intros H.
  destruct (run x (start x) h) as [[s m | st m] | ]; inversion H; eauto.
Qed.

Lemma returns_return (x: inputs) (h: list answer) (st: Z) (m: mem) :
  run x (start x) h = Some (Return st m) -> returns x h = Some (st, m).
Proof. unfold returns. intros E. rewrite E. reflexivity. Qed.

Lemma returns_run (x: inputs) (h: list answer) (st: Z) (m: mem) :
  returns x h = Some (st, m) -> run x (start x) h = Some (Return st m).
Proof.
  unfold returns. intros H.
  destruct (run x (start x) h) as [[s m' | st' m'] | ]; inversion H; subst; reflexivity.
Qed.

(* The model's returns other than through the phase ends are failures: each phase end returns its status. *)
Lemma copy_end_fail (x: inputs) (st: Z) (m: mem) : st <> S_OK -> copy_end x st m = Return st m.
Proof. intros. unfold copy_end. rewrite (proj2 (Z.eqb_neq st S_OK) H). reflexivity. Qed.

Lemma projection_end_fail (x: inputs) (st: Z) (m: mem) : st <> S_OK -> projection_end x st m = Return st m.
Proof. intros. unfold projection_end. rewrite (proj2 (Z.eqb_neq st S_OK) H). reflexivity. Qed.
