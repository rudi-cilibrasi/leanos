(* Pure definitions shared by every proof of leanos_frame_selection (include/boot_frame_selection.h, through the
   wrapper unit patch/frame_unit.c): each of the seven steps main may call (frame_terminal, frame_select,
   frame_cross_check, frame_scrub_selected, frame_publication_result, frame_publication_check, frame_rescan) as a
   state machine over the answers of the header's callees: the candidate decoder and the scrub, which it is given
   as function pointers, and the six Lean exports.  No program here.

   One step is one machine.  Its inputs (`inputs`) are the step, its scalar arguments, the four objects no step
   writes (the manifest, the decoded state, the usable and blocked bitmaps) and the memory before the step
   (i_mem: every object some step writes).  The law's main composes the steps of boot_allocate's sequence: each
   step starts from the memory the previous one returned, with the selection's records as the later steps'
   frame arguments (allocate_next).  main's own record of the sequence (law.call, and law.scrubbed: the scrub
   answered 1, which the publication result's export checks in the sequence) is the law's, not a step's.

   The model follows the first comment of harness/frame_selection_exact.c (the law's claim) clause by clause, and
   its stages are the law's `expect` with its counters (harness/frame_selection_exact.h):

     stage                         law
     ExpectManifest b ms me fw a   EXPECT_MANIFEST, step TERMINAL, block = b, word = |a| + 1, answer[1..|a|] = a,
                                   manifest_status = ms, manifest_error = me, free_words[0 .. b) = fw
     ExpectFree b ms me fw         EXPECT_FREE, block = b, the rest as above (the mask: reserved_expect[b])
     ExpectFinish q ms me fw       EXPECT_FINISH, word = q, the rest as above (|fw| = 64)
     ExpectDecode c k f fm         EXPECT_DECODE, step SELECT, candidate = c, scan = k, first = f,
                                   first_manifest = fm, second = 4096
     ExpectCandidate c k f fm      EXPECT_CANDIDATE, step SELECT, likewise
     ExpectConsume c k f fm cm     EXPECT_CONSUME, likewise, candidate_manifest = cm
     ExpectScrub                   EXPECT_SCRUB
     ExpectAuthority q             EXPECT_AUTHORITY, word = q
     ExpectRescanDecode            EXPECT_DECODE, step RESCAN, candidate = next, scan = 1
     ExpectRescanCandidate         EXPECT_CANDIDATE, step RESCAN, candidate = next, scan = 1
     Return st m                   EXPECT_NOTHING, verdict = st

   and the model's mem is the law's model of memory: reserved_expect, terminal_expect, states_expect,
   publication_expect, rescan_expect, selected_expect, manifest_expect, next_expect and decoder_expect.  So each
   callee of the harness moves the law's record exactly as `step` moves the model, each begin_* of main is `start`,
   and check_step's comparisons read the model's outcome (`returns`).

   What the calls and the status depend on: the answers and the scalar inputs (take_next and the frame arguments),
   and where the C reads memory, the model reads its own:
   - the free word's mask is the reserved word the overlay just wrote;
   - the terminal checks read the terminal words the finish just wrote;
   - the consumer's status, usable and blocked arguments are words of the state the decoder just wrote;
   - the cross-check reads the terminal result and state 0, the publication result state 0, the publication check
     the publication result, and the rescan state 1 as its decoder just wrote it.
   The objects no step writes are inputs: the manifest, the decoded state (its words 1, 2, 11 and 17) and the
   usable and blocked bitmaps.

   Words are Z values in their C type's range (inputs_ok, mem_ok): uint64_t, and uint32_t for take_next, the
   decoder's status and record and the scrub's answer.  The C's integer details:
   - the decoder's status (`uint32_t status = decode(...)`) and the scrub's answer (`!= 1`) are uint32_t: the
     callbacks answer 32-bit values (FrameSpecs.decode_spec, scrub_spec);
   - the selection's scan is the uint32_t 0 or 1, and `take_next == 0` compares a uint32_t;
   - the published object `selected + 1` is uint64_t: it wraps to 0 at 2^64 - 1 (publication_check);
   - every other comparison (`next <= published` among them) is of uint64_t words, as the model's Z. *)
Require Import VST.floyd.proofauto.
Local Open Scope Z_scope.
Local Open Scope bool_scope.   (* && and || are andb and orb here, not VST's andp and orp *)

(* ---------------------------------------------------------------------- *)
(* The statuses and the constants.                                        *)
(* ---------------------------------------------------------------------- *)

(* enum boot_frame_status, in order: the statuses of the header without the prefix BOOT_FRAME_. *)
Definition S_OK : Z := 0.
Definition S_TERMINAL_VERSION : Z := 1.
Definition S_TERMINAL_STATUS : Z := 2.
Definition S_TERMINAL_ERROR : Z := 3.
Definition S_TERMINAL_FRAME : Z := 4.
Definition S_TERMINAL_OWNER : Z := 5.
Definition S_TERMINAL_ENTRY_COUNT : Z := 6.
Definition S_DECODER : Z := 7.
Definition S_AUTHORITY_NONE : Z := 8.
Definition S_AUTHORITY_NOMINATION : Z := 9.
Definition S_AUTHORITY_TARGET : Z := 10.
Definition S_AUTHORITY_ENTRY_COUNT : Z := 11.
Definition S_AUTHORITY_HIGHEST : Z := 12.
Definition S_AUTHORITY_USABLE : Z := 13.
Definition S_AUTHORITY_BLOCKED : Z := 14.
Definition S_AUTHORITY_MANIFEST : Z := 15.
Definition S_SCRUB : Z := 16.
Definition S_PUBLICATION_VERSION : Z := 17.
Definition S_PUBLICATION_STATUS : Z := 18.
Definition S_PUBLICATION_ERROR : Z := 19.
Definition S_PUBLICATION_FRAME : Z := 20.
Definition S_PUBLICATION_OBJECT : Z := 21.
Definition S_UNPUBLISHED_LIMIT : Z := 22.
Definition S_UNPUBLISHED_ORDER : Z := 23.
Definition S_RESCAN_ENTRY_COUNT : Z := 24.
Definition S_RESCAN_HIGHEST : Z := 25.
Definition S_RESCAN_TARGET : Z := 26.
Definition S_RESCAN_STATUS : Z := 27.
Definition S_RESCAN_USABLE : Z := 28.
Definition S_RESCAN_BLOCKED : Z := 29.
Definition S_RESCAN_MANIFEST : Z := 30.

(* The header's constants, as notations so that lia and the list tactics see the numbers. *)
Notation FRAMES := 4096%Z (only parsing).          (* BOOT_FRAME_COUNT: the candidates, and "no frame" *)
Notation BLOCKS := 64%Z (only parsing).            (* BOOT_FRAME_BLOCKS: a bitmap's words *)
Notation WORDS := 41%Z (only parsing).             (* BOOT_FRAME_DECODE_WORDS: a decoder state's words *)
Notation MANIFEST_WORDS := 18%Z (only parsing).    (* BOOT_FRAME_MANIFEST_WORDS *)
Notation TERMINAL_WORDS := 9%Z (only parsing).     (* BOOT_FRAME_TERMINAL_WORDS *)
Notation PUBLICATION_WORDS := 5%Z (only parsing).  (* BOOT_FRAME_PUBLICATION_WORDS *)
Notation RESCAN_WORDS := 5%Z (only parsing).       (* BOOT_FRAME_RESCAN_WORDS *)

Definition u64_ok (v: Z) : Prop := 0 <= v <= Int64.max_unsigned.
Definition u32_ok (v: Z) : Prop := 0 <= v <= Int.max_unsigned.

(* A status of enum boot_frame_status. *)
Definition status_ok (st: Z) : Prop := 0 <= st <= S_RESCAN_MANIFEST.

(* ---------------------------------------------------------------------- *)
(* The memory and the inputs.                                             *)
(* ---------------------------------------------------------------------- *)

(* What the steps write, as the law keeps it (struct law's *_expect): the reserved bitmap (64 words), the terminal
   result (9), the two decoder states (2 x 41: state 0 and state 1), the publication result (5), the rescan's
   record (5), the selection's three uint64_t records (the selected frame, its manifest answer, the next frame) and
   the uint32_t decoder record. *)
Record mem : Type := mk_mem {
  m_reserved: list Z; m_terminal: list Z; m_states: list (list Z); m_publication: list Z; m_rescan: list Z;
  m_selected: Z; m_selected_manifest: Z; m_next: Z; m_decoder: Z }.

Definition with_reserved (m: mem) (r: list Z) : mem :=
  mk_mem r (m_terminal m) (m_states m) (m_publication m) (m_rescan m)
         (m_selected m) (m_selected_manifest m) (m_next m) (m_decoder m).
Definition with_terminal (m: mem) (t: list Z) : mem :=
  mk_mem (m_reserved m) t (m_states m) (m_publication m) (m_rescan m)
         (m_selected m) (m_selected_manifest m) (m_next m) (m_decoder m).
Definition with_states (m: mem) (ss: list (list Z)) : mem :=
  mk_mem (m_reserved m) (m_terminal m) ss (m_publication m) (m_rescan m)
         (m_selected m) (m_selected_manifest m) (m_next m) (m_decoder m).
Definition with_publication (m: mem) (p: list Z) : mem :=
  mk_mem (m_reserved m) (m_terminal m) (m_states m) p (m_rescan m)
         (m_selected m) (m_selected_manifest m) (m_next m) (m_decoder m).
Definition with_rescan (m: mem) (r: list Z) : mem :=
  mk_mem (m_reserved m) (m_terminal m) (m_states m) (m_publication m) r
         (m_selected m) (m_selected_manifest m) (m_next m) (m_decoder m).
(* The selection's records: the selected frame s, its manifest answer sm, the next frame n. *)
Definition with_records (m: mem) (s sm n: Z) : mem :=
  mk_mem (m_reserved m) (m_terminal m) (m_states m) (m_publication m) (m_rescan m) s sm n (m_decoder m).
Definition with_decoder (m: mem) (d: Z) : mem :=
  mk_mem (m_reserved m) (m_terminal m) (m_states m) (m_publication m) (m_rescan m)
         (m_selected m) (m_selected_manifest m) (m_next m) d.

(* State k (0 or 1) is ws. *)
Definition with_state (m: mem) (k: Z) (ws: list Z) : mem := with_states m (upd_Znth k (m_states m) ws).

(* The step main calls (law.step, STEP_TERMINAL .. STEP_RESCAN): frame_terminal, frame_select,
   frame_cross_check, frame_scrub_selected, frame_publication_result, frame_publication_check, frame_rescan. *)
Inductive func : Type :=
  FTerminal | FSelect | FCrossCheck | FScrub | FPublicationResult | FPublicationCheck | FRescan.

(* A step's inputs: the step; take_next (the selection's, uint32_t); the frame arguments: the selected frame and
   its manifest answer (the cross-check, the scrub and the publication), the published and the next frame (the
   rescan); the objects no step writes: the manifest (18 words), the projection decoder's final state (41) and the
   usable and blocked bitmaps (64 each); and the memory before the step. *)
Record inputs : Type := mk_inputs {
  i_step: func;
  i_take_next: Z; i_selected: Z; i_selected_manifest: Z; i_published: Z; i_next: Z;
  i_manifest: list Z; i_decoded: list Z; i_usable: list Z; i_blocked: list Z;
  i_mem: mem }.

(* The next step of main, from memory m, with the same scalar arguments. *)
Definition with_step (x: inputs) (f: func) (m: mem) : inputs :=
  mk_inputs f (i_take_next x) (i_selected x) (i_selected_manifest x) (i_published x) (i_next x)
            (i_manifest x) (i_decoded x) (i_usable x) (i_blocked x) m.

(* boot_allocate's sequence passes the selection's records on (main, after frame_select): the selected frame and
   its manifest answer to the cross-check, the scrub and the publication, the selected frame as the published one
   and the next frame to the rescan. *)
Definition after_select (x: inputs) (m: mem) : inputs :=
  mk_inputs (i_step x) (i_take_next x) (m_selected m) (m_selected_manifest m) (m_selected m) (m_next m)
            (i_manifest x) (i_decoded x) (i_usable x) (i_blocked x) (i_mem x).

(* boot_allocate's sequence (main's CALL_ALLOCATE): the step after a step of inputs x that returned OK with
   memory m, if there is one: the terminal, the selection, the cross-check, the scrub, the publication result,
   the publication check and, with take_next nonzero, the rescan, each from the memory the step before returned,
   the selection's records passed on. *)
Definition allocate_next (x: inputs) (m: mem) : option inputs :=
  match i_step x with
  | FTerminal => Some (with_step x FSelect m)
  | FSelect => Some (after_select (with_step x FCrossCheck m) m)
  | FCrossCheck => Some (with_step x FScrub m)
  | FScrub => Some (with_step x FPublicationResult m)
  | FPublicationResult => Some (with_step x FPublicationCheck m)
  | FPublicationCheck => if i_take_next x =? 0 then None else Some (with_step x FRescan m)
  | FRescan => None
  end.

(* The memory of the model: objects of their sizes holding words; the states 64-bit words, the decoder record a
   32-bit one. *)
Definition mem_ok (m: mem) : Prop :=
  Zlength (m_reserved m) = BLOCKS /\ Forall u64_ok (m_reserved m) /\
  Zlength (m_terminal m) = TERMINAL_WORDS /\ Forall u64_ok (m_terminal m) /\
  Zlength (m_states m) = 2 /\ Forall (fun s => Zlength s = WORDS /\ Forall u64_ok s) (m_states m) /\
  Zlength (m_publication m) = PUBLICATION_WORDS /\ Forall u64_ok (m_publication m) /\
  Zlength (m_rescan m) = RESCAN_WORDS /\ Forall u64_ok (m_rescan m) /\
  u64_ok (m_selected m) /\ u64_ok (m_selected_manifest m) /\ u64_ok (m_next m) /\ u32_ok (m_decoder m).

(* The inputs main may choose: a 32-bit take_next, 64-bit frames, the read-only objects of their sizes holding
   64-bit words, and such a memory. *)
Definition inputs_ok (x: inputs) : Prop :=
  u32_ok (i_take_next x) /\ u64_ok (i_selected x) /\ u64_ok (i_selected_manifest x) /\
  u64_ok (i_published x) /\ u64_ok (i_next x) /\
  Zlength (i_manifest x) = MANIFEST_WORDS /\ Forall u64_ok (i_manifest x) /\
  Zlength (i_decoded x) = WORDS /\ Forall u64_ok (i_decoded x) /\
  Zlength (i_usable x) = BLOCKS /\ Forall u64_ok (i_usable x) /\
  Zlength (i_blocked x) = BLOCKS /\ Forall u64_ok (i_blocked x) /\
  mem_ok (i_mem x).

(* ---------------------------------------------------------------------- *)
(* Calls and answers.                                                     *)
(* ---------------------------------------------------------------------- *)

(* A call of the header to one of its callees, with its arguments. *)
Inductive call : Type :=
  (* leanos_boot_projection_manifest(block, m0, ..., m17, query): the 18 words of the manifest ms *)
  | Manifest (block: Z) (ms: list Z) (query: Z)
  (* leanos_boot_projection_free(usable, blocked, reserved) *)
  | Free (usable blocked reserved: Z)
  (* leanos_boot_projection_finish(decode_status, decode_error, manifest_status, manifest_error, entry_count,
     highest, owner, query, w0, ..., w63): the 64 free words fw *)
  | Finish (decode_status decode_error manifest_status manifest_error entry_count highest owner query: Z)
           (fw: list Z)
  (* decode(context, candidate, states[k]): the decoder writes state k *)
  | Decode (candidate k: Z)
  (* leanos_boot_manifest_candidate(frame, m0, ..., m17) *)
  | Candidate (frame: Z) (ms: list Z)
  (* leanos_boot_consume_exact_projection(current, candidate, decode_status, usable, blocked, manifest) *)
  | Consume (current candidate decode_status usable blocked manifest: Z)
  (* scrub(context, frame) *)
  | Scrub (frame: Z)
  (* leanos_boot_authority_result(selected, rescanned, status, usable, blocked, manifest, scrubbed, query) *)
  | Authority (selected rescanned status usable blocked manifest scrubbed query: Z).

(* A callee's answer: a word (the exports' uint64_t, the scrub's uint32_t), or the decoder's uint32_t status with
   the 41 words it wrote to the state it was given. *)
Inductive reply : Type :=
  | Word (v: Z)
  | Decoded (status: Z) (ws: list Z).

Definition reply_value (r: reply) : Z := match r with Word v => v | Decoded st _ => st end.
Definition reply_state (r: reply) : list Z := match r with Word _ => nil | Decoded _ ws => ws end.

(* The decoder answers Decoded, every other callee a Word. *)
Definition fits (c: call) (r: reply) : bool :=
  match c, r with
  | Decode _ _, Decoded _ _ => true
  | Decode _ _, Word _ => false
  | _, Word _ => true
  | _, Decoded _ _ => false
  end.

(* What each callee may answer (their specifications' postconditions): the decoder a 32-bit status and 41
   64-bit words, the scrub a 32-bit word, each export a 64-bit word. *)
Definition reply_ok (c: call) (r: reply) : Prop :=
  match c, r with
  | Decode _ _, Decoded st ws => u32_ok st /\ Zlength ws = WORDS /\ Forall u64_ok ws
  | Scrub _, Word v => u32_ok v
  | Decode _ _, Word _ => False
  | _, Word v => u64_ok v
  | _, Decoded _ _ => False
  end.

(* One answered call. *)
Definition answer : Type := (call * reply)%type.

Definition answers_ok (h: list answer) : Prop := Forall (fun a => reply_ok (fst a) (snd a)) h.

Definition call_eq_dec (a b: call) : {a = b} + {a <> b}.
Proof. decide equality; first [ apply Z.eq_dec | apply (list_eq_dec Z.eq_dec) ]. Defined.

(* ---------------------------------------------------------------------- *)
(* The checks, each the first status that applies, or OK.                 *)
(* ---------------------------------------------------------------------- *)

(* boot_frame_terminal after its finish: terminal words 0..5 (the memory's), against the decoded state's entry
   count (word 11). *)
Definition terminal_check (x: inputs) (m: mem) : Z :=
  let t := m_terminal m in
  if negb (Znth 0 t =? 1) then S_TERMINAL_VERSION
  else if negb (Znth 1 t =? 1) then S_TERMINAL_STATUS
  else if negb (Znth 2 t =? 0) then S_TERMINAL_ERROR
  else if FRAMES <=? Znth 3 t then S_TERMINAL_FRAME
  else if negb (Znth 4 t =? 1) then S_TERMINAL_OWNER
  else if negb (Znth 5 t =? Znth 11 (i_decoded x)) then S_TERMINAL_ENTRY_COUNT
  else S_OK.

(* boot_frame_cross_check of the frame S and its manifest answer A (the inputs'), with the terminal result and
   state 0 of memory. *)
Definition cross_check (x: inputs) (m: mem) : Z :=
  let S := i_selected x in let s := Znth 0 (m_states m) in let d := i_decoded x in
  if FRAMES <=? S then S_AUTHORITY_NONE
  else if negb (Znth 3 (m_terminal m) =? S) then S_AUTHORITY_NOMINATION
  else if negb (Znth 16 s =? S) then S_AUTHORITY_TARGET
  else if negb (Znth 11 s =? Znth 11 d) then S_AUTHORITY_ENTRY_COUNT
  else if negb (Znth 17 s =? Znth 17 d) then S_AUTHORITY_HIGHEST
  else if negb (Znth 14 s =? 1) then S_AUTHORITY_USABLE
  else if negb (Znth 15 s =? 0) then S_AUTHORITY_BLOCKED
  else if negb (i_selected_manifest x =? 1) then S_AUTHORITY_MANIFEST
  else S_OK.

(* boot_frame_publication_check of the frame S, with the publication result of memory: word 4 must be S + 1 in
   uint64_t. *)
Definition publication_check (x: inputs) (m: mem) : Z :=
  let S := i_selected x in let p := m_publication m in
  if negb (Znth 0 p =? 1) then S_PUBLICATION_VERSION
  else if negb (Znth 1 p =? 1) then S_PUBLICATION_STATUS
  else if negb (Znth 2 p =? 0) then S_PUBLICATION_ERROR
  else if negb (Znth 3 p =? S) then S_PUBLICATION_FRAME
  else if negb (Znth 4 p =? (S + 1) mod 2 ^ 64) then S_PUBLICATION_OBJECT
  else S_OK.

(* boot_frame_rescan before its decoder: the next frame N below 4096 and above the published frame P. *)
Definition rescan_order (x: inputs) : Z :=
  if FRAMES <=? i_next x then S_UNPUBLISHED_LIMIT
  else if i_next x <=? i_published x then S_UNPUBLISHED_ORDER
  else S_OK.

(* boot_frame_rescan after the manifest's answer v for N, with state 1 as its decoder wrote it (s). *)
Definition rescan_check (x: inputs) (s: list Z) (v: Z) : Z :=
  let d := i_decoded x in
  if negb (Znth 11 s =? Znth 11 d) then S_RESCAN_ENTRY_COUNT
  else if negb (Znth 17 s =? Znth 17 d) then S_RESCAN_HIGHEST
  else if negb (Znth 16 s =? i_next x) then S_RESCAN_TARGET
  else if negb (Znth 1 s =? 1) then S_RESCAN_STATUS
  else if negb (Znth 14 s =? 1) then S_RESCAN_USABLE
  else if negb (Znth 15 s =? 0) then S_RESCAN_BLOCKED
  else if negb (v =? 1) then S_RESCAN_MANIFEST
  else S_OK.

(* ---------------------------------------------------------------------- *)
(* The machine.                                                           *)
(* ---------------------------------------------------------------------- *)

(* Where the step is between calls (the law's `expect` with its counters; see the table above).  b is a block,
   ms and me the overlay's status and error so far, fw the free words answered so far, a the current block's
   overlay answers so far (to words 1, 2); q a query word; c a candidate, k the state it is decoded into (the
   scan), f and fm the selected frame and its manifest answer so far (4096 and 0 before one is selected), cm the
   current candidate's manifest answer. *)
Inductive stage : Type :=
  | ExpectManifest (b ms me: Z) (fw a: list Z)
  | ExpectFree (b ms me: Z) (fw: list Z)
  | ExpectFinish (q ms me: Z) (fw: list Z)
  | ExpectDecode (c k f fm: Z)
  | ExpectCandidate (c k f fm: Z)
  | ExpectConsume (c k f fm cm: Z)
  | ExpectScrub
  | ExpectAuthority (q: Z)
  | ExpectRescanDecode
  | ExpectRescanCandidate.

(* Calling again, with the model of memory m; or returned with the status st, leaving m. *)
Inductive progress : Type :=
  | Go (s: stage) (m: mem)
  | Return (st: Z) (m: mem).

(* The terminal. *)

(* After block b's three overlay answers (status st, error er, mask): the overlay's status and error become st
   and er when they are not 1 and 0; word b of the reserved bitmap is the mask; then the block's free word. *)
Definition overlay_done (b ms me: Z) (fw: list Z) (st er mask: Z) (m: mem) : progress :=
  let bad := negb (st =? 1) || negb (er =? 0) in
  Go (ExpectFree b (if bad then st else ms) (if bad then er else me) fw)
     (with_reserved m (upd_Znth b (m_reserved m) mask)).

(* After block b's free word: the next block, or after block 63 the terminal result's word 0. *)
Definition free_done (b ms me: Z) (fw: list Z) (m: mem) : progress :=
  if b + 1 <? BLOCKS then Go (ExpectManifest (b + 1) ms me fw nil) m else Go (ExpectFinish 0 ms me fw) m.

(* After the terminal result's word q, written to memory: the next word, or after word 8 the checks. *)
Definition finish_done (x: inputs) (q ms me: Z) (fw: list Z) (m: mem) : progress :=
  if q + 1 <? TERMINAL_WORDS then Go (ExpectFinish (q + 1) ms me fw) m else Return (terminal_check x m) m.

(* The selection. *)

(* The scan ended: OK, with the selected frame f, its manifest answer fm and the next frame n in the records. *)
Definition select_done (f fm n: Z) (m: mem) : progress := Return S_OK (with_records m f fm n).

(* The candidate after c into state k, or after candidate 4095 the end of the scan (no next frame). *)
Definition next_candidate (c k f fm: Z) (m: mem) : progress :=
  if c + 1 <? FRAMES then Go (ExpectDecode (c + 1) k f fm) m else select_done f fm FRAMES m.

(* After the consumer's answer v for candidate c (its manifest answer cm): below 4096 it accepts c; the first
   accepted is the selected frame, and the scan stops there with take_next 0, or goes on into state 1; the
   second accepted is the next frame, and the scan stops. *)
Definition consume_done (x: inputs) (c k f fm cm v: Z) (m: mem) : progress :=
  if FRAMES <=? v then next_candidate c k f fm m
  else if k =? 0 then
    (if i_take_next x =? 0 then select_done v cm FRAMES m else next_candidate c 1 v cm m)
  else select_done f fm v m.

(* The decoder's answer (status st, words ws) into state k: the state is ws whatever the status; a status other
   than 0 returns DECODER, writing it to the decoder record; else go on to g. *)
Definition decode_done (k st: Z) (ws: list Z) (g: stage) (m: mem) : progress :=
  let m := with_state m k ws in
  if st =? 0 then Go g m else Return S_DECODER (with_decoder m st).

(* The rescan: after the manifest's answer v for the next frame, the checks on state 1; on OK the record is its
   target frame, status, usable and blocked words and v. *)
Definition rescan_done (x: inputs) (v: Z) (m: mem) : progress :=
  let s := Znth 1 (m_states m) in
  let st := rescan_check x s v in
  if st =? S_OK then Return S_OK (with_rescan m [Znth 16 s; Znth 1 s; Znth 14 s; Znth 15 s; v]) else Return st m.

(* The publication result: after word q, written to memory, the next word, or after word 4 OK. *)
Definition authority_done (q: Z) (m: mem) : progress :=
  if q + 1 <? PUBLICATION_WORDS then Go (ExpectAuthority (q + 1)) m else Return S_OK m.

(* Before the first call (main's begin_ functions): a step's first expected call, or the verdict of a step that makes
   none (the cross-check, the publication check, the rescan's order checks). *)
Definition start (x: inputs) : progress :=
  let m := i_mem x in
  match i_step x with
  | FTerminal => Go (ExpectManifest 0 1 0 nil nil) m
  | FSelect => Go (ExpectDecode 0 0 FRAMES 0) m
  | FCrossCheck => Return (cross_check x m) m
  | FScrub => Go ExpectScrub m
  | FPublicationResult => Go (ExpectAuthority 0) m
  | FPublicationCheck => Return (publication_check x m) m
  | FRescan => let st := rescan_order x in if st =? S_OK then Go ExpectRescanDecode m else Return st m
  end.

(* The call the step makes in stage s with memory m. *)
Definition expected (x: inputs) (s: stage) (m: mem) : call :=
  match s with
  | ExpectManifest b _ _ _ a => Manifest b (i_manifest x) (Zlength a + 1)
  | ExpectFree b _ _ _ => Free (Znth b (i_usable x)) (Znth b (i_blocked x)) (Znth b (m_reserved m))
  | ExpectFinish q ms me fw =>
      let d := i_decoded x in Finish (Znth 1 d) (Znth 2 d) ms me (Znth 11 d) (Znth 17 d) 1 q fw
  | ExpectDecode c k _ _ => Decode c k
  | ExpectCandidate c _ _ _ => Candidate c (i_manifest x)
  | ExpectConsume c k _ _ cm =>
      let s := Znth k (m_states m) in Consume FRAMES c (Znth 1 s) (Znth 14 s) (Znth 15 s) cm
  | ExpectScrub => Scrub (i_selected x)
  | ExpectAuthority q =>
      let s := Znth 0 (m_states m) in
      Authority (i_selected x) (Znth 16 s) (Znth 1 s) (Znth 14 s) (Znth 15 s) (i_selected_manifest x) 1 q
  | ExpectRescanDecode => Decode (i_next x) 1
  | ExpectRescanCandidate => Candidate (i_next x) (i_manifest x)
  end.

(* One answer r in stage s with memory m. *)
Definition step (x: inputs) (s: stage) (m: mem) (r: reply) : progress :=
  let v := reply_value r in
  match s with
  | ExpectManifest b ms me fw a =>
      if Zlength a <? 2 then Go (ExpectManifest b ms me fw (a ++ [v])) m
      else overlay_done b ms me fw (Znth 0 a) (Znth 1 a) v m
  | ExpectFree b ms me fw => free_done b ms me (fw ++ [v]) m
  | ExpectFinish q ms me fw => finish_done x q ms me fw (with_terminal m (upd_Znth q (m_terminal m) v))
  | ExpectDecode c k f fm => decode_done k v (reply_state r) (ExpectCandidate c k f fm) m
  | ExpectCandidate c k f fm => Go (ExpectConsume c k f fm v) m
  | ExpectConsume c k f fm cm => consume_done x c k f fm cm v m
  | ExpectScrub => Return (if v =? 1 then S_OK else S_SCRUB) m
  | ExpectAuthority q => authority_done q (with_publication m (upd_Znth q (m_publication m) v))
  | ExpectRescanDecode => decode_done 1 v (reply_state r) ExpectRescanCandidate m
  | ExpectRescanCandidate => rescan_done x v m
  end.

(* The step after the answers h from progress p: Some (Go s m) while it would call again, Some (Return st m)
   when it returned after the last answer (or before any), None when h is not its sequence of calls. *)
Fixpoint run (x: inputs) (p: progress) (h: list answer) : option progress :=
  match h with
  | nil => Some p
  | (c, r) :: rest =>
    match p with
    | Go s m => if call_eq_dec c (expected x s m) then (if fits c r then run x (step x s m r) rest else None)
                else None
    | Return _ _ => None
    end
  end.

(* The call the step makes after the answers h, if it calls again. *)
Definition next_call (x: inputs) (h: list answer) : option call :=
  match run x (start x) h with Some (Go s m) => Some (expected x s m) | _ => None end.

(* The status and memory when the step returns after the answers h. *)
Definition returns (x: inputs) (h: list answer) : option (Z * mem) :=
  match run x (start x) h with Some (Return st m) => Some (st, m) | _ => None end.

(* ---------------------------------------------------------------------- *)
(* What a step writes.                                                    *)
(* ---------------------------------------------------------------------- *)

(* The memory m0 with the objects step f writes taken from m: the terminal writes the reserved bitmap and the
   terminal result; the selection the two states and the four records; the publication result its five words;
   the rescan state 1, its record and the decoder record; the cross-check, the scrub and the publication check
   nothing. *)
Definition written (f: func) (m0 m: mem) : mem :=
  match f with
  | FTerminal => with_terminal (with_reserved m0 (m_reserved m)) (m_terminal m)
  | FSelect =>
      with_decoder (with_records (with_states m0 (m_states m)) (m_selected m) (m_selected_manifest m) (m_next m))
                   (m_decoder m)
  | FCrossCheck | FScrub | FPublicationCheck => m0
  | FPublicationResult => with_publication m0 (m_publication m)
  | FRescan =>
      with_decoder (with_rescan (with_state m0 1 (Znth 1 (m_states m))) (m_rescan m)) (m_decoder m)
  end.

(* m differs from the memory before the step only in what the step writes.  main compares the objects it did not
   pass to the step too: they keep their contents. *)
Definition keeps (x: inputs) (m: mem) : Prop := m = written (i_step x) (i_mem x) m.

(* ---------------------------------------------------------------------- *)
(* How the machine moves (for the body proofs and the law's oracle).      *)
(* ---------------------------------------------------------------------- *)

Lemma run_app (x: inputs) (p: progress) (h1 h2: list answer) :
  run x p (h1 ++ h2) = match run x p h1 with Some q => run x q h2 | None => None end.
Proof.
  revert p; induction h1 as [| [c r] rest IH]; intros p; simpl; [reflexivity |].
  destruct p as [s m | st m]; [| reflexivity].
  destruct (call_eq_dec c (expected x s m)); [| reflexivity].
  destruct (fits c r); [apply IH | reflexivity].
Qed.

(* Answering the expected call of stage s with r (of the call's kind) moves to step x s m r. *)
Lemma run_snoc (x: inputs) (p: progress) (h: list answer) (s: stage) (m: mem) (r: reply) :
  run x p h = Some (Go s m) -> fits (expected x s m) r = true ->
  run x p (h ++ [(expected x s m, r)]) = Some (step x s m r).
Proof.
  intros E F. rewrite run_app, E. simpl.
  destruct (call_eq_dec (expected x s m) (expected x s m)); [| contradiction].
  rewrite F. reflexivity.
Qed.

(* The same for a word answer to an export or the scrub, and for the decoder's answer. *)
Lemma run_word (x: inputs) (p: progress) (h: list answer) (s: stage) (m: mem) (v: Z) :
  run x p h = Some (Go s m) -> (forall c k, expected x s m <> Decode c k) ->
  run x p (h ++ [(expected x s m, Word v)]) = Some (step x s m (Word v)).
Proof.
  intros E N. apply run_snoc; [exact E |].
  destruct (expected x s m) eqn:Q; try reflexivity. exfalso. eapply N. reflexivity.
Qed.

Lemma run_decoded (x: inputs) (p: progress) (h: list answer) (s: stage) (m: mem) (c k st: Z) (ws: list Z) :
  run x p h = Some (Go s m) -> expected x s m = Decode c k ->
  run x p (h ++ [(Decode c k, Decoded st ws)]) = Some (step x s m (Decoded st ws)).
Proof. intros E Q. rewrite <- Q. apply run_snoc; [exact E | rewrite Q; reflexivity]. Qed.

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

(* ---------------------------------------------------------------------- *)
(* What every return gives: a status, a memory of the model, what is kept. *)
(* ---------------------------------------------------------------------- *)

(* The step a stage belongs to. *)
Definition stage_step (s: stage) : func :=
  match s with
  | ExpectManifest _ _ _ _ _ | ExpectFree _ _ _ _ | ExpectFinish _ _ _ _ => FTerminal
  | ExpectDecode _ _ _ _ | ExpectCandidate _ _ _ _ | ExpectConsume _ _ _ _ _ => FSelect
  | ExpectScrub => FScrub
  | ExpectAuthority _ => FPublicationResult
  | ExpectRescanDecode | ExpectRescanCandidate => FRescan
  end.

(* The selection's frames so far are 64-bit words. *)
Definition stage_words (s: stage) : Prop :=
  match s with
  | ExpectDecode _ _ f fm | ExpectCandidate _ _ f fm => u64_ok f /\ u64_ok fm
  | ExpectConsume _ _ f fm cm => u64_ok f /\ u64_ok fm /\ u64_ok cm
  | _ => True
  end.

Definition progress_ok (x: inputs) (p: progress) : Prop :=
  match p with
  | Go s m => stage_step s = i_step x /\ stage_words s /\ mem_ok m /\ keeps x m
  | Return st m => status_ok st /\ mem_ok m /\ keeps x m
  end.



Lemma Zlength_upd_Znth' {A} (i: Z) (l: list A) (v: A) : Zlength (upd_Znth i l v) = Zlength l.
Proof.
  unfold upd_Znth. destruct (Sumbool.sumbool_and _ _ _ _ _ _); [| reflexivity].
  rewrite Zlength_app, Zlength_cons, !Zlength_sublist by lia. lia.
Qed.

Lemma Forall_Znth' {A} {d: Inhabitant A} (P: A -> Prop) (l: list A) (i: Z) :
  Forall P l -> 0 <= i < Zlength l -> P (Znth i l).
Proof. intros F R. rewrite Forall_forall in F. apply F, Znth_In. exact R. Qed.

Ltac unfold_statuses :=
  unfold S_OK, S_TERMINAL_VERSION, S_TERMINAL_STATUS, S_TERMINAL_ERROR, S_TERMINAL_FRAME, S_TERMINAL_OWNER,
    S_TERMINAL_ENTRY_COUNT, S_DECODER, S_AUTHORITY_NONE, S_AUTHORITY_NOMINATION, S_AUTHORITY_TARGET,
    S_AUTHORITY_ENTRY_COUNT, S_AUTHORITY_HIGHEST, S_AUTHORITY_USABLE, S_AUTHORITY_BLOCKED, S_AUTHORITY_MANIFEST,
    S_SCRUB, S_PUBLICATION_VERSION, S_PUBLICATION_STATUS, S_PUBLICATION_ERROR, S_PUBLICATION_FRAME,
    S_PUBLICATION_OBJECT, S_UNPUBLISHED_LIMIT, S_UNPUBLISHED_ORDER, S_RESCAN_ENTRY_COUNT, S_RESCAN_HIGHEST,
    S_RESCAN_TARGET, S_RESCAN_STATUS, S_RESCAN_USABLE, S_RESCAN_BLOCKED, S_RESCAN_MANIFEST in *.

(* Each check answers a status of the enum. *)
Ltac checks_ok :=
  unfold status_ok, terminal_check, cross_check, publication_check, rescan_order, rescan_check;
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; unfold_statuses; lia.

(* The memory's updates by the machine keep a memory of the model. *)
Lemma mem_ok_reserved (m: mem) (b v: Z) :
  mem_ok m -> u64_ok v -> mem_ok (with_reserved m (upd_Znth b (m_reserved m) v)).
Proof.
  destruct m. unfold mem_ok. cbn. intros (R1 & R2 & rest) V.
  refine (conj _ (conj _ rest)); [ rewrite Zlength_upd_Znth'; exact R1 | apply Forall_upd_Znth; auto ].
Qed.

Lemma mem_ok_terminal (m: mem) (q v: Z) :
  mem_ok m -> u64_ok v -> mem_ok (with_terminal m (upd_Znth q (m_terminal m) v)).
Proof.
  destruct m. unfold mem_ok. cbn. intros (R1 & R2 & T1 & T2 & rest) V.
  refine (conj R1 (conj R2 (conj _ (conj _ rest)))); [ rewrite Zlength_upd_Znth'; exact T1 | apply Forall_upd_Znth; auto ].
Qed.

Lemma mem_ok_state (m: mem) (k: Z) (ws: list Z) :
  mem_ok m -> Zlength ws = WORDS -> Forall u64_ok ws -> mem_ok (with_state m k ws).
Proof.
  destruct m. unfold mem_ok, with_state, with_states. cbn. intros (R1 & R2 & T1 & T2 & S1 & S2 & rest) L F.
  refine (conj R1 (conj R2 (conj T1 (conj T2 (conj _ (conj _ rest))))));
    [ rewrite Zlength_upd_Znth'; exact S1 | apply Forall_upd_Znth; auto ].
Qed.

Lemma mem_ok_publication (m: mem) (q v: Z) :
  mem_ok m -> u64_ok v -> mem_ok (with_publication m (upd_Znth q (m_publication m) v)).
Proof.
  destruct m. unfold mem_ok. cbn. intros (R1 & R2 & T1 & T2 & S1 & S2 & P1 & P2 & rest) V.
  refine (conj R1 (conj R2 (conj T1 (conj T2 (conj S1 (conj S2 (conj _ (conj _ rest))))))));
    [ rewrite Zlength_upd_Znth'; exact P1 | apply Forall_upd_Znth; auto ].
Qed.

Lemma mem_ok_rescan (m: mem) (r: list Z) :
  mem_ok m -> Zlength r = RESCAN_WORDS -> Forall u64_ok r -> mem_ok (with_rescan m r).
Proof.
  destruct m. unfold mem_ok. cbn. intros (R1 & R2 & T1 & T2 & S1 & S2 & P1 & P2 & Q1 & Q2 & rest) L F.
  exact (conj R1 (conj R2 (conj T1 (conj T2 (conj S1 (conj S2 (conj P1 (conj P2 (conj L (conj F rest)))))))))).
Qed.

Lemma mem_ok_records (m: mem) (s sm n: Z) :
  mem_ok m -> u64_ok s -> u64_ok sm -> u64_ok n -> mem_ok (with_records m s sm n).
Proof.
  destruct m. unfold mem_ok. cbn. intros (R1 & R2 & T1 & T2 & S1 & S2 & P1 & P2 & Q1 & Q2 & _ & _ & _ & D) Us Usm Un.
  exact (conj R1 (conj R2 (conj T1 (conj T2 (conj S1 (conj S2 (conj P1 (conj P2 (conj Q1 (conj Q2
           (conj Us (conj Usm (conj Un D))))))))))))).
Qed.

Lemma mem_ok_decoder (m: mem) (d: Z) : mem_ok m -> u32_ok d -> mem_ok (with_decoder m d).
Proof.
  destruct m. unfold mem_ok. cbn. intros (R1 & R2 & T1 & T2 & S1 & S2 & P1 & P2 & Q1 & Q2 & U1 & U2 & U3 & _) D.
  exact (conj R1 (conj R2 (conj T1 (conj T2 (conj S1 (conj S2 (conj P1 (conj P2 (conj Q1 (conj Q2
           (conj U1 (conj U2 (conj U3 D))))))))))))).
Qed.

(* The memory's updates by step f keep what f does not write. *)
Ltac keeps_tac x m :=
  unfold keeps; intros ? K; destruct x as [? ? ? ? ? ? ? ? ? ? m0]; cbn [i_step i_mem] in *; subst;
  rewrite K at 1; destruct m, m0; reflexivity.

Lemma keeps_with_reserved (x: inputs) (m: mem) (r: list Z) :
  i_step x = FTerminal -> keeps x m -> keeps x (with_reserved m r).
Proof. keeps_tac x m. Qed.
Lemma keeps_with_terminal (x: inputs) (m: mem) (t: list Z) :
  i_step x = FTerminal -> keeps x m -> keeps x (with_terminal m t).
Proof. keeps_tac x m. Qed.
Lemma keeps_with_state (x: inputs) (m: mem) (k: Z) (ws: list Z) :
  i_step x = FSelect -> keeps x m -> keeps x (with_state m k ws).
Proof. keeps_tac x m. Qed.
Lemma keeps_with_records (x: inputs) (m: mem) (s sm n: Z) :
  i_step x = FSelect -> keeps x m -> keeps x (with_records m s sm n).
Proof. keeps_tac x m. Qed.
Lemma keeps_with_decoder_select (x: inputs) (m: mem) (d: Z) :
  i_step x = FSelect -> keeps x m -> keeps x (with_decoder m d).
Proof. keeps_tac x m. Qed.
Lemma keeps_with_publication (x: inputs) (m: mem) (p: list Z) :
  i_step x = FPublicationResult -> keeps x m -> keeps x (with_publication m p).
Proof. keeps_tac x m. Qed.
Lemma keeps_with_rescan (x: inputs) (m: mem) (r: list Z) :
  i_step x = FRescan -> keeps x m -> keeps x (with_rescan m r).
Proof. keeps_tac x m. Qed.
Lemma keeps_with_decoder_rescan (x: inputs) (m: mem) (d: Z) :
  i_step x = FRescan -> keeps x m -> keeps x (with_decoder m d).
Proof. keeps_tac x m. Qed.

Lemma keeps_with_state1 (x: inputs) (m: mem) (ws: list Z) :
  i_step x = FRescan -> Zlength (m_states (i_mem x)) = 2 -> Zlength (m_states m) = 2 -> keeps x m ->
  keeps x (with_state m 1 ws).
Proof.
  unfold keeps. intros F L0 L K. destruct x as [f ? ? ? ? ? ? ? ? ? m0]; cbn [i_step i_mem] in *. subst f.
  rewrite K at 1. destruct m as [r t ss p rs s sm n d], m0 as [r0 t0 ss0 p0 rs0 s0 sm0 n0 d0].
  unfold written, with_state, with_states, with_rescan, with_decoder;
    cbn [m_reserved m_terminal m_states m_publication m_rescan m_selected m_selected_manifest m_next m_decoder] in *.
  rewrite upd_Znth_twice by lia. rewrite upd_Znth_same by lia. reflexivity.
Qed.

Lemma keeps_start (x: inputs) : Zlength (m_states (i_mem x)) = 2 -> keeps x (i_mem x).
Proof.
  unfold keeps. destruct x as [f ? ? ? ? ? ? ? ? ? m0]; cbn [i_step i_mem]. intros L.
  destruct m0 as [r t ss p rs s sm n d]; cbn in L.
  destruct f; unfold written, with_state, with_states, with_reserved, with_terminal, with_publication,
    with_rescan, with_records, with_decoder; cbn; try reflexivity.
  rewrite upd_Znth_triv by (auto; lia). reflexivity.
Qed.

Lemma go_ok (x: inputs) (s: stage) (m: mem) :
  stage_step s = i_step x -> stage_words s -> mem_ok m -> keeps x m -> progress_ok x (Go s m).
Proof. intros A B C D. exact (conj A (conj B (conj C D))). Qed.

Lemma ret_ok (x: inputs) (st: Z) (m: mem) : status_ok st -> mem_ok m -> keeps x m -> progress_ok x (Return st m).
Proof. intros A B C. exact (conj A (conj B C)). Qed.

Lemma start_ok (x: inputs) : inputs_ok x -> progress_ok x (start x).
Proof.
  intros I. pose proof I as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M).
  assert (K: keeps x (i_mem x)) by (apply keeps_start; destruct M as (_ & _ & _ & _ & S1 & _); exact S1).
  unfold start. destruct (i_step x) eqn:F;
    try solve [ apply go_ok; [ cbn; congruence | cbn; unfold u64_ok; try split; rep_lia | auto | auto ]
              | apply ret_ok; [ checks_ok | auto | auto ] ].
  destruct (rescan_order x =? S_OK).
  - apply go_ok; [ cbn; congruence | exact Logic.I | auto | auto ].
  - apply ret_ok; [ checks_ok | auto | auto ].
Qed.

(* One answer of the kind and range of its call keeps the invariant. *)
Lemma step_ok (x: inputs) (s: stage) (m: mem) (r: reply) :
  inputs_ok x -> progress_ok x (Go s m) -> reply_ok (expected x s m) r -> progress_ok x (step x s m r).
Proof.
  intros I (Fs & W & M & K) R.
  pose proof I as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M0).
  assert (L0: Zlength (m_states (i_mem x)) = 2) by (destruct M0 as (_ & _ & _ & _ & S1 & _); exact S1).
  assert (L: Zlength (m_states m) = 2) by (destruct M as (_ & _ & _ & _ & S1 & _); exact S1).
  destruct s; cbn [stage_step stage_words] in Fs, W; destruct r as [v | st ws]; cbn in R; try contradiction;
    unfold step; cbn [reply_value reply_state].
  - (* ExpectManifest *)
    destruct (Zlength a <? 2).
    + apply go_ok; auto.
    + unfold overlay_done. apply go_ok; auto. apply mem_ok_reserved; auto. apply keeps_with_reserved; auto.
  - (* ExpectFree *)
    unfold free_done. destruct (b + 1 <? BLOCKS); apply go_ok; auto.
  - (* ExpectFinish *)
    assert (M': mem_ok (with_terminal m (upd_Znth q (m_terminal m) v))) by (apply mem_ok_terminal; auto).
    assert (K': keeps x (with_terminal m (upd_Znth q (m_terminal m) v))) by (apply keeps_with_terminal; auto).
    unfold finish_done. destruct (q + 1 <? TERMINAL_WORDS); [ apply go_ok | apply ret_ok ]; auto. checks_ok.
  - (* ExpectDecode *)
    destruct R as (Rs & Rl & Rw).
    assert (M': mem_ok (with_state m k ws)) by (apply mem_ok_state; auto).
    assert (K': keeps x (with_state m k ws)) by (apply keeps_with_state; auto).
    unfold decode_done. destruct (st =? 0); [ apply go_ok | apply ret_ok ]; auto.
    + unfold status_ok; unfold_statuses; lia.
    + apply mem_ok_decoder; auto.
    + apply keeps_with_decoder_select; auto.
  - (* ExpectCandidate *)
    destruct W. apply go_ok; [ auto | cbn [stage_words]; auto | auto | auto ].
  - (* ExpectConsume *)
    destruct W as (Wf & Wfm & Wcm).
    unfold consume_done, next_candidate, select_done.
    repeat match goal with |- context [if ?c then _ else _] => destruct c end;
      first [ apply go_ok; [ auto | cbn [stage_words]; split; auto | auto | auto ]
            | apply ret_ok; [ unfold status_ok; unfold_statuses; lia
                            | apply mem_ok_records; auto; unfold u64_ok; rep_lia
                            | apply keeps_with_records; auto ] ].
  - (* ExpectScrub *)
    apply ret_ok; auto. unfold status_ok. destruct (v =? 1); unfold_statuses; lia.
  - (* ExpectAuthority *)
    assert (M': mem_ok (with_publication m (upd_Znth q (m_publication m) v))) by (apply mem_ok_publication; auto).
    assert (K': keeps x (with_publication m (upd_Znth q (m_publication m) v)))
      by (apply keeps_with_publication; auto).
    unfold authority_done. destruct (q + 1 <? PUBLICATION_WORDS); [ apply go_ok | apply ret_ok ]; auto.
    unfold status_ok; unfold_statuses; lia.
  - (* ExpectRescanDecode *)
    destruct R as (Rs & Rl & Rw).
    assert (M': mem_ok (with_state m 1 ws)) by (apply mem_ok_state; auto).
    assert (K': keeps x (with_state m 1 ws)) by (apply keeps_with_state1; auto).
    unfold decode_done. destruct (st =? 0); [ apply go_ok | apply ret_ok ]; auto.
    + unfold status_ok; unfold_statuses; lia.
    + apply mem_ok_decoder; auto.
    + apply keeps_with_decoder_rescan; auto.
  - (* ExpectRescanCandidate *)
    unfold rescan_done.
    pose proof M as (_ & _ & _ & _ & S1 & S2 & _).
    destruct (Forall_Znth' _ (m_states m) 1 S2 ltac:(lia)) as [Ls Fs1].
    destruct (rescan_check x (Znth 1 (m_states m)) v =? S_OK); apply ret_ok; auto; try checks_ok.
    + apply mem_ok_rescan; auto.
      repeat apply Forall_cons; try apply Forall_nil; auto; apply (Forall_Znth' u64_ok); auto; lia.
    + apply keeps_with_rescan; auto.
Qed.

Lemma run_ok (x: inputs) (p p': progress) (h: list answer) :
  inputs_ok x -> progress_ok x p -> answers_ok h -> run x p h = Some p' -> progress_ok x p'.
Proof.
  revert p. induction h as [| [c r] rest IH]; intros p I P A R; cbn in R.
  - inversion R; subst; exact P.
  - destruct p as [s m | st m]; [| discriminate].
    destruct (call_eq_dec c (expected x s m)) as [E | _]; [| discriminate].
    destruct (fits c r); [| discriminate].
    inversion A as [| ? ? A1 A2]; subst. cbn in A1.
    apply (IH (step x s m r)); auto. apply step_ok; auto.
Qed.

(* Every return of the model, for inputs of main and answers of their calls' kinds and ranges, has a status of
   the enum, leaves a memory of the model, and keeps what the step does not write. *)
Lemma returns_ok (x: inputs) (h: list answer) (st: Z) (m: mem) :
  inputs_ok x -> answers_ok h -> returns x h = Some (st, m) -> status_ok st /\ mem_ok m /\ keeps x m.
Proof.
  intros I A R. apply returns_run in R.
  exact (run_ok x (start x) (Return st m) h I (start_ok x I) A R).
Qed.

(* The next step of boot_allocate's sequence has inputs of main, the step's memory being one of the model. *)
Lemma inputs_ok_next (x x': inputs) (m: mem) :
  inputs_ok x -> mem_ok m -> allocate_next x m = Some x' -> inputs_ok x'.
Proof.
  intros (U1 & U2 & U3 & U4 & U5 & rest) M A.
  pose proof M as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Us & Usm & Un & _).
  pose proof rest as (L1 & F1 & L2 & F2 & L3 & F3 & L4 & F4 & _).
  unfold allocate_next in A.
  destruct (i_step x); try destruct (i_take_next x =? 0); inversion A; subst; clear A;
    unfold inputs_ok, with_step, after_select; cbn;
    repeat match goal with |- _ /\ _ => split end; auto.
Qed.
