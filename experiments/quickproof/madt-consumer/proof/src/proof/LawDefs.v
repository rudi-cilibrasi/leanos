(* Law consumer_obligations: the law's oracle (the harness's global `oracle` and a readable share of the span it
   reads), as the oracle predicate Ora_law of the protocol of MadtSpecs, and the specifications of the harness's
   helpers.  The oracle's fields are a function of the consumer's run: while it calls (Go) they are the stage's, and
   once it has returned (Return o) they are what main's checks need of them (main_ok). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosMadt.harness.consumer_obligations.code.
Require Import LeanosMadt.proof.Defs.
Require Import LeanosMadt.proof.MadtSpecs.
Require Import LeanosMadt.proof.LawProg.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[export] Existing Instance LawProg.LCS.

Definition t_oracle := Tstruct _oracle__1 noattr.

(* The oracle's mutable fields: phase, byte, word, state[12], answer[16], nmi_count, nmi[4], policy[5], bound[6],
   rejected. *)
Record ost : Type := mk_ost {
  os_phase: Z; os_byte: Z; os_word: Z; os_state: list Z; os_answer: list Z; os_count: Z; os_nmi: list Z;
  os_policy: list Z; os_bound: list Z; os_rejected: Z }.

(* struct oracle: entries, length, executing, cpuid_edx, available, apic_base, sample_id, routing, then s. *)
Definition oval (p: val) (n: Z) (ob: observation) (s: ost) : reptype t_oracle :=
  (p, (vl n, (vl (o_executing ob), (vl (o_cpuid_edx ob), (vl (o_available ob), (vl (o_apic_base ob),
   (vl (o_sample_id ob), (vl (o_routing ob), (vl (os_phase s), (vl (os_byte s), (vl (os_word s),
   (map vl (os_state s), (map vl (os_answer s), (vl (os_count s), (map vl (os_nmi s), (map vl (os_policy s),
   (map vl (os_bound s), vl (os_rejected s)))))))))))))))))).

(* The same, field by field (as the exports and main use it; LawSplit proves it is the struct). *)
Definition ofields (q p: val) (n: Z) (ob: observation) (s: ost) : mpred :=
 (field_at Ews t_oracle (DOT _entries) p q * field_at Ews t_oracle (DOT _length) (vl n) q *
  field_at Ews t_oracle (DOT _executing) (vl (o_executing ob)) q *
  field_at Ews t_oracle (DOT _cpuid_edx) (vl (o_cpuid_edx ob)) q *
  field_at Ews t_oracle (DOT _available) (vl (o_available ob)) q *
  field_at Ews t_oracle (DOT _apic_base) (vl (o_apic_base ob)) q *
  field_at Ews t_oracle (DOT _sample_id) (vl (o_sample_id ob)) q *
  field_at Ews t_oracle (DOT _routing) (vl (o_routing ob)) q *
  field_at Ews t_oracle (DOT _phase) (vl (os_phase s)) q *
  field_at Ews t_oracle (DOT _byte) (vl (os_byte s)) q *
  field_at Ews t_oracle (DOT _word) (vl (os_word s)) q *
  field_at Ews t_oracle (DOT _state) (map vl (os_state s)) q *
  field_at Ews t_oracle (DOT _answer) (map vl (os_answer s)) q *
  field_at Ews t_oracle (DOT _nmi_count) (vl (os_count s)) q *
  field_at Ews t_oracle (DOT _nmi) (map vl (os_nmi s)) q *
  field_at Ews t_oracle (DOT _policy) (map vl (os_policy s)) q *
  field_at Ews t_oracle (DOT _bound) (map vl (os_bound s)) q *
  field_at Ews t_oracle (DOT _rejected) (vl (os_rejected s)) q)%logic.

Definition ost_ok (s: ost) : Prop :=
  u64_ok (os_phase s) /\ u64_ok (os_byte s) /\ u64_ok (os_word s) /\ u64_ok (os_count s) /\
  u64_ok (os_rejected s) /\
  Zlength (os_state s) = 12 /\ Zlength (os_answer s) = 16 /\ Zlength (os_nmi s) = 4 /\
  Zlength (os_policy s) = 5 /\ Zlength (os_bound s) = 6 /\
  Forall u64_ok (os_state s) /\ Forall u64_ok (os_answer s) /\ Forall u64_ok (os_nmi s) /\
  Forall u64_ok (os_policy s) /\ Forall u64_ok (os_bound s).

(* The record walk's result, which main stores before the call and nothing changes. *)
Definition nmi_ok (bytes: list Z) (s: ost) : Prop :=
  forall c m, records bytes = Some (c, m) -> os_count s = c /\ os_nmi s = m.

(* The oracle while the consumer calls, in stage g. *)
Definition go_inv (x: inputs) (g: stage) (s: ost) : Prop :=
  let n := Zlength (fst x) in
  match g with
  | Stream i state cur =>
      os_phase s = 0 /\ os_byte s = i /\ os_word s = Zlength cur /\ os_state s = state /\
      sublist 0 (Zlength cur) (os_answer s) = cur /\ os_rejected s = 0 /\ 0 <= i < n /\ Zlength cur < 16
  | Policy last state count nmi cur =>
      os_phase s = 1 /\ os_byte s = n /\ os_word s = Zlength cur /\ os_state s = state /\ os_answer s = last /\
      sublist 0 (Zlength cur) (os_policy s) = cur /\ os_rejected s = 0 /\ records (fst x) = Some (count, nmi) /\
      Zlength cur < 5
  | Bound last state cur =>
      os_phase s = 2 /\ os_byte s = n /\ os_word s = Zlength cur /\ os_state s = state /\ os_answer s = last /\
      os_policy s = [1; 1; 0; 1; 4] /\ sublist 0 (Zlength cur) (os_bound s) = cur /\ os_rejected s = 0 /\
      records (fst x) <> None /\ Zlength cur < 6
  end.

(* The conditions of main's checks. *)
Definition two_b (a: list Z) : bool := (Znth 0 a =? 1) && (Znth 1 a =? 2).
Definition pacc (p: list Z) : bool :=
  (Znth 0 p =? 1) && (Znth 1 p =? 1) && (Znth 2 p =? 0) && (Znth 3 p =? 1) && (Znth 4 p =? 4).
Definition five_b (p: list Z) : bool :=
  (Znth 0 p =? 1) && (Znth 3 p <=? 1) && (Znth 4 p <=? 4) && negb (Znth 1 p =? 1).
Definition bacc (ob: observation) (state b: list Z) : bool :=
  (Znth 0 b =? 1) && (Znth 1 b =? 1) && (Znth 2 b =? o_executing ob) && (Znth 3 b =? Znth 6 state) &&
  (Znth 4 b =? o_apic_base ob) && (Znth 5 b =? 0).
Definition four_b (b: list Z) : bool := (Znth 0 b =? 1) && (Znth 5 b =? 0) && ((Znth 1 b =? 2) || (Znth 1 b =? 5)).
Definition walk_b (bytes: list Z) : bool := match records bytes with Some _ => true | None => false end.

(* The oracle once the consumer has returned the outcome r: main's checks after a valid call, in its order. *)
Definition main_ok (x: inputs) (r: outcome) (s: ost) : Prop :=
  let '(stt, d, off, a, c, b) := r in
  0 <= stt <= 5 /\ (stt <> 0 -> a = 0 /\ c = 0 /\ b = 0) /\
  (os_rejected s <> 0 ->
     stt = (if two_b (os_answer s) then 2 else 3) /\
     d = (if two_b (os_answer s) then Znth 2 (os_answer s) else 0) /\ off = 44 + os_byte s) /\
  (os_rejected s = 0 ->
     os_byte s = Zlength (fst x) /\ off = Znth 0 (os_state s) /\
     (walk_b (fst x) = false -> os_phase s = 1 /\ os_word s = 0 /\ stt = 3 /\ d = 0) /\
     (walk_b (fst x) = true -> os_phase s = 3 /\
        (pacc (os_policy s) = false ->
           stt = (if five_b (os_policy s) then 5 else 3) /\
           d = (if five_b (os_policy s) then Znth 2 (os_policy s) else 0)) /\
        (pacc (os_policy s) = true -> os_word s = 0 /\
           (bacc (snd x) (os_state s) (os_bound s) = true ->
              stt = 0 /\ d = 0 /\ a = Znth 2 (os_bound s) /\ c = Znth 3 (os_bound s) /\ b = Znth 4 (os_bound s)) /\
           (bacc (snd x) (os_state s) (os_bound s) = false ->
              stt = (if four_b (os_bound s) then 4 else 3) /\
              d = (if four_b (os_bound s) then Znth 2 (os_bound s) else 0))))).

(* The oracle after the answers h. *)
Definition J (x: inputs) (h: list answer) (s: ost) : Prop :=
  match run x (start x) h with
  | Some (Go g) => go_inv x g s
  | Some (Return r) => main_ok x r s
  | None => False
  end.

(* The law's oracle: the global `oracle`, whose entries point at the span, and a readable share of the span. *)
Definition Ora_law : ORA := fun gv x h =>
  EX p: val, EX sh: share, EX s: ost,
    !! (readable_share sh /\ length_ok (Zlength (fst x)) = true /\ Forall byte_ok (fst x) /\ obs_ok (snd x) /\
        ost_ok s /\ nmi_ok (fst x) s /\ J x h s) &&
    (ofields (gv _oracle) p (Zlength (fst x)) (snd x) s *
     data_at sh (tarray tuchar (Zlength (fst x))) (bytes_val (fst x)) p)%logic.

(* ---------------------------------------------------------------------- *)
(* The harness's helpers                                                    *)
(* ---------------------------------------------------------------------- *)

Definition any_u64_spec :=
  DECLARE _any_u64
  WITH u: unit
  PRE [ ] PROP () PARAMS () SEP ()
  POST [ tulong ] EX v: Z, PROP (u64_ok v) RETURN (vl v) SEP ().

(* records_ok(e, length, count, nmi): Defs.records, with the count and the NMI words it stores when it returns 1. *)
Definition records_ok_spec :=
  DECLARE _records_ok
  WITH e: val, sh: share, bytes: list Z, cp: val, np: val
  PRE [ tptr tuchar, tulong, tptr tulong, tptr tulong ]
    PROP (readable_share sh; Forall byte_ok bytes; Zlength bytes <= MAX_LENGTH)
    PARAMS (e; vl (Zlength bytes); cp; np)
    SEP (data_at sh (tarray tuchar (Zlength bytes)) (bytes_val bytes) e; data_at_ Ews tulong cp;
         data_at_ Ews (tarray tulong 4) np)
  POST [ tint ]
    EX c: Z, EX m: list Z,
    PROP (u64_ok c; Zlength m = 4; Forall u64_ok m;
          match records bytes with Some (c', m') => c = c' /\ m = m' | None => True end)
    RETURN (Vint (Int.repr (if walk_b bytes then 1 else 0)))
    SEP (data_at sh (tarray tuchar (Zlength bytes)) (bytes_val bytes) e; data_at Ews tulong (vl c) cp;
         data_at Ews (tarray tulong 4) (map vl m) np).

(* The global variable of the harness, for the functions that use it. *)
Definition Vlaw : varspecs := [(_oracle, t_oracle)].
