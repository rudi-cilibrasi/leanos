(* Law handoff_decode_exact: main's state at its call (the law's oracle about to be handed over) and after it (its
   checks). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosHandoff.harness.handoff_decode_exact.code.
Require Import LeanosHandoff.proof.Defs.
Require Import LeanosHandoff.proof.HandoffSpecs.
Require Import LeanosHandoff.proof.LawProg LeanosHandoff.proof.LawDefs LeanosHandoff.proof.LawFacts
  LeanosHandoff.proof.LawLib LeanosHandoff.proof.LawZero LeanosHandoff.proof.LawMainDefs LeanosHandoff.proof.LawMainPre.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[export] Existing Instance LawProg.LCS.

(* m->info_expect: the copy in an allocation, main's info_expect otherwise. *)
Definition ie_of (x: inputs) (cep iep: val) : val := if is_alloc x then cep else iep.

(* The projection record main passes. *)
Definition proj_val (gv: globals) (up bp rp: val) : val * (val * (val * (val * val))) :=
  (gv _projection_record, (gv _law, (up, (bp, rp)))).

(* The model's inputs of main's x (the contents it chose) and its two expectation arrays: x with, in the words the
   model does not read for the call, the encoding of the pointer of the array the oracle holds (LawDefs.ptr_ok). *)
Definition xm (x: inputs) (cep iep: val) : inputs :=
  mk_inputs (i_call x) (i_magic x) (i_address x) (i_total x) (i_candidate x)
    (if has_copy x then enc_ptr cep else i_info x) (if has_copy x then i_copy x else enc_ptr iep)
    (i_usable x) (i_blocked x) (i_reserved x) (i_states x) (i_total_record x) (i_length_record x)
    (i_current_record x).

(* The expectation array main keeps itself: info_expect for an allocation or a copy, copy_expect otherwise. *)
Definition own_obj (x: inputs) (cep iep: val) : mpred :=
  if has_copy x then data_at Ews (tarray tulong (info_len x)) (map vl (i_info x)) iep
  else data_at Ews (tarray tulong (copy_len x)) (map vl (i_copy x)) cep.

Definition call_pre (gv: globals) (x: inputs) (s0: lst) (cp cep ip iep up bp rp sp vtr vlr vcr vpj: val)
    : environ -> mpred :=
  PROP ()
  LOCAL (temp _m (gv _law); temp _copy_words (vi (copy_len x)); temp _copy cp; temp _copy_expect cep;
         temp _info_words (vi (info_len x)); temp _info ip; temp _info_expect iep; temp _usable up;
         temp _blocked bp; temp _reserved rp; temp _states sp;
         temp _total_prior (vi (i_total_record x)); temp _length_prior (vi (i_length_record x));
         temp _current_prior (vi (i_current_record x));
         lvar _total_record tuint vtr; lvar _length_record tuint vlr; lvar _current_record tuint vcr;
         lvar _projection t_projection vpj; gvars gv)
  SEP (mem_mgr gv; lfields (gv _law) (xm x cep iep) cep (ie_of x cep iep) (mem_of (start (xm x cep iep))) s0;
       arrays (xm x cep iep) cep (ie_of x cep iep) (mem_of (start (xm x cep iep)));
       own_obj x cep iep;
       data_at Ews (tarray tulong (copy_len x)) (map vl (i_copy x)) cp;
       data_at Ews (tarray tulong (info_len x)) (map vl (i_info x)) ip;
       data_at Ews (tarray tulong 64) (map vl (i_usable x)) up;
       data_at Ews (tarray tulong 64) (map vl (i_blocked x)) bp;
       data_at Ews (tarray tulong 64) (map vl (i_reserved x)) rp;
       data_at Ews t_states (states_val (i_states x)) sp;
       data_at Tsh tuint (vi (i_total_record x)) vtr; data_at Tsh tuint (vi (i_length_record x)) vlr;
       data_at Tsh tuint (vi (i_current_record x)) vcr; data_at Tsh t_projection (proj_val gv up bp rp) vpj; TT).

Definition call_ok (Espec: OracleKind) : Prop :=
  forall gv x s0 cp cep ip iep up bp rp sp vtr vlr vcr vpj,
  inputs_ok (xm x cep iep) -> x_fit (xm x cep iep) -> ptr_ok (xm x cep iep) cep (ie_of x cep iep) ->
  filled x -> (i_call x <> FAllocate -> extent_fits (i_total x)) -> J (xm x cep iep) (start (xm x cep iep)) s0 ->
  isptr cp -> isptr cep -> isptr ip -> isptr iep -> isptr up -> isptr bp -> isptr rp -> isptr sp ->
  @semax LCS Espec Delta0 (call_pre gv x s0 cp cep ip iep up bp rp sp vtr vlr vcr vpj) s_call Post0.

Lemma dec_enc: forall p, isptr p -> dec_ptr (enc_ptr p) = p.
Proof.
  intros p P. destruct p; try contradiction. unfold dec_ptr, enc_ptr.
  change (Znth 0 [Zpos b; Ptrofs.unsigned i]) with (Zpos b).
  change (Znth 1 [Zpos b; Ptrofs.unsigned i]) with (Ptrofs.unsigned i).
  rewrite Ptrofs.repr_unsigned. reflexivity.
Qed.

(* The rest of main, as a hypothesis. *)
Definition rest_ok (Espec: OracleKind) : Prop :=
  forall gv x cp cep ip iep up bp rp sp vtr vlr vcr vpj,
  x0_ok (call_code (i_call x)) (i_magic x) (i_address x) (i_total x) (i_candidate x) -> filled x ->
  isptr cp -> isptr cep -> isptr ip -> isptr iep -> isptr up -> isptr bp -> isptr rp -> isptr sp ->
  @semax LCS Espec Delta0 (rest_pre gv x cp cep ip iep up bp rp sp vtr vlr vcr vpj) s_rest Post0.

