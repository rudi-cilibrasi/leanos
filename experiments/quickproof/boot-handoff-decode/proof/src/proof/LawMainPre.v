(* Law handoff_decode_exact: the states of main the parts of its proof share: before the fills of the storage,
   before the records, at the call (the law's oracle about to be handed over), and after the call (its checks). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosHandoff.harness.handoff_decode_exact.code.
Require Import LeanosHandoff.proof.Defs.
Require Import LeanosHandoff.proof.HandoffSpecs.
Require Import LeanosHandoff.proof.LawProg LeanosHandoff.proof.LawDefs LeanosHandoff.proof.LawFacts
  LeanosHandoff.proof.LawLib LeanosHandoff.proof.LawZero LeanosHandoff.proof.LawMainDefs.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[export] Existing Instance LawProg.LCS.

(* main's inputs before the fills: the call, the magic, the address, the extent, the candidate. *)
Definition x0 (cc mg ad tt cd: Z) : inputs := mk_inputs (call_of cc) mg ad tt cd nil nil nil nil nil nil 0 0 0.

(* The inputs once the storage is filled and the records drawn. *)
Definition xin (cc mg ad tt cd: Z) (il cl ul bl rl: list Z) (sl: list (list Z)) (tr lr cr: Z) : inputs :=
  mk_inputs (call_of cc) mg ad tt cd il cl ul bl rl sl tr lr cr.

Definition info_len (x: inputs) : Z := if is_alloc x then 0 else i_total x / 8.

(* The facts of main's choices. *)
Definition x0_ok (cc mg ad tt cd: Z) : Prop :=
  0 <= cc <= 3 /\ u32_ok mg /\ u32_ok ad /\ u32_ok tt /\ u64_ok cd /\
  (cc <> 0 -> extent_fits tt).

(* The law's fields before the fills: main's choices, the rest as zero. *)
Definition fields0 (q: val) (x: inputs) : mpred :=
  lraw q (vi (call_code (i_call x))) (vi (i_magic x)) (vi (i_address x)) (vi (i_total x)) (vl (target x))
    (vi (proj_code x)) z32 nullval nullval (Zrepeat z64 64) (Zrepeat z64 64) (Zrepeat z64 64)
    (Zrepeat (Zrepeat z64 41) 2) z32 z32 z32 z32 z32 z64 z64 z64 z64 (Zrepeat z64 7) (Zrepeat z64 41).

Definition fill_pre (gv: globals) (x: inputs) (cp cep ip iep up bp rp sp vtr vlr vcr vpj: val) : environ -> mpred :=
  PROP ()
  LOCAL (temp _m (gv _law); temp _copy_words (vi (copy_len x)); temp _copy cp; temp _copy_expect cep;
         temp _info_words (vi (info_len x)); temp _info ip; temp _info_expect iep; temp _usable up;
         temp _blocked bp; temp _reserved rp; temp _states sp;
         lvar _total_record tuint vtr; lvar _length_record tuint vlr; lvar _current_record tuint vcr;
         lvar _projection t_projection vpj; gvars gv)
  SEP (mem_mgr gv; fields0 (gv _law) x;
       data_at_ Ews (tarray tulong (copy_len x)) cp; data_at_ Ews (tarray tulong (copy_len x)) cep;
       data_at_ Ews (tarray tulong (info_len x)) ip; data_at_ Ews (tarray tulong (info_len x)) iep;
       data_at_ Ews (tarray tulong 64) up; data_at_ Ews (tarray tulong 64) bp; data_at_ Ews (tarray tulong 64) rp;
       data_at_ Ews t_states sp;
       data_at_ Tsh tuint vtr; data_at_ Tsh tuint vlr; data_at_ Tsh tuint vcr; data_at_ Tsh t_projection vpj; TT).

(* The law's fields once the storage is filled: the bitmaps and the states as main's. *)
Definition fields1 (q: val) (x: inputs) : mpred :=
  lraw q (vi (call_code (i_call x))) (vi (i_magic x)) (vi (i_address x)) (vi (i_total x)) (vl (target x))
    (vi (proj_code x)) z32 nullval nullval (map vl (i_usable x)) (map vl (i_blocked x)) (map vl (i_reserved x))
    (states_val (i_states x)) z32 z32 z32 z32 z32 z64 z64 z64 z64 (Zrepeat z64 7) (Zrepeat z64 41).

(* The storage as filled: the facts. *)
Definition filled (x: inputs) : Prop :=
  Zlength (i_copy x) = copy_len x /\ Forall u64_ok (i_copy x) /\
  Zlength (i_info x) = info_len x /\ Forall u64_ok (i_info x) /\
  Zlength (i_usable x) = BLOCKS /\ Forall u64_ok (i_usable x) /\
  Zlength (i_blocked x) = BLOCKS /\ Forall u64_ok (i_blocked x) /\
  Zlength (i_reserved x) = BLOCKS /\ Forall u64_ok (i_reserved x) /\
  Zlength (i_states x) = 2 /\ state_ok (Znth 0 (i_states x)) /\ state_ok (Znth 1 (i_states x)).

Definition rest_pre (gv: globals) (x: inputs) (cp cep ip iep up bp rp sp vtr vlr vcr vpj: val) : environ -> mpred :=
  PROP ()
  LOCAL (temp _m (gv _law); temp _copy_words (vi (copy_len x)); temp _copy cp; temp _copy_expect cep;
         temp _info_words (vi (info_len x)); temp _info ip; temp _info_expect iep; temp _usable up;
         temp _blocked bp; temp _reserved rp; temp _states sp;
         lvar _total_record tuint vtr; lvar _length_record tuint vlr; lvar _current_record tuint vcr;
         lvar _projection t_projection vpj; gvars gv)
  SEP (mem_mgr gv; fields1 (gv _law) x;
       data_at Ews (tarray tulong (copy_len x)) (map vl (i_copy x)) cp;
       data_at Ews (tarray tulong (copy_len x)) (map vl (i_copy x)) cep;
       data_at Ews (tarray tulong (info_len x)) (map vl (i_info x)) ip;
       data_at Ews (tarray tulong (info_len x)) (map vl (i_info x)) iep;
       data_at Ews (tarray tulong 64) (map vl (i_usable x)) up;
       data_at Ews (tarray tulong 64) (map vl (i_blocked x)) bp;
       data_at Ews (tarray tulong 64) (map vl (i_reserved x)) rp;
       data_at Ews t_states (states_val (i_states x)) sp;
       data_at_ Tsh tuint vtr; data_at_ Tsh tuint vlr; data_at_ Tsh tuint vcr; data_at_ Tsh t_projection vpj; TT).

(* The fills, as a hypothesis of the proof of main's beginning. *)
Definition fill_ok (Espec: OracleKind) : Prop :=
  forall gv cc mg ad tt cd cp cep ip iep up bp rp sp vtr vlr vcr vpj,
  x0_ok cc mg ad tt cd ->
  isptr cp -> isptr cep -> isptr ip -> isptr iep -> isptr up -> isptr bp -> isptr rp -> isptr sp ->
  @semax LCS Espec Delta0 (fill_pre gv (x0 cc mg ad tt cd) cp cep ip iep up bp rp sp vtr vlr vcr vpj) s_fill Post0.

Lemma x0_call: forall cc mg ad tt cd, i_call (x0 cc mg ad tt cd) = call_of cc.
Proof. reflexivity. Qed.

Lemma call_of_0: forall c, 0 <= c <= 3 -> (call_of c = FAllocate <-> c = 0).
Proof.
  intros c H. unfold call_of. split; intros E.
  - destruct (Z.eqb_spec c 0); [ auto | ]. destruct (c =? 1), (c =? 2); discriminate.
  - subst. reflexivity.
Qed.

(* From the first malloc on. *)
Definition s_malloc : statement :=
  ltac:(main_from ltac:(fun s => match s with Scall (Some _t'10) _ _ => idtac end)).

Definition malloc_pre (gv: globals) (x: inputs) (vtr vlr vcr vpj: val) : environ -> mpred :=
  PROP ()
  LOCAL (temp _m (gv _law); temp _copy_words (vi (copy_len x));
         lvar _total_record tuint vtr; lvar _length_record tuint vlr; lvar _current_record tuint vcr;
         lvar _projection t_projection vpj; gvars gv)
  SEP (mem_mgr gv; fields0 (gv _law) x;
       data_at_ Tsh tuint vtr; data_at_ Tsh tuint vlr; data_at_ Tsh tuint vcr; data_at_ Tsh t_projection vpj; TT).

Definition malloc_ok (Espec: OracleKind) : Prop :=
  forall gv cc mg ad tt cd vtr vlr vcr vpj,
  x0_ok cc mg ad tt cd ->
  @semax LCS Espec Delta0 (malloc_pre gv (x0 cc mg ad tt cd) vtr vlr vcr vpj) s_malloc Post0.
