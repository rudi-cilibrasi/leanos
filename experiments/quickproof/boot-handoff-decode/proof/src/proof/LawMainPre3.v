(* Law handoff_decode_exact: main's state after its call: the law's oracle at the run's answers, main's objects as
   the function left them (the model's memory m, or main's own where the function was not given them), the three
   records as the outcome's, the projection record main passed; then the checks (check_ok). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosHandoff.harness.handoff_decode_exact.code.
Require Import LeanosHandoff.proof.Defs.
Require Import LeanosHandoff.proof.HandoffSpecs.
Require Import LeanosHandoff.proof.LawProg LeanosHandoff.proof.LawDefs LeanosHandoff.proof.LawFacts
  LeanosHandoff.proof.LawLib LeanosHandoff.proof.LawZero LeanosHandoff.proof.LawMainDefs LeanosHandoff.proof.LawMainPre
  LeanosHandoff.proof.LawMainPre2.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[export] Existing Instance LawProg.LCS.

(* From main's checks on. *)
Definition check_pre (gv: globals) (x: inputs) (h: list answer) (st: Z) (m: mem)
    (cp cep ip iep up bp rp sp vtr vlr vcr vpj: val) : environ -> mpred :=
  PROP ()
  LOCAL (temp _status (vi st); temp _m (gv _law); temp _copy_words (vi (copy_len x)); temp _copy cp;
         temp _copy_expect cep; temp _info_words (vi (info_len x)); temp _info ip; temp _info_expect iep;
         temp _usable up; temp _blocked bp; temp _reserved rp; temp _states sp;
         temp _total_prior (vi (i_total_record x)); temp _length_prior (vi (i_length_record x));
         temp _current_prior (vi (i_current_record x));
         lvar _total_record tuint vtr; lvar _length_record tuint vlr; lvar _current_record tuint vcr;
         lvar _projection t_projection vpj; gvars gv)
  SEP (Ora_law gv (gv _law) (gv _law) (xm x cep iep) h; own_obj x cep iep;
       data_at Ews (tarray tulong (copy_len x)) (map vl (if has_copy x then m_copy m else i_copy x)) cp;
       data_at Ews (tarray tulong (info_len x)) (map vl (i_info x)) ip;
       data_at Ews (tarray tulong 64) (map vl (m_usable m)) up;
       data_at Ews (tarray tulong 64) (map vl (m_blocked m)) bp;
       data_at Ews (tarray tulong 64) (map vl (m_reserved m)) rp;
       data_at Ews t_states (states_val (m_states m)) sp;
       data_at Tsh tuint (vi (out_total_record (xm x cep iep) m)) vtr;
       data_at Tsh tuint (vi (out_length_record (xm x cep iep) st m)) vlr;
       data_at Tsh tuint (vi (out_current_record (xm x cep iep) st m)) vcr;
       data_at Tsh t_projection (gv _projection_record, (gv _law, (up, (bp, rp)))) vpj; TT).

Definition check_ok (Espec: OracleKind) : Prop :=
  forall gv x h st m cp cep ip iep up bp rp sp vtr vlr vcr vpj,
  returns (xm x cep iep) h = Some (st, m) -> filled x -> isptr cep -> isptr iep ->
  @semax LCS Espec Delta0 (check_pre gv x h st m cp cep ip iep up bp rp sp vtr vlr vcr vpj) s_check Post0.
