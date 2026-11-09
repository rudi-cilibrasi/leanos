(* Law admission_exact: main's call of the function it chose: the law's oracle handed over at no answers (its fields
   folded after the loads of the arguments), the copy and the APIC ID record between the law's compspecs and the
   unit's; then the checks (LawMainCheck). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosMadtAdmission.harness.admission_exact.code.
Require Import LeanosMadtAdmission.proof.Defs.
Require Import LeanosMadtAdmission.proof.MgaSpecs.
Require Import LeanosMadtAdmission.proof.LawProg LeanosMadtAdmission.proof.LawDefs LeanosMadtAdmission.proof.LawFacts
  LeanosMadtAdmission.proof.LawLib LeanosMadtAdmission.proof.LawMainLib
  LeanosMadtAdmission.proof.LawMainCheck.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

Lemma tail_disp {Espec: OracleKind} gv madt cp vid x s0:
  inputs_ok x -> lst_ok s0 -> J x nil s0 -> ls_args s0 = i_args x -> isptr madt ->
  forall Delta R cmd, Delta = Delta0 -> R = Post0 -> cmd = s_disp ->
  semax Delta
    (PROP () LOCAL (temp _prior (vi (i_prior x)); temp _madt madt; temp _m (gv _law); lvar _id tuint vid; gvars gv)
     SEP (lfields (gv _law) cp x s0; data_at Ews (tarray tuchar (i_length x)) (bytes_val (i_bytes x)) madt;
          data_at Ews (tarray tuchar (i_length x)) (bytes_val (i_bytes x)) cp;
          data_at Tsh tuint (vi (i_prior x)) vid; TT))
    cmd R.
Proof.
  intros Hx Hs HJ Ha Pm Delta R cmd -> -> ->.
  unfold s_disp, Delta0, Post0. start_tail.
  pose proof (call_code_range (i_call x)) as Rc.
  pose proof Hx as Hx'. inputs_facts Hx'.
  assert (E0: mk_lst (i_args x) (ls_expect s0) (ls_verdict s0) (ls_at s0) (ls_word s0) (ls_state s0) (ls_answer s0)
                     (ls_id s0) = s0) by (destruct s0; simpl in *; subst; reflexivity).
  unfold lfields. Intros. rewrite Ha.
  rng_list (i_args x) 10.
  forward.
  forward_if (EX h: list answer, EX st: Z, EX w: option Z, EX rec: Z,
    PROP (returns x h = Some (st, w); rec_ok x st w rec; u32_ok rec)
    LOCAL (temp _status (vi st); temp _prior (vi (i_prior x)); temp _madt madt; temp _m (gv _law);
           lvar _id tuint vid; gvars gv)
    SEP (Ora_law gv x h; data_at Ews (tarray tuchar (i_length x)) (bytes_val (i_bytes x)) madt;
         data_at Tsh tuint (vi rec) vid; TT)).
  - (* the envelope *)
    u64c. assert (C: i_call x = FEnvelope) by (apply call_code_0; auto).
    forward.
    sep_apply (lfields_fold (gv _law) cp x (i_args x) (ls_expect s0) (ls_verdict s0) (ls_at s0) (ls_word s0)
                 (ls_state s0) (ls_answer s0) (ls_id s0)).
    rewrite E0. sep_apply (ora_intro gv x cp s0 Hx Hs HJ).
    rewrite (data_at_tuchar_cs LCS MgaSpecs.CS Ews (i_length x) (bytes_val (i_bytes x)) madt).
    forward_call (gv, x, madt, Ews).
    Intros vret. destruct vret as [h st]. simpl fst in *; simpl snd in *.
    forward.
    rewrite <- (data_at_tuchar_cs LCS MgaSpecs.CS Ews (i_length x) (bytes_val (i_bytes x)) madt).
    Exists h st (@None Z) (i_prior x). entailer!.
    unfold rec_ok. rewrite C. simpl. rewrite andb_false_r. reflexivity.
  - u64c. forward. forward_if.
    + (* the entries *)
      u64c. assert (C: i_call x = FEntries) by (apply call_code_1; auto).
      forward. forward.
      sep_apply (lfields_fold (gv _law) cp x (i_args x) (ls_expect s0) (ls_verdict s0) (ls_at s0) (ls_word s0)
                   (ls_state s0) (ls_answer s0) (ls_id s0)).
      rewrite E0. sep_apply (ora_intro gv x cp s0 Hx Hs HJ).
      rewrite (data_at_tuchar_cs LCS MgaSpecs.CS Ews (i_length x) (bytes_val (i_bytes x)) madt).
      rewrite (data_at_tuint_cs LCS MgaSpecs.CS Tsh (vi (i_prior x)) vid).
      forward_call (gv, x, madt, Ews, vid, Tsh).
      Intros vret. destruct vret as [[h st] id]. simpl fst in *; simpl snd in *.
      forward.
      rewrite <- (data_at_tuchar_cs LCS MgaSpecs.CS Ews (i_length x) (bytes_val (i_bytes x)) madt).
      rewrite <- (data_at_tuint_cs LCS MgaSpecs.CS Tsh _ vid).
      Exists h st (if st =? S_OK then Some id else None) (if st =? S_OK then id else i_prior x). entailer!.
      unfold rec_ok. rewrite C. simpl. rewrite andb_true_r. split; destruct (st =? S_OK); auto.
    + u64c. forward. forward_if.
      * (* the result *)
        u64c. assert (C: i_call x = FResult) by (apply call_code_2; auto).
        forward. forward. forward. forward. forward. forward. forward. forward. forward. forward.
        sep_apply (lfields_fold (gv _law) cp x (i_args x) (ls_expect s0) (ls_verdict s0) (ls_at s0) (ls_word s0)
                     (ls_state s0) (ls_answer s0) (ls_id s0)).
        rewrite E0. sep_apply (ora_intro gv x cp s0 Hx Hs HJ).
        rewrite (data_at_tuint_cs LCS MgaSpecs.CS Tsh (vi (i_prior x)) vid).
        forward_call (gv, x, vid, Tsh).
        Intros vret. destruct vret as [[h st] id]. simpl fst in *; simpl snd in *.
        forward.
        rewrite <- (data_at_tuint_cs LCS MgaSpecs.CS Tsh _ vid).
        Exists h st (if st =? S_OK then Some id else None) (if st =? S_OK then id else i_prior x). entailer!.
        unfold rec_ok. rewrite C. simpl. rewrite andb_true_r. split; destruct (st =? S_OK); auto.
      * (* the admission *)
        u64c. assert (C: i_call x = FAdmission) by (destruct (i_call x); simpl in *; congruence || lia).
        forward. forward. forward. forward. forward. forward. forward.
        sep_apply (lfields_fold (gv _law) cp x (i_args x) (ls_expect s0) (ls_verdict s0) (ls_at s0) (ls_word s0)
                     (ls_state s0) (ls_answer s0) (ls_id s0)).
        rewrite E0. sep_apply (ora_intro gv x cp s0 Hx Hs HJ).
        rewrite (data_at_tuchar_cs LCS MgaSpecs.CS Ews (i_length x) (bytes_val (i_bytes x)) madt).
        rewrite (data_at_tuint_cs LCS MgaSpecs.CS Tsh (vi (i_prior x)) vid).
        forward_call (gv, x, madt, Ews, vid, Tsh).
        Intros vret. destruct vret as [[h st] id]. simpl fst in *; simpl snd in *.
        forward.
        rewrite <- (data_at_tuchar_cs LCS MgaSpecs.CS Ews (i_length x) (bytes_val (i_bytes x)) madt).
        rewrite <- (data_at_tuint_cs LCS MgaSpecs.CS Tsh _ vid).
        Exists h st (if st =? S_OK then Some id else None) (if st =? S_OK then id else i_prior x). entailer!.
        unfold rec_ok. rewrite C. simpl. rewrite andb_true_r. split; destruct (st =? S_OK); auto.
  - Intros h st w rec.
    eapply semax_pre; [ | apply (tail_check gv madt vid x h st w rec); first [ reflexivity | assumption | auto ] ].
    entailer!.
Qed.
