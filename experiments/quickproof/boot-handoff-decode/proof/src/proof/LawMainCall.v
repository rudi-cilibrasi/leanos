(* Law handoff_decode_exact: main's call of the function it chose: the law's oracle handed over at no answers, the
   allocation's two calls (handoff_extent, then handoff_project when it returns OK), a copy, a projection or a
   candidate alone; then the checks (check_ok).  main's objects are under the law's compspecs and the callees'
   specifications under the unit's: VST's cancel converts between the two (change_composite_env both ways). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosHandoff.harness.handoff_decode_exact.code.
Require Import LeanosHandoff.proof.Defs.
Require Import LeanosHandoff.proof.HandoffSpecs.
Require Import LeanosHandoff.proof.LawProg LeanosHandoff.proof.LawDefs LeanosHandoff.proof.LawFacts
  LeanosHandoff.proof.LawLib LeanosHandoff.proof.LawLib2 LeanosHandoff.proof.LawZero
  LeanosHandoff.proof.LawMainDefs LeanosHandoff.proof.LawMainPre LeanosHandoff.proof.LawMainPre2
  LeanosHandoff.proof.LawMainPre3.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[local] Existing Instance LawProg.LCS.

#[local] Instance LCR' : change_composite_env LCS HandoffSpecs.CS.
Proof. make_cs_preserve LCS HandoffSpecs.CS. Defined.

Lemma ora_at: forall gv x h p s ce ie, inputs_ok x -> x_fit x -> run x (start x) h = Some p -> J x p s ->
  ptr_ok x ce ie ->
  (lfields (gv _law) x ce ie (mem_of p) s * arrays x ce ie (mem_of p))%logic |-- Ora_law gv (gv _law) (gv _law) x h.
Proof. intros. unfold Ora_law. Exists p s ce ie. entailer!. Qed.

Lemma J_running: forall x p s, J x p s ->
  J x p (mk_lst 1 (w_records s) (w_expect s) (w_verdict s) (w_chunk s) (w_word s) (w_block s) (w_value s)
           (w_stream s) (w_answer s)).
Proof.
  intros x p s (L & F & G). split; [ | split; [ exact F | exact G ] ].
  destruct L as (L1 & L2). split; [ unfold u32_ok; cbn; rep_lia | exact L2 ].
Qed.

Lemma total_start: forall x, m_total (mem_of (start x)) = i_total x.
Proof.
  intros. unfold start, begin_decode. destruct (i_call x); try reflexivity.
  - destruct (_ =? _); reflexivity.
  - destruct (projection x); reflexivity.
  - destruct (projection x); reflexivity.
Qed.

Lemma has_copy_true: forall x, i_call x = FAllocate \/ i_call x = FCopy -> has_copy x = true.
Proof. intros x [C | C]; unfold has_copy; rewrite C; reflexivity. Qed.

Lemma has_copy_false: forall x, i_call x = FProjection \/ i_call x = FCandidate -> has_copy x = false.
Proof. intros x [C | C]; unfold has_copy; rewrite C; reflexivity. Qed.

Lemma i_copy_xm: forall x cep iep, has_copy x = true -> i_copy (xm x cep iep) = i_copy x.
Proof. intros x cep iep H. unfold xm; cbn [i_copy]. rewrite H. reflexivity. Qed.

Lemma i_info_xm: forall x cep iep, has_copy x = false -> i_info (xm x cep iep) = i_info x.
Proof. intros x cep iep H. unfold xm; cbn [i_info]. rewrite H. reflexivity. Qed.

Lemma initial_xm: forall x cep iep, initial (xm x cep iep) =
  mk_mem (i_total x) false (if has_copy x then i_copy x else enc_ptr iep) (i_usable x) (i_blocked x)
    (i_reserved x) (i_states x) 0.
Proof. reflexivity. Qed.

Lemma ora_unfold: forall gv ctx rctx x h, Ora_law gv ctx rctx x h =
  (EX p: progress, EX s: lst, EX ce: val, EX ie: val,
    !! (ctx = gv _law /\ rctx = gv _law /\ inputs_ok x /\ x_fit x /\ run x (start x) h = Some p /\ J x p s /\
        ptr_ok x ce ie) &&
    (lfields (gv _law) x ce ie (mem_of p) s * arrays x ce ie (mem_of p)))%logic.
Proof. reflexivity. Qed.

Lemma status_range: forall st, status_ok st -> 0 <= st <= Int.max_unsigned.
Proof. intros st H. unfold status_ok, S_AUTHORITY_REJECTED_TARGET in H. rep_lia. Qed.

Lemma if_ok: forall {A} (a b: A), (if S_OK =? S_OK then a else b) = a.
Proof. reflexivity. Qed.

Lemma out_tot_noext: forall x cep iep m, m_extent_ok m = false ->
  out_total_record (xm x cep iep) m = i_total_record x.
Proof. intros x cep iep m E. unfold out_total_record. rewrite E. reflexivity. Qed.

Lemma out_len_ncopy: forall x cep iep st m, i_call x <> FCopy ->
  out_length_record (xm x cep iep) st m = i_length_record x.
Proof.
  intros x cep iep st m N. unfold out_length_record, is_copy. cbn [xm i_call].
  destruct (i_call x); try reflexivity. contradiction.
Qed.

Lemma out_len_nok: forall x cep iep st m, st <> S_OK ->
  out_length_record (xm x cep iep) st m = i_length_record x.
Proof.
  intros x cep iep st m N. unfold out_length_record. rewrite (proj2 (Z.eqb_neq st S_OK) N), andb_false_r.
  reflexivity.
Qed.

Lemma out_cur_copy: forall x cep iep st m, i_call x = FCopy ->
  out_current_record (xm x cep iep) st m = i_current_record x.
Proof. intros x cep iep st m C. unfold out_current_record, is_copy. cbn [xm i_call]. rewrite C. reflexivity. Qed.

Lemma out_cur_nok: forall x cep iep st m, st <> S_OK ->
  out_current_record (xm x cep iep) st m = i_current_record x.
Proof.
  intros x cep iep st m N. unfold out_current_record. rewrite (proj2 (Z.eqb_neq st S_OK) N), andb_false_r.
  reflexivity.
Qed.

Lemma target_cand: forall x cep iep, i_call x = FCandidate -> target (xm x cep iep) = i_candidate (xm x cep iep).
Proof. intros x cep iep C. unfold target. cbn [xm i_call]. rewrite C. reflexivity. Qed.

(* The law's fields refolded, and the oracle at the answers h. *)
Ltac fold_ora gv x cep iep h p s ce ie Ix Xf Hr HJ Po :=
  sep_apply (lfields_fold (gv _law) (xm x cep iep) ce ie (mem_of p) s);
  sep_apply (ora_at gv (xm x cep iep) h p s ce ie Ix Xf Hr HJ Po).

(* The callee's objects back under the law's compspecs. *)
Ltac of_cs :=
  rewrite <- ?data_at_tuint_cs, <- ?data_at_words_cs, <- ?data_at_states_cs, <- ?data_at_projection_cs.

(* A call's results named. *)
Ltac call_res h st m :=
  let v := fresh "vret" in Intros v; destruct v as [[h st] m]; cbn [fst snd] in *.

Lemma tail_call {Espec: OracleKind} (TK: @check_ok Espec): @call_ok Espec.
Proof.
  intros gv x s0 cp cep ip iep up bp rp sp vtr vlr vcr vpj Ix Xf Po Fx Ext HJ Pcp Pcep Pip Piep Pup Pbp Prp Psp.
  unfold call_pre, s_call, proj_val. start_tail_main.
  pose proof (J_running _ _ _ HJ) as HJ1.
  set (s1 := mk_lst 1 (w_records s0) (w_expect s0) (w_verdict s0) (w_chunk s0) (w_word s0) (w_block s0)
                    (w_value s0) (w_stream s0) (w_answer s0)) in HJ1.
  pose proof (call_code_range (i_call x)) as Rc.
  pose proof Fx as (F1 & F2 & F3 & F4 & _).
  make_func_ptr _bootloader_read. make_func_ptr _projection_record.
  unfold lfields. Intros.
  assert_PROP (isptr (gv _law)) as Plaw by entailer!.
  assert (Pnl: is_pointer_or_null (gv _law)) by (destruct (gv _law); try contradiction; simpl; auto).
  change (i_call (xm x cep iep)) with (i_call x).
  forward.
  forward.
  forward_if ((EX h: list answer, EX st: Z, EX m: mem,
    PROP (returns (xm x cep iep) h = Some (st, m))
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
         data_at Tsh t_projection (gv _projection_record, (gv _law, (up, (bp, rp)))) vpj; TT))%assert).
  { (* an allocation: handoff_extent, then handoff_project on OK *)
    assert (C: i_call x = FAllocate) by (u64c; apply call_code_inj; assumption).
    assert (Hc: has_copy x = true) by (apply has_copy_true; auto).
    assert (Ecl: copy_len x = COPY_WORDS) by (unfold copy_len; rewrite C; reflexivity).
    forward. forward.
    fold_ora gv x cep iep (@nil answer) (start (xm x cep iep)) s1 cep (ie_of x cep iep) Ix Xf (@eq_refl _ (Some (start (xm x cep iep)))) HJ1 Po.
    forward_call (gv, gv _bootloader_read, gv _law, gv _law, xm x cep iep, vtr, Tsh).
    call_res h st T.
    match goal with H: run _ _ h = Some (extent_end _ _ _) |- _ => rename H into Hr0 end.
    match goal with H: status_ok st |- _ => rename H into Sok end.
    match goal with H: st = S_OK -> extent_fits T |- _ => rename H into ExT end.
    pose proof (status_range st Sok) as Rst.
    of_cs.
    forward.
    forward_if.
    { (* OK: the second call *)
      assert (E0: st = S_OK) by (u64c; auto). subst st. rewrite if_ok.
      specialize (ExT eq_refl).
      change (extent_end (xm x cep iep) S_OK T) with (after_extent (xm x cep iep) T) in Hr0.
      rewrite (ora_unfold gv (gv _law) (gv _law) (xm x cep iep) h). Intros p s ce ie.
      match goal with H: run _ _ h = Some p |- _ => rename H into Hr end.
      match goal with H: J _ p s |- _ => rename H into HJp end.
      match goal with H: ptr_ok _ ce ie |- _ => rename H into Pp end.
      unfold lfields. Intros.
      forward. forward. forward.
      fold_ora gv x cep iep h p s ce ie Ix Xf Hr HJp Pp.
      assert (Lc: Zlength (i_copy (xm x cep iep)) = COPY_WORDS) by (rewrite i_copy_xm by auto; rewrite F1; auto).
      rewrite Ecl, <- (i_copy_xm x cep iep Hc).
      forward_call (gv, gv _bootloader_read, gv _law, gv _law, gv _projection_record, xm x cep iep, h, T,
                    cp, Ews, vpj, Tsh, up, bp, rp, Ews, sp, Ews, vcr, Tsh).
      call_res h' st' m.
      match goal with H: keeps _ _ m |- _ => rename H into K end.
      of_cs. rewrite <- Ecl.
      forward.
      assert (Ot: out_total_record (xm x cep iep) m = T)
        by (destruct K as (K1 & K2 & _); unfold out_total_record; rewrite K2, K1; reflexivity).
      Exists h' st' m. rewrite Hc, Ot. rewrite out_len_ncopy by (rewrite C; discriminate).
      entailer!. }
    { (* the extent rejected: the return *)
      forward.
      assert (N: st <> S_OK) by (unfold S_OK; u64c; auto).
      assert (Eqf: (st =? S_OK) = false) by (apply Z.eqb_neq; auto).
      assert (Et: (if st =? S_OK then T else i_total_record (xm x cep iep)) = i_total_record x)
        by (rewrite Eqf; reflexivity).
      rewrite Et.
      Exists h st (initial (xm x cep iep)).
      rewrite Hc, initial_xm, Hc. cbn [m_copy m_usable m_blocked m_reserved m_states].
      rewrite out_tot_noext by reflexivity. rewrite out_len_ncopy by (rewrite C; discriminate).
      rewrite out_cur_nok by exact N.
      entailer!.
      unfold returns. rewrite Hr0. unfold extent_end. rewrite Eqf, initial_xm, Hc. reflexivity. } }
  { (* not an allocation *)
    forward.
    forward_if.
    { (* a copy alone *)
      assert (C: i_call x = FCopy) by (u64c; apply call_code_inj; assumption).
      assert (Hc: has_copy x = true) by (apply has_copy_true; auto).
      assert (Ecl: copy_len x = COPY_WORDS) by (unfold copy_len; rewrite C; reflexivity).
      assert (Ex: extent_fits (i_total (xm x cep iep))) by (apply Ext; congruence).
      assert (Lc: Zlength (i_copy (xm x cep iep)) = COPY_WORDS) by (rewrite i_copy_xm by auto; rewrite F1; auto).
      forward. forward. forward.
      fold_ora gv x cep iep (@nil answer) (start (xm x cep iep)) s1 cep (ie_of x cep iep) Ix Xf (@eq_refl _ (Some (start (xm x cep iep)))) HJ1 Po.
      rewrite total_start.
      rewrite Ecl, <- (i_copy_xm x cep iep Hc).
      forward_call (gv, gv _bootloader_read, gv _law, gv _law, xm x cep iep, cp, Ews, vlr, Tsh).
      call_res h st m.
      match goal with H: keeps _ _ m |- _ => rename H into K end.
      of_cs. rewrite <- Ecl.
      forward.
      unfold keeps in K. cbn [i_call xm] in K. rewrite C in K.
      destruct K as (K1 & K2 & Ku & Kb & Kr & Ks & Ka).
      rewrite initial_xm in K2, Ku, Kb, Kr, Ks. cbn [m_extent_ok m_usable m_blocked m_reserved m_states] in K2, Ku, Kb, Kr, Ks.
      Exists h st m. rewrite Hc, Ku, Kb, Kr, Ks.
      rewrite out_tot_noext by auto. rewrite out_cur_copy by auto.
      entailer!. }
    forward.
    forward_if.
    { (* a projection alone *)
      assert (C: i_call x = FProjection) by (u64c; apply call_code_inj; assumption).
      assert (Hc: has_copy x = false) by (apply has_copy_false; auto).
      assert (Eil: info_len x = i_total (xm x cep iep) / 8) by (unfold info_len, is_alloc; rewrite C; reflexivity).
      assert (Ex: extent_fits (i_total (xm x cep iep))) by (apply Ext; congruence).
      assert (Li: Zlength (i_info (xm x cep iep)) = i_total (xm x cep iep) / 8)
        by (rewrite i_info_xm by auto; rewrite F3; auto).
      forward. forward. forward.
      fold_ora gv x cep iep (@nil answer) (start (xm x cep iep)) s1 cep (ie_of x cep iep) Ix Xf (@eq_refl _ (Some (start (xm x cep iep)))) HJ1 Po.
      rewrite total_start.
      rewrite Eil, <- (i_info_xm x cep iep Hc).
      forward_call (gv, gv _law, gv _law, gv _projection_record, xm x cep iep, ip, Ews, vpj, Tsh, up, bp, rp, Ews,
                    sp, Ews, vcr, Tsh).
      call_res h st m.
      match goal with H: keeps _ _ m |- _ => rename H into K end.
      of_cs. rewrite (i_info_xm x cep iep Hc), <- Eil.
      forward.
      unfold keeps in K. cbn [i_call xm] in K. rewrite C in K.
      destruct K as (K1 & K2 & Kc).
      rewrite initial_xm in K2. cbn [m_extent_ok] in K2.
      Exists h st m. rewrite Hc.
      rewrite out_tot_noext by auto. rewrite out_len_ncopy by (rewrite C; discriminate).
      entailer!. }
    { (* a candidate alone *)
      assert (C: i_call x = FCandidate)
        by (u64c; apply call_code_inj; change (call_code FCandidate) with 3; lia).
      assert (Hc: has_copy x = false) by (apply has_copy_false; auto).
      assert (Eil: info_len x = i_total (xm x cep iep) / 8) by (unfold info_len, is_alloc; rewrite C; reflexivity).
      assert (Ex: extent_fits (i_total (xm x cep iep))) by (apply Ext; congruence).
      assert (Li: Zlength (i_info (xm x cep iep)) = i_total (xm x cep iep) / 8)
        by (rewrite i_info_xm by auto; rewrite F3; auto).
      forward. forward. forward. forward.
      fold_ora gv x cep iep (@nil answer) (start (xm x cep iep)) s1 cep (ie_of x cep iep) Ix Xf (@eq_refl _ (Some (start (xm x cep iep)))) HJ1 Po.
      rewrite total_start, (target_cand x cep iep C).
      rewrite Eil, <- (i_info_xm x cep iep Hc).
      forward_call (gv, gv _law, gv _law, xm x cep iep, ip, Ews, sp, Ews, vcr, Tsh).
      call_res h st m.
      match goal with H: keeps _ _ m |- _ => rename H into K end.
      of_cs. rewrite (i_info_xm x cep iep Hc), <- Eil.
      forward.
      unfold keeps in K. cbn [i_call xm] in K. rewrite C in K.
      destruct K as (K1 & K2 & Kc & Ku & Kb & Kr).
      rewrite initial_xm in K2, Ku, Kb, Kr. cbn [m_extent_ok m_usable m_blocked m_reserved] in K2, Ku, Kb, Kr.
      Exists h st m. rewrite Hc, Ku, Kb, Kr.
      rewrite out_tot_noext by auto. rewrite out_len_ncopy by (rewrite C; discriminate).
      entailer!. } }
  Intros h st m.
  eapply semax_pre; [ | apply (TK gv x h st m cp cep ip iep up bp rp sp vtr vlr vcr vpj); auto ].
  unfold check_pre. entailer!.
Qed.
