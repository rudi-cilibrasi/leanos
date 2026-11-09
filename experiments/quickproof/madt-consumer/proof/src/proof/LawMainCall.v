(* Law consumer_obligations: main's call of madt_bind: the span split between the law's oracle and the consumer,
   the arguments that may be NULL, the oracle handed over exactly on a valid call. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosMadt.harness.consumer_obligations.code.
Require Import LeanosMadt.proof.Defs.
Require Import LeanosMadt.proof.MadtSpecs.
Require Import LeanosMadt.proof.LawProg LeanosMadt.proof.LawDefs LeanosMadt.proof.LawFacts LeanosMadt.proof.LawLib
  LeanosMadt.proof.LawSplit LeanosMadt.proof.LawMainLib LeanosMadt.proof.LawMainDefs.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.
Require Import LeanosMadt.proof.LawTailInvalid LeanosMadt.proof.LawTailValid.

Lemma if_same: forall {A: Type} (b: bool) (x: A), (if b then x else x) = x.
Proof. intros A [ ] x; reflexivity. Qed.

Lemma tail_call {Espec: OracleKind} gv q v_out v_observation n bs ob c m (eb obb qb: bool):
  0 <= n <= Int64.max_unsigned -> isptr q -> isptr v_out -> isptr v_observation ->
  Zlength bs = (if length_ok n then n else 1) -> 0 < Zlength bs -> Forall byte_ok bs -> obs_ok ob ->
  u64_ok c -> Zlength m = 4 -> Forall u64_ok m ->
  (length_ok n = true -> match records bs with Some (c', m') => c = c' /\ m = m' | None => True end) ->
  forall Delta R c', Delta = Delta0 -> R = Post0 -> c' = s_call ->
  semax Delta
    (PROP ()
     LOCAL (temp _walk (Vint (Int.repr (if length_ok n then (if walk_b bs then 1 else 0) else 0)));
            temp _out_arg (sel qb v_out); temp _observation_arg (sel obb v_observation);
            temp _entries_arg (sel eb q); temp _valid_length (Vint (Int.repr (Z.b2z (length_ok n))));
            temp _length (Vlong (Int64.repr n)); temp _o (gv _oracle);
            lvar _out t_result v_out; lvar _observation t_obs v_observation; gvars gv)
     SEP (ofields (gv _oracle) q n ob (s_main (negb qb && negb eb && negb obb && length_ok n)%bool c m);
          data_at Ews (tarray tuchar (Zlength bs)) (bytes_val bs) q;
          @data_at LCS Tsh t_result (vl 7, (vl 7, (vl 7, (vl 7, (vl 7, vl 7))))) v_out;
          @data_at LCS Tsh t_obs (obs_val ob) v_observation; TT))
    c' R.
Proof.
  intros Hn Pq Po Pob Lbs Lb0 Hby Hob Hc Lm Fm Hrec Delta R c' -> -> ->.
  unfold s_call. start_tail.
  rewrite (span_split (Zlength bs) (bytes_val bs) q).
  rewrite (data_at_tuchar_cs LCS MadtSpecs.CS sh2 (Zlength bs) (bytes_val bs) q).
  sep_apply (maybe_split eb sh2 (tarray tuchar (Zlength bs)) (bytes_val bs) q Pq).
  rewrite (obs_cs Tsh (obs_val ob) v_observation).
  sep_apply (maybe_split obb Tsh t_obs (obs_val ob) v_observation Pob).
  rewrite (result_cs Tsh (vl 7, (vl 7, (vl 7, (vl 7, (vl 7, vl 7))))) v_out).
  sep_apply (maybe_split qb Tsh t_result (vl 7, (vl 7, (vl 7, (vl 7, (vl 7, vl 7))))) v_out Po).
  set (rold := (vl 7, (vl 7, (vl 7, (vl 7, (vl 7, vl 7)))))).
  destruct (invalid_call (sel eb q) (sel obb v_observation) (sel qb v_out) n) eqn:Inv.
  - (* invalid arguments: the oracle stays main's *)
    sep_apply (add_emp_if (invalid_call (sel eb q) (sel obb v_observation) (sel qb v_out) n)
                 (Ora_law gv (bs, ob) nil) TT Inv).
    forward_call (gv, sel eb q, sh2, bs, n, sel obb v_observation, Tsh, ob, sel qb v_out, rold).
    { cancel. }
    { repeat split; auto; try apply sh2_readable; try apply sel_ptr; auto.
      intros E. rewrite Lbs, E. reflexivity. }
    Intros vret. destruct vret as [h o]. simpl fst in *; simpl snd in *.
    rewrite Inv in *. match goal with E: _ /\ _ |- _ => destruct E as [-> ->] end.
    sep_apply (maybe_join qb Tsh t_result rold (result_val (reject 1 0 44)) v_out Po).
    sep_apply (maybe_join obb Tsh t_obs (obs_val ob) (obs_val ob) v_observation Pob).
    rewrite if_same.
    rewrite <- (result_cs Tsh), <- (obs_cs Tsh).
    eapply semax_pre;
      [ | apply (tail_invalid gv q v_out v_observation n ob (s_main (negb qb && negb eb && negb obb && length_ok n) c m)
                   eb obb qb (Zlength bs) (bytes_val bs));
          auto; first [ reflexivity | rewrite <- (invalid_sel eb obb qb q v_observation v_out n); auto ] ].
    entailer!.
  - (* valid arguments: the law's oracle handed over *)
    assert (V: (qb || eb || obb || negb (length_ok n))%bool = false)
      by (rewrite <- (invalid_sel eb obb qb q v_observation v_out n); auto).
    repeat rewrite orb_false_iff in V. destruct V as [[[Vq Ve] Vo] Vl]. apply negb_false_iff in Vl.
    subst qb eb obb.
    assert (Zbn: Zlength bs = n) by (rewrite Lbs, Vl; reflexivity).
    rewrite Vl. cbn [negb andb]. rewrite <- Zbn.
    assert (L2: length_ok (Zlength bs) = true) by (rewrite Zbn; auto).
    assert (Ost: ost_ok (s_main true c m)) by (apply ost_ok_main; auto).
    assert (Nmi: nmi_ok bs (s_main true c m)) by (apply nmi_ok_main; apply Hrec; exact Vl).
    sep_apply (ora_intro gv bs ob q sh1 (s_main true c m) sh1_readable L2 Hby Hob Ost Nmi
                 eq_refl eq_refl eq_refl eq_refl eq_refl).
    sep_apply (to_if_false (invalid_call (sel false q) (sel false v_observation) (sel false v_out) (Zlength bs))
                 (Ora_law gv (bs, ob) nil)).
    { rewrite Zbn; auto. }
    forward_call (gv, sel false q, sh2, bs, Zlength bs, sel false v_observation, Tsh, ob, sel false v_out, rold).
    { repeat split; auto; try apply sh2_readable; try apply sel_ptr; auto; rep_lia. }
    Intros vret. destruct vret as [h o]. simpl fst in *; simpl snd in *.
    rewrite Zbn. rewrite Inv.
    match goal with E: (if invalid_call _ _ _ _ then _ else _) |- _ => rewrite Zbn, Inv in E end.
    sep_apply (maybe_join false Tsh t_result rold (result_val o) v_out Po).
    sep_apply (maybe_join false Tsh t_obs (obs_val ob) (obs_val ob) v_observation Pob).
    sep_apply (maybe_join false sh2 (tarray tuchar n) (bytes_val bs) (bytes_val bs) q Pq).
    rewrite <- (result_cs Tsh), <- (obs_cs Tsh).
    eapply semax_pre;
      [ | apply (tail_valid gv q v_out v_observation n bs ob h o); auto; first [ reflexivity | auto ] ].
    rewrite <- Zbn. unfold sel. entailer!.
Qed.
