(* Law handoff_decode_exact: the body of the harness's main up to the fills of the storage: the law's call, magic,
   address, extent and candidate, the return for an extent a call alone does not take, the candidate and projection
   of the call, the eight mallocs and the return when one fails; the rest is the tail lemmas (fill_ok, LawMainFill
   and on). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosHandoff.harness.handoff_decode_exact.code.
Require Import LeanosHandoff.proof.Defs.
Require Import LeanosHandoff.proof.HandoffSpecs.
Require Import LeanosHandoff.proof.LawProg LeanosHandoff.proof.LawDefs LeanosHandoff.proof.LawFacts
  LeanosHandoff.proof.LawLib LeanosHandoff.proof.LawLib2 LeanosHandoff.proof.LawZero
  LeanosHandoff.proof.LawMainDefs LeanosHandoff.proof.LawMainPre.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[local] Existing Instance LawProg.LCS.

(* Freeze the law's fields (main's other SEP items stay). *)
Ltac keep_nf x :=
  lazymatch x with
  | field_at _ _ (StructField _ :: nil) _ _ => constr:(false)
  | _ => constr:(true)
  end.
Ltac idx_nf R i :=
  lazymatch R with
  | nil => constr:(@nil Z)
  | ?x :: ?R' =>
      let rest := idx_nf R' (Z.succ i) in
      let k := keep_nf x in
      lazymatch k with true => rest | false => let i' := eval cbn in i in constr:(i' :: rest) end
  end.
Ltac freeze_fields F :=
  match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
    let I := idx_nf R 0 in freeze_tac I F
  end.

Lemma modu4: forall c, 0 <= c <= Int.max_unsigned -> Int.modu (Int.repr c) (Int.repr 4) = Int.repr (c mod 4).
Proof. intros. unfold Int.modu. rewrite !Int.unsigned_repr by rep_lia. reflexivity. Qed.

Lemma and7': forall T, 0 <= T <= Int.max_unsigned -> Int.and (Int.repr T) (Int.repr 7) = Int.repr (T mod 8).
Proof.
  intros T R. unfold Int.and. rewrite !Int.unsigned_repr by rep_lia.
  change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma proj_code_x0: forall cc mg ad tt cd, 0 <= cc <= 3 ->
  Z.b2z ((cc =? 0) || (cc =? 2)) = proj_code (x0 cc mg ad tt cd).
Proof.
  intros. unfold proj_code, projection, x0, call_of; cbn [i_call].
  assert (cc = 0 \/ cc = 1 \/ cc = 2 \/ cc = 3) as [-> | [-> | [-> | ->]]] by lia; reflexivity.
Qed.

Lemma copy_len_x0: forall cc mg ad tt cd, 0 <= cc <= 3 ->
  copy_len (x0 cc mg ad tt cd) = if (cc =? 0) || (cc =? 1) then 8192 else 0.
Proof.
  intros. unfold copy_len, x0, call_of; cbn [i_call].
  assert (cc = 0 \/ cc = 1 \/ cc = 2 \/ cc = 3) as [-> | [-> | [-> | ->]]] by lia; reflexivity.
Qed.

Lemma info_len_x0: forall cc mg ad tt cd, 0 <= cc <= 3 ->
  info_len (x0 cc mg ad tt cd) = if cc =? 0 then 0 else tt / 8.
Proof.
  intros. unfold info_len, is_alloc, x0, call_of; cbn [i_call i_total].
  assert (cc = 0 \/ cc = 1 \/ cc = 2 \/ cc = 3) as [-> | [-> | [-> | ->]]] by lia; reflexivity.
Qed.

Lemma target_x0: forall cc mg ad tt cd, 0 <= cc <= 3 ->
  target (x0 cc mg ad tt cd) = if cc =? 3 then cd else 0.
Proof.
  intros. unfold target, x0, call_of; cbn [i_call i_candidate].
  assert (cc = 0 \/ cc = 1 \/ cc = 2 \/ cc = 3) as [-> | [-> | [-> | ->]]] by lia; reflexivity.
Qed.

Lemma drop_TT: forall P: mpred, (P * TT)%logic |-- TT.
Proof. intros. apply TT_right. Qed.

Lemma body_main (TM: forall Espec: OracleKind, @malloc_ok Espec): forall p, QPprog_vars p = [(_law, v_law)] ->
  semax_body Vlaw Gmain f_main (_main, main_spec_std p).
Proof.
  intros p Hp. start_function. rewrite Hp.
  assert_PROP (headptr (gv _law)) as HP by entailer!.
  sep_apply (law_zero gv HP).
  sep_apply (create_mem_mgr gv).
  unfold lraw. Intros.
  forward.
  forward_call tt. Intros c. forward.
  forward_call tt. Intros mg. forward.
  forward_call tt. Intros ad. forward.
  forward_call tt. Intros tt0. forward.
  forward_call tt. Intros cd. forward.
  rewrite modu4 by rep_lia.
  set (cc := c mod 4).
  assert (Rcc: 0 <= cc <= 3) by (unfold cc; pose proof (Z.mod_pos_bound c 4 ltac:(lia)); lia).
  clearbody cc.
  (* an extent a call alone does not take: return *)
  forward.
  forward_if (temp _t'6 (Vint (Int.repr (Z.b2z (negb (cc =? 0) && ((65536 <? tt0) || negb (tt0 mod 8 =? 0))))))).
  { forward.
    assert (Nc0: cc <> 0) by (u64c; lia).
    forward_if.
    { forward. entailer!. rewrite (proj2 (Z.eqb_neq _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
      reflexivity. }
    { forward. forward. forward. entailer!.
      replace (Z.land tt0 7) with (tt0 mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
      rewrite (proj2 (Z.eqb_neq cc 0)) by lia. rewrite (proj2 (Z.ltb_ge 65536 tt0)) by lia. cbn [orb negb andb].
      pose proof (Z.mod_pos_bound tt0 8 ltac:(lia)).
      rewrite Int_eq_repr by rep_lia. destruct (tt0 mod 8 =? 0); reflexivity. } }
  { forward. entailer!. }
  forward_if.
  { forward. Exists (Int.repr 0). entailer!. }
  match goal with
  | H: (negb (cc =? 0) && _) = false |- _ => rename H into E6
  | H: Int.repr (Z.b2z _) = _ |- _ => apply b2z_false in H; rename H into E6
  end.
  assert (Ext: cc <> 0 -> extent_fits tt0).
  { intros N. rewrite (proj2 (Z.eqb_neq _ _) N) in E6. cbn [negb andb] in E6.
    apply orb_false_iff in E6 as [E6a E6b]. apply Z.ltb_ge in E6a. apply negb_false_iff, Z.eqb_eq in E6b.
    split; [ lia | auto ]. }
  clear E6.
  set (X := x0 cc mg ad tt0 cd).
  (* the candidate *)
  forward.
  freeze_but [_candidate] (@nil val) FA.
  forward_if (PROP () LOCAL (temp _m (gv _law); lvar _projection t_projection v_projection;
                             lvar _current_record tuint v_current_record; lvar _length_record tuint v_length_record;
                             lvar _total_record tuint v_total_record; gvars gv)
              SEP (FRZL FA; field_at Ews t_law (DOT _candidate) (vl (target X)) (gv _law))).
  { forward. entailer!; try (unfold X; rewrite target_x0 by lia; u64c; rewrite (proj2 (Z.eqb_neq _ _)) by lia;
    apply derives_refl). }
  { forward. entailer!; try (unfold X; rewrite target_x0 by lia; u64c; subst; apply derives_refl). }
  thaw FA.
  (* the projection *)
  forward.
  forward_if (temp _t'7 (Vint (Int.repr (Z.b2z ((cc =? 0) || (cc =? 2)))))).
  { forward. entailer!; try (u64c; subst; reflexivity). }
  { forward. forward. entailer!; try (u64c; rewrite (proj2 (Z.eqb_neq _ _)) by lia; cbn [orb]; cmp_close). }
  forward.
  rewrite (proj_code_x0 cc mg ad tt0 cd Rcc). fold X.
  (* the copy's words *)
  forward.
  forward_if (temp _t'8 (Vint (Int.repr (Z.b2z ((cc =? 0) || (cc =? 1)))))).
  { forward. entailer!; try (u64c; subst; reflexivity). }
  { forward. forward. entailer!; try (u64c; rewrite (proj2 (Z.eqb_neq _ _)) by lia; cbn [orb]; cmp_close). }
  forward_if (temp _t'9 (vi (copy_len X))).
  { forward. entailer!; try (unfold X; rewrite copy_len_x0 by lia; try b2z_hyp; rw_bools; reflexivity). }
  { forward. entailer!; try (unfold X; rewrite copy_len_x0 by lia; try b2z_hyp; rw_bools; reflexivity). }
  forward.
  assert (Rcl: copy_len X = 0 \/ copy_len X = 8192)
    by (unfold X; rewrite copy_len_x0 by lia; destruct (_ || _); auto).
  (* the mallocs and on *)
  sep_apply (drop_TT (has_ext tt)).
  eapply semax_pre; [ | apply (TM _ gv cc mg ad tt0 cd v_total_record v_length_record v_current_record v_projection);
                        unfold x0_ok; split_and; auto; unfold u32_ok, u64_ok; lia ].
  unfold malloc_pre, fields0, lraw. unfold X. rewrite x0_call, call_code_of by lia. cbn [i_magic i_address i_total x0].
  entailer!.
Qed.
