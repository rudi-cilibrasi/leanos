(* Law enumeration_exact: the body of the harness's device_read against the read protocol of Dev_exact. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosEnum.harness.enumeration_exact.code.
Require Import LeanosEnum.proof.Defs.
Require LeanosEnum.proof.EnumSpecs.
Require Import LeanosEnum.proof.LawProg LeanosEnum.proof.LawRun LeanosEnum.proof.LawSpecs LeanosEnum.proof.LawDev
  LeanosEnum.proof.LawSplit LeanosEnum.proof.LawAddr LeanosEnum.proof.LawSeen.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

Lemma data_at__tuint_cs: forall sh p, @data_at_ EnumSpecs.CS sh tuint p = @data_at_ LCS sh tuint p.
Proof.
  intros. apply (f_equal (fun f => f p)).
  apply (@data_at__change_composite EnumSpecs.CS LCS (CCE_any EnumSpecs.CS LCS)); reflexivity.
Qed.

Lemma data_at_tuint_cs: forall sh v p, @data_at EnumSpecs.CS sh tuint v p = @data_at LCS sh tuint v p.
Proof.
  intros. apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite EnumSpecs.CS LCS (CCE_any EnumSpecs.CS LCS)); [ apply JMeq_refl | reflexivity ].
Qed.

(* After a store into seen[k]: one update of seen at k. *)
Ltac seen_simpl :=
  repeat first
    [ rewrite upd_Znth_same by (rewrite ?upd_Znth_Zlength by lia; lia)
    | rewrite upd_Znth_twice by (rewrite ?upd_Znth_Zlength by lia; lia) ];
  simpl fst; simpl snd.

(* The value stored through read's pointer, under the law's compspecs. *)
Ltac vp_true :=
  try match goal with |- context [if true then ?a else ?b] => change (if true then a else b) with a end;
  rewrite data_at_tuint_cs.

(* Exists the seen[] the SEP holds. *)
Ltac exists_seen := match goal with |- context [field_at _ _ (DOT _seen) ?x _] => Exists x end.

(* The answer list of read_spec's postcondition, as the list of answers the lemmas of LawDev rewrite. *)
Ltac fix_ans :=
  match goal with |- context [Dev_exact ?c (?h ++ [?a])] =>
    change (Dev_exact c (h ++ [a])) with (Dev_exact c (@app answer h (@cons answer a nil))) end.

Lemma body_device_read: semax_body Vh Gh f_device_read device_read_spec.
Proof.
  start_function.
  destruct (next_read_go h i off H) as (next & w & fs & R & L & Rq).
  pose proof (run_go h _ R) as [I N].
  pose proof (nreads_bound _ I) as NB.
  pose proof I as (Rn & Rw & Rf & Fi & Fc).
  unfold request in Rq.
  assert (Ei: i = if w =? 0 then next else next - 1) by (destruct (w =? 0); congruence).
  assert (Eo: off = 4 * w) by (destruct (Z.eqb_spec w 0); inv Rq; lia).
  assert (Ri: 0 <= i < FUNCTIONS).
  { unfold live in L. destruct (Z.eqb_spec w 0) as [W0|W0].
    - subst w i. simpl in L. destruct (Z.eqb_spec next FUNCTIONS); [ discriminate | ]. lia.
    - cbv beta iota in Fc. destruct Fc as (ws & rest & E & _). subst fs i.
      pose proof (Forall_inv Fi) as X. simpl in X. lia. }
  pose proof (bus_range i Ri) as Rb. pose proof (dev_range i) as Rd. pose proof (fn_range i) as Rfn.
  assert (Eb: Int.shru (Int.repr i) (Int.repr 8) = Int.repr (bus_of i)).
  { unfold Int.shru. rewrite !Int.unsigned_repr by (unfold FUNCTIONS in *; rep_lia). reflexivity. }
  assert (Ed: Int.and (Int.shru (Int.repr i) (Int.repr 3)) (Int.repr 31) = Int.repr (dev_of i)).
  { unfold Int.shru. rewrite !Int.unsigned_repr by (unfold FUNCTIONS in *; rep_lia). rewrite and_repr. reflexivity. }
  assert (Ef: Int.and (Int.repr i) (Int.repr 7) = Int.repr (fn_of i)) by (rewrite and_repr; reflexivity).
  assert (Ro: 0 <= off <= 60) by (unfold WORDS in *; lia).
  assert (Ei2: (w = 0 /\ i = next) \/ (w <> 0 /\ i = next - 1)) by (destruct (Z.eqb_spec w 0); auto).
  clear Ei. subst off.
  unfold FUNCTIONS, WORDS, CAPACITY in *.
  rewrite (Dev_go ctx h next w fs R). unfold dev_at. Intros seen.
  rewrite data_at__tuint_cs.
  rewrite dev_split. unfold dev_fields. Intros.
  forward.
  forward.
  forward_call (Int.one).
  forward.
  forward_if (temp _t'1 (Vint (Int.repr i))).
  { forward. forward. entailer!; destruct Ei2 as [[? E]|[? E]]; rewrite E; first [ reflexivity | lia ]. }
  { forward. forward. entailer!; destruct Ei2 as [[? E]|[? E]]; rewrite E; first [ reflexivity | lia ]. }
  forward.
  forward_call (Int.one).
  { entailer!; unfold Int.ltu; rewrite !Int.unsigned_repr by rep_lia; destruct (zlt _ _); first [ reflexivity | lia ]. }
  forward_if (temp _t'2 (Vint Int.one)).
  { forward. entailer!; first [ rewrite Ed | unfold dev_of ]; rewrite Int.eq_true; reflexivity. }
  { exfalso. match goal with E: Int.repr _ <> _ |- _ => apply E; rewrite Eb; reflexivity end. }
  forward_if (temp _t'3 (Vint Int.one)).
  { forward. entailer!; first [ rewrite Ef | unfold fn_of ]; rewrite Int.eq_true; reflexivity. }
  { discriminate. }
  forward_call (Int.one).
  forward.
  forward_call (Int.one).
  { entailer!; rewrite ?mul_repr, ?Int.eq_true; reflexivity. }
  forward. forward.
  forward. forward. forward. forward.
  rewrite add_repr.
  rewrite !zero_ext_inrange by (rewrite Int.unsigned_repr by rep_lia; simpl; rep_lia).
  pose proof (fun ok v => answers_req (next, w, fs) i (4 * w) ok v Rq) as A.
  forward_call. Intros b.
  forward_if.
  { (* the read fails *)
    forward. forward. forward.
    Exists false 0.
    fix_ans.
    rewrite (Dev_snoc_stop ctx h (i, 4 * w, false, 0) next w fs S_READ_FAILED i (4 * w) R L (A _ _)) by reflexivity.
    simpl Z.eqb. cbv iota. rewrite last_loc_snoc. unfold dev_at, loc_of. Exists seen.
    rewrite dev_split. unfold dev_fields. rewrite data_at__tuint_cs.
    entailer!; unfold EnumSpecs.u32_ok; rep_lia. }
  forward_call. Intros v.
  forward. forward.
  apply semax_if_seq.
  forward_if.
  { (* an identity read *)
    match goal with W: w = 0 |- _ => rename W into W0 end.
    destruct Ei2 as [[_ Ei]|[? _]]; [ | lia ]. subst w i.
    forward.
    apply semax_if_seq.
    forward_if.
    { (* a function *)
      assert (Vn: Z.land v 65535 <> 65535).
      { match goal with E: Int.and _ _ <> _ |- _ => intro X; apply E; apply vendor_iff; auto end. }
      forward.
      apply semax_if_seq.
      forward_if.
      { (* the 17th *)
        assert (F16: Zlength fs = 16) by (unfold found in *; lia).
        forward. forward. forward.
        Exists true v. fix_ans.
        rewrite (Dev_snoc_stop ctx h (next, 4 * 0, true, v) next 0 fs S_CAPACITY_EXCEEDED next 0 R L (A _ _))
          by (apply step_cap; [ exact Vn | exact F16 ]).
        simpl Z.eqb. cbv iota. rewrite last_loc_snoc. unfold dev_at, loc_of. Exists seen.
        rewrite dev_split. unfold dev_fields, CAPACITY. vp_true.
        entailer!. }
      { (* found *)
        forward. forward.
        assert_PROP (field_compatible t_device (DOT _seen) ctx) as FCs by entailer!.
        assert (F16': Zlength fs < 16) by (unfold found in *; lia).
        pose proof (Zlength_nonneg fs) as F0.
        pose proof H0 as (Ls & _ & _). unfold CAPACITY in Ls.

        rewrite (seen_addr ctx (Zlength fs) FCs) by lia.
        unfold t_device.
        forward.
        match goal with |- context [@upd_Znth ?T _ seen _] => assert (Ls': @Zlength T seen = 16) by exact Ls end.
        forward. seen_simpl. forward. seen_simpl. forward. seen_simpl.
        forward. forward. forward. forward.
        Exists true v. fix_ans.
        rewrite (Dev_snoc_go ctx h (next, 4 * 0, true, v) (next, 0, fs) (next + 1) 1 ((next, [v]) :: fs) R L (A _ _))
          by (apply step_found; [ exact Vn | unfold CAPACITY; lia ]).
        rewrite last_loc_snoc. unfold dev_at, loc_of.
        exists_seen.
        rewrite dev_split. unfold dev_fields, t_device.
        vp_true.
        entailer!.
        - eapply (@seen_new _ fs seen next v H0 F16').
        - rewrite Zlength_cons. apply derives_refl. }
    }
    { (* no function *)
      assert (Vy: Z.land v 65535 = 65535).
      { match goal with E: Int.and _ _ = _ |- _ => apply vendor_iff; auto end. }
      forward.
      Exists true v. fix_ans.
      rewrite (Dev_snoc_go ctx h (next, 4 * 0, true, v) (next, 0, fs) (next + 1) 0 fs R L (A _ _))
        by (apply step_none; exact Vy).
      rewrite last_loc_snoc. unfold dev_at, loc_of. Exists seen.
      rewrite dev_split. unfold dev_fields. vp_true.
      entailer!. } }
  { (* a dword *)
    assert (W0: w <> 0).
    { intro E. subst w.
      match goal with H: Int.repr 0 <> Int.repr 0 |- _ => apply H; reflexivity | H: 0 <> 0 |- _ => apply H; reflexivity end. }
    destruct Ei2 as [[? _]|[_ Ei]]; [ contradiction | subst i ].
    rewrite (proj2 (Z.eqb_neq w 0) W0) in Fc.
    destruct Fc as (ws & rest & Efs & Lws & Fr). subst w fs.
    pose proof (Zlength_nonneg rest) as Lr0.
    assert (Lfs: @Zlength found ((next - 1, ws) :: rest) = Zlength rest + 1) by (rewrite Zlength_cons; reflexivity).
    assert (Lr16: Zlength rest < 16) by (unfold found in *; lia).
    forward. forward.
    forward.
    forward.
    forward_if (temp _t'6 (Vint (Int.repr (if Zlength ws =? 15 then 0 else Zlength ws + 1)))).
    { assert (W15: Zlength ws = 15).
      { match goal with E: Int.repr (Zlength ws) = Int.sub _ _ |- _ =>
          rewrite sub_repr in E; apply repr_inj_unsigned in E; rep_lia end. }
      forward. rewrite W15. entailer!. }
    { forward. forward.
      entailer!; destruct (Z.eqb_spec (Zlength ws) 15) as [E|E];
        [ exfalso; match goal with N: Int.repr _ <> _ |- _ => apply N; rewrite E; reflexivity end
        | rewrite ?add_repr; reflexivity ]. }
    forward. forward.
    Exists true v. fix_ans.
    rewrite (Dev_snoc_go ctx h (next - 1, 4 * Zlength ws, true, v) (next, Zlength ws, (next - 1, ws) :: rest) next
               (if Zlength ws =? 15 then 0 else Zlength ws + 1) (add_word v ((next - 1, ws) :: rest)) R L (A _ _))
      by (apply step_word; exact W0).
    rewrite add_word_len, last_loc_snoc. unfold dev_at, loc_of.
    exists_seen.
    rewrite dev_split. unfold dev_fields. vp_true.
    entailer!.
    simpl add_word.
    eapply (@seen_word _ (next - 1) ws rest seen v); [ exact H0 | lia | lia | unfold found; rewrite Zlength_cons; lia ]. }
Qed.
