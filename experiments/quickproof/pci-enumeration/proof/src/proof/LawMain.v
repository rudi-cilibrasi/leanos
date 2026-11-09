(* Law enumeration_exact: the body of the harness's main. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosEnum.harness.enumeration_exact.code.
Require Import LeanosEnum.proof.Defs.
Require LeanosEnum.proof.EnumSpecs.
Require Import LeanosEnum.proof.LawProg LeanosEnum.proof.LawRun LeanosEnum.proof.LawSpecs LeanosEnum.proof.LawSplit
  LeanosEnum.proof.LawLib LeanosEnum.proof.LawOut LeanosEnum.proof.LawSplitU LeanosEnum.proof.LawMainDefs
  LeanosEnum.proof.LawTailInv LeanosEnum.proof.LawTailStop LeanosEnum.proof.LawTailOK.
Local Open Scope Z_scope.

Lemma body_main: forall p, QPprog_vars p = nil -> semax_body nil Gmain f_main (_main, main_spec_std p).
Proof.
  intros p Hp.
  start_function.
  rewrite Hp. change (globvars2pred gv nil) with (@emp mpred _ _).
  make_func_ptr _device_read.
  assert_PROP (isptr (gv _device_read) /\ isptr v_d /\ isptr v_snapshot /\ isptr v_result) as PTRS by entailer!.
  destruct PTRS as (Pr & Pd & Ps & Pq).
  change (Tstruct _device noattr) with t_device.
  rewrite dev_split_. Intros.
  forward. forward. forward. forward. forward. forward.
  forward_call. Intros cnt. forward.
  forward.
  forward.
  forward_call. Intros rb. forward.
  forward_call. Intros rd. forward.
  forward_call. Intros rf. forward.
  forward_call. Intros ro. forward.
  zext.
  fw. fw. fw. fw. fw. fw. fw. fw.
  zext.
  (* the NULL choices *)
  forward_call. Intros b6.
  forward_if (temp _t'7 (if b6 =? 0 then nullval else gv _device_read)).
  { forward. entailer!. }
  { eapply semax_post_flipped'; [ clear_Delta_specs; forward_setx | ].
    simplify_remove_localdef_temp. destruct (Z.eqb_spec b6 0); [ contradiction | ]. entailer!. }
  forward.
  forward_call. Intros b8.
  forward_if (temp _t'9 (if b8 =? 0 then nullval else v_snapshot)).
  { forward. entailer!. }
  { forward. destruct (Z.eqb_spec b8 0); [ contradiction | ]. entailer!. }
  forward.
  forward_call. Intros b10.
  forward_if (temp _t'11 (if b10 =? 0 then nullval else v_result)).
  { forward. entailer!. }
  { forward. destruct (Z.eqb_spec b10 0); [ contradiction | ]. entailer!. }
  forward.
  deadvars!.
  set (rb' := (b6 =? 0)) in *. set (sb := (b8 =? 0)) in *. set (qb := (b10 =? 0)) in *.
  (* the scan's arguments *)
  pose proof (dev_init v_d) as DI. unfold dev_fields, loc_undef in DI. simpl fst in DI; simpl snd in DI.
  sep_apply DI. clear DI.
  sep_apply (maybe_read_split rb' (gv _device_read)).
  change (Tstruct _pci_enumeration_snapshot noattr) with EnumSpecs.t_snapshot.
  change (Tstruct _pci_enumeration_result noattr) with EnumSpecs.t_result.
  sep_apply (maybe_split_ sb Tsh EnumSpecs.t_snapshot
               (Vint (Int.repr cnt), snd (default_val EnumSpecs.t_snapshot)) v_snapshot Ps ltac:(reflexivity)).
  sep_apply (maybe_split_ qb Tsh EnumSpecs.t_result
               (Vint (Int.repr 0), (Vint (Int.repr rb), (Vint (Int.repr rd), (Vint (Int.repr rf), Vint (Int.repr ro)))))
               v_result Pq ltac:(reflexivity)).
  forward_call ((if rb' then nullval else gv _device_read), v_d, (if sb then nullval else v_snapshot),
                @default_val EnumSpecs.CS EnumSpecs.t_snapshot,
                (if qb then nullval else v_result), @default_val EnumSpecs.CS EnumSpecs.t_result).
  { cancel. }
  { repeat split; apply sel_ptr_or_null; auto. }
  Intros vret. destruct vret as [[[[[h st] i] off] pub] rest]. simpl fst in *; simpl snd in *.
  rewrite !sel_isnull in * by auto.
  sep_apply (maybe_join' sb Tsh EnumSpecs.t_snapshot
               (EnumSpecs.snapshot_val (Zlength pub) (map EnumSpecs.header_val pub ++ rest))
               (EnumSpecs.snapshot_val (Zlength pub) (map EnumSpecs.header_val pub ++ rest)
                  : @reptype LCS EnumSpecs.t_snapshot)
               ((Vint (Int.repr cnt), Zrepeat (Vundef, (Vundef, (Vundef, Zrepeat Vundef 16))) 16)
                  : @reptype LCS EnumSpecs.t_snapshot)
               v_snapshot Ps ltac:(apply JMeq_refl) ltac:(reflexivity)).
  sep_apply (maybe_join' qb Tsh EnumSpecs.t_result (EnumSpecs.result_at st i off)
               (EnumSpecs.result_at st i off : @reptype LCS EnumSpecs.t_result)
               ((Vint (Int.repr 0), (Vint (Int.repr rb), (Vint (Int.repr rd), (Vint (Int.repr rf),
                  Vint (Int.repr ro))))) : @reptype LCS EnumSpecs.t_result)
               v_result Pq ltac:(apply JMeq_refl) ltac:(reflexivity)).
  unfold EnumSpecs.snapshot_val, EnumSpecs.result_at, EnumSpecs.result_val. rewrite !if_pair, !if_vint.
  clearbody rb' sb qb.
  sep_apply (read_TT (if rb' then nullval else gv _device_read) (gv _device_read)).
  match goal with E: context [if (rb' || sb)%bool then _ else _] |- _ => rename E into Sc end.
  destruct (rb' || sb)%bool eqn:Einv; simpl in Sc.
  - (* INVALID_ARGUMENT *)
    destruct Sc as (-> & -> & -> & -> & ->).
    sep_apply (dev_nil v_d). Intros seen.
    eapply semax_pre;
      [ | apply (tail_inv gv v_d v_snapshot v_result rb' sb qb cnt rb rd rf ro seen rest);
          first [ reflexivity | assumption ] ].
    unfold dev_fields, loc_undef, S_INVALID_ARGUMENT. simpl fst; simpl snd.
    rewrite Zlength_nil, app_nil_l.
    change (bus_of 0) with 0. change (dev_of 0) with 0. change (fn_of 0) with 0.
    entailer!.
  - destruct (Z.eq_dec st S_OK) as [Eok|Nok].
    + (* OK *)
      subst st. sep_apply (dev_ok v_d h i off pub Sc). Intros fs seen.
      try subst i; try subst off; try subst pub.
      pose proof (Zlength_nonneg h).
      eapply semax_pre;
        [ | apply (tail_ok gv v_d v_snapshot v_result rb' sb qb cnt rb rd rf ro fs (Zlength h) (last_loc h) seen rest);
            first [ reflexivity | assumption | rep_lia ] ].
      unfold dev_fields, S_OK.
      change (bus_of 0) with 0. change (dev_of 0) with 0. change (fn_of 0) with 0.
      entailer!.
    + (* READ_FAILED or CAPACITY_EXCEEDED *)
      sep_apply (dev_stop v_d h st i off pub Sc Nok). Intros nx wx fx seen.
      try subst pub.
      eapply semax_pre;
        [ | apply (tail_stop gv v_d v_snapshot v_result rb' sb qb cnt rb rd rf ro st i off nx wx fx (Zlength h) seen
                     rest); first [ reflexivity | assumption ] ].
      unfold dev_fields, loc_of. simpl fst; simpl snd.
      rewrite Zlength_nil, app_nil_l.
      entailer!.
Qed.
