(* Law capabilities_adversarial: the body of the harness's main. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosCaps.harness.capabilities_adversarial.code.
Require Import LeanosCaps.proof.Defs.
Require LeanosCaps.proof.CapsSpecs.
Require Import LeanosCaps.proof.AdvProg LeanosCaps.proof.AdvWalk LeanosCaps.proof.AdvFacts LeanosCaps.proof.AdvSpecs
  LeanosCaps.proof.AdvLib LeanosCaps.proof.AdvMainDefs LeanosCaps.proof.AdvTailArg LeanosCaps.proof.AdvTailWalk.
Local Open Scope Z_scope.

(* struct pci_enumeration_header with any words. *)
Definition hdr_part (bus dev fn: Z) (l: list val) : reptype t_header :=
  (Vint (Int.repr bus), (Vint (Int.repr dev), (Vint (Int.repr fn), l))).

Lemma words_snoc: forall (ws: list Z) x i, Zlength ws = i -> 0 <= i < 16 ->
  upd_Znth i (map (fun w => Vint (Int.repr w)) ws ++ Zrepeat Vundef (16 - i)) (Vint (Int.repr x)) =
  map (fun w => Vint (Int.repr w)) (ws ++ [x]) ++ Zrepeat Vundef (16 - (i + 1)).
Proof. intros. list_solve. Qed.

Lemma body_main: forall p, QPprog_vars p = nil -> semax_body nil Gmain f_main (_main, main_spec_std p).
Proof.
  intros p Hp.
  start_function.
  rewrite Hp. change (globvars2pred gv nil) with (@emp mpred _ _).
  make_func_ptr _device_read.
  assert_PROP (isptr (gv _device_read) /\ isptr v_initial /\ isptr v_snapshot /\ isptr v_result /\ isptr v_d)
    as PTRS by entailer!.
  destruct PTRS as (Pr & Pi & Ps & Pq & Pd).
  forward_call. Intros bus. forward.
  forward_call. Intros dev. forward.
  forward_call. Intros fn. forward.
  zext.
  freeze_except v_initial v_initial F1.
  forward_for_simple_bound 16
    (EX i: Z, EX ws: list Z,
     PROP (Zlength ws = i; Forall CapsSpecs.u32_ok ws)
     LOCAL (lvar _masks (tarray tuint 4) v_masks; lvar _header_offsets (tarray tuchar 4) v_header_offsets;
            lvar _result t_res v_result; lvar _snapshot t_snap v_snapshot; lvar _d t_device v_d;
            lvar _initial t_header v_initial; gvars gv)
     SEP (FRZL F1;
          data_at Tsh t_header (hdr_part bus dev fn (map (fun w => Vint (Int.repr w)) ws ++ Zrepeat Vundef (16 - i)))
            v_initial)).
  { Exists (@nil Z). entailer!. }
  { forward_call. Intros x. unfold hdr_part. forward.
    Exists (ws ++ [x]). entailer!.
    - split; [ list_solve | apply Forall_app; split; [ assumption | constructor; [ unfold CapsSpecs.u32_ok; assumption | constructor ] ] ].
    - rewrite words_snoc by lia. apply derives_refl. }
  Intros ws. thaw F1.
  replace (map (fun w => Vint (Int.repr w)) ws ++ Zrepeat Vundef (16 - 16)) with (map (fun w => Vint (Int.repr w)) ws)
    by list_solve.
  change (hdr_part bus dev fn (map (fun w => Vint (Int.repr w)) ws)) with (hdr_val bus dev fn ws).
  unfold hdr_val.
  fw. fw. fw. fw. fw. fw. fw.
  forward_call. Intros cnt. fw.
  fw.
  forward_call. Intros ro. fw.
  fw. fw.
  zext.
  forward_call. Intros b7.
  forward_if (temp _t'8 (if b7 =? 0 then nullval else gv _device_read)).
  { forward. entailer!. }
  { eapply semax_post_flipped'; [ clear_Delta_specs; forward_setx | ].
    simplify_remove_localdef_temp. destruct (Z.eqb_spec b7 0); [ contradiction | ]. entailer!. }
  forward.
  forward_call. Intros b9.
  forward_if (temp _t'10 (if b9 =? 0 then nullval else v_initial)).
  { forward. entailer!. }
  { forward. destruct (Z.eqb_spec b9 0); [ contradiction | ]. entailer!. }
  forward.
  forward_call. Intros b11.
  forward_if (temp _t'12 (if b11 =? 0 then nullval else v_snapshot)).
  { forward. entailer!. }
  { forward. destruct (Z.eqb_spec b11 0); [ contradiction | ]. entailer!. }
  forward.
  forward_call. Intros b13.
  forward_if (temp _t'14 (if b13 =? 0 then nullval else v_result)).
  { forward. entailer!. }
  { forward. destruct (Z.eqb_spec b13 0); [ contradiction | ]. entailer!. }
  forward.
  fw.
  deadvars!.
  freeze [1; 2; 3; 5; 6] F2.
  forward_if (temp _t'15 (Vint (Int.repr (CapsSpecs.b2z ((b7 =? 0) || (b9 =? 0))%bool)))).
  { apply sel_tc_test; [ entailer! | auto ]. }
  { match goal with E: (if _ then nullval else _) = nullval |- _ => apply sel_eq_null in E; [ | auto ] end.
    forward. entailer!. bsubst. reflexivity. }
  { match goal with E: (if _ then nullval else _) <> nullval |- _ => apply sel_ne_null in E end.
    forward. { tc_sel. } ptr_bool. }
  forward_if (temp _t'16 (Vint (Int.repr (CapsSpecs.b2z ((b7 =? 0) || (b9 =? 0) || (b11 =? 0))%bool)))).
  { b2z_hyps. forward. entailer!. bsubst. reflexivity. }
  { b2z_hyps. forward. { tc_sel. } ptr_bool. }
  forward_if (temp _t'17 (Vint (Int.repr (CapsSpecs.b2z ((b7 =? 0) || (b9 =? 0) || (b11 =? 0) || (31 <? dev))%bool)))).
  { b2z_hyps. forward. entailer!. bsubst. reflexivity. }
  { b2z_hyps. fw. fw. entailer!. bool_fin. }
  forward_if (temp _t'18 (Vint (Int.repr (CapsSpecs.b2z ((b7 =? 0) || (b9 =? 0) || (b11 =? 0) || (31 <? dev) ||
                                                         (7 <? fn))%bool)))).
  { b2z_hyps. forward. entailer!. bsubst. reflexivity. }
  { b2z_hyps. fw. fw. entailer!. bool_fin. }
  assert (W3: 0 <= Znth 3 ws <= Int.max_unsigned) by (apply words_Znth; auto; lia).
  assert (W0: 0 <= Znth 0 ws <= Int.max_unsigned) by (apply words_Znth; auto; lia).
  forward_if (temp _t'19 (Vint (Int.repr (CapsSpecs.b2z ((b7 =? 0) || (b9 =? 0) || (b11 =? 0) || (31 <? dev) ||
                                    (7 <? fn) || (1 <? Z.land (Z.shiftr (Znth 3 ws) 16) 127))%bool)))).
  { b2z_hyps. forward. entailer!. bsubst. reflexivity. }
  { b2z_hyps. fw. fw. entailer!. bool_fin. }
  forward_if (temp _t'20 (Vint (Int.repr (CapsSpecs.b2z ((b7 =? 0) || (b9 =? 0) || (b11 =? 0) || (31 <? dev) ||
                (7 <? fn) || (1 <? Z.land (Z.shiftr (Znth 3 ws) 16) 127) ||
                (Z.land (Znth 0 ws) 65535 =? 65535))%bool)))).
  { b2z_hyps. forward. entailer!. bsubst. reflexivity. }
  { b2z_hyps. fw. fw. entailer!. bool_fin. }
  rewrite inv_eq.
  forward.
  thaw F2.
  deadvars!.
  set (rb := (b7 =? 0)) in *. set (ib := (b9 =? 0)) in *. set (sb := (b11 =? 0)) in *. set (qb := (b13 =? 0)) in *.
  (* the walker's arguments *)
  change (Tstruct _device noattr) with t_device.
  sep_apply (dev_init bus dev fn v_d).
  sep_apply (maybe_read_split rb (gv _device_read)).
  change (Vint (Int.repr bus), (Vint (Int.repr dev), (Vint (Int.repr fn), map (fun w => Vint (Int.repr w)) ws)))
    with (hdr_val bus dev fn ws).
  rewrite (maybe_split ib Tsh t_header (CapsSpecs.header_val bus dev fn ws) (hdr_val bus dev fn ws) v_initial Pi
             ltac:(apply JMeq_refl) ltac:(reflexivity)).
  change (Tstruct _pci_capability_snapshot noattr) with CapsSpecs.t_snapshot.
  sep_apply (maybe_split_snap sb Tsh
     (Vint (Int.repr cnt), snd (default_val (Tstruct _pci_capability_snapshot noattr))) v_snapshot Ps).
  change (Tstruct _pci_capability_result noattr) with CapsSpecs.t_result.
  sep_apply (maybe_split_res qb Tsh (Vint (Int.repr 0), Vint (Int.repr ro)) v_result Pq).
  forward_call ((if rb then nullval else gv _device_read), v_d, (if ib then nullval else v_initial), Tsh, bus, dev, fn,
                ws, (if sb then nullval else v_snapshot), @default_val LCS CapsSpecs.t_snapshot,
                (if qb then nullval else v_result), @default_val LCS CapsSpecs.t_result).
  { cancel. }
  { repeat split; apply sel_ptr_or_null; auto. }
  Intros vret. destruct vret as [[[[h st] off] caps] rest]. simpl fst in *; simpl snd in *.
  rewrite !sel_isnull in * by auto.
  sep_apply (maybe_join' ib Tsh t_header (CapsSpecs.header_val bus dev fn ws) (hdr_val bus dev fn ws)
               (hdr_val bus dev fn ws) v_initial Pi ltac:(apply JMeq_refl) ltac:(reflexivity)).
  rewrite if_same.
  sep_apply (maybe_join' sb Tsh CapsSpecs.t_snapshot
               (CapsSpecs.snapshot_val (Zlength caps) (map CapsSpecs.cap_val caps ++ rest))
               (CapsSpecs.snapshot_val (Zlength caps) (map CapsSpecs.cap_val caps ++ rest) : @reptype LCS CapsSpecs.t_snapshot)
               ((Vint (Int.repr cnt), Zrepeat (Vundef, Vundef) 48) : @reptype LCS CapsSpecs.t_snapshot) v_snapshot Ps
               ltac:(apply JMeq_refl) ltac:(reflexivity)).
  sep_apply (maybe_join' qb Tsh CapsSpecs.t_result (CapsSpecs.result_val st off)
               (CapsSpecs.result_val st off : @reptype LCS CapsSpecs.t_result)
               ((Vint (Int.repr 0), Vint (Int.repr ro)) : @reptype LCS CapsSpecs.t_result) v_result Pq
               ltac:(apply JMeq_refl) ltac:(reflexivity)).
  unfold CapsSpecs.snapshot_val, CapsSpecs.result_val. rewrite !if_pair, !if_vint.
  deadvars!.
  clearbody rb ib sb qb.
  destruct (rb || ib || sb || negb (args_ok dev fn ws))%bool eqn:Einv.
  - destruct H11 as (-> & -> & -> & ->).
    eapply semax_pre;
      [ | apply (tail_arg gv v_initial v_d v_snapshot v_result v_header_offsets v_masks bus dev fn ws cnt ro rb ib sb qb
                   rest);
        first [ reflexivity | assumption | (rewrite Zlength_nil in H10; lia) | auto ] ].
    unfold S_ARGUMENT. simpl CapsSpecs.b2z. rewrite Zlength_nil. simpl map. simpl app.
    entailer!.
  - repeat match goal with E: (_ || _)%bool = false |- _ => apply orb_false_iff in E; destruct E as [E ?] end.
    subst rb ib sb.
    match goal with E: negb (args_ok _ _ _) = false |- _ => apply negb_false_iff in E end.
    repeat match goal with |- context [if false then ?a else ?b] => change (if false then a else b) with b end.
    eapply semax_pre;
      [ | apply (tail_walk gv v_initial v_d v_snapshot v_result v_header_offsets v_masks bus dev fn ws cnt ro qb h st off
                   caps rest); first [ reflexivity | assumption | auto ] ].
    simpl CapsSpecs.b2z.
    entailer!.
Qed.
