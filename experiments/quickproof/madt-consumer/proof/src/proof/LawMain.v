(* Law consumer_obligations: the body of the harness's main, up to the call of madt_bind; its checks after the call
   are the tail lemmas (LawTailInvalid, LawTailValid). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosMadt.harness.consumer_obligations.code.
Require Import LeanosMadt.proof.Defs.
Require Import LeanosMadt.proof.MadtSpecs.
Require Import LeanosMadt.proof.LawProg LeanosMadt.proof.LawDefs LeanosMadt.proof.LawFacts LeanosMadt.proof.LawLib
  LeanosMadt.proof.LawSplit LeanosMadt.proof.LawMainLib LeanosMadt.proof.LawMainDefs LeanosMadt.proof.LawMainInit.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

Lemma malloc_test_null (t: type) (q: val) (P: mpred):
  0 < sizeof t ->
  ((if eq_dec q nullval then emp else malloc_token Ews t q * data_at_ Ews t q) * P)%logic
  |-- denote_tc_test_eq q (Vlong (Int64.repr 0)).
Proof.
  intros Ht. destruct (eq_dec q nullval).
  - subst. simpl. entailer!.
  - sep_apply (data_at__valid_ptr Ews t q); [ auto | lia | ]. entailer!.
Qed.

(* The value of `nondet_u8() == 0 ? NULL : p`. *)
Ltac sel_close :=
  u64c;
  unfold sel; match goal with |- context [?u =? 0] => destruct (Z.eqb_spec u 0) end;
  first [ reflexivity | (exfalso; lia) | contradiction ].

Lemma body_main: forall p, QPprog_vars p = [(_oracle, v_oracle)] ->
  semax_body Vlaw Gmain f_main (_main, main_spec_std p).
Proof.
  intros p Hp. start_function. rewrite Hp.
  assert_PROP (headptr (gv _oracle)) as HO by entailer!.
  sep_apply (oracle_zero gv HO).
  sep_apply (create_mem_mgr gv).
  forward.
  forward_call. Intros n.
  forward_if (temp _t'2 (Vint (Int.repr (Z.b2z (length_ok n))))).
  { forward. entailer!. unfold length_ok, MAX_LENGTH. bool_fin. }
  { forward. entailer!. unfold length_ok, MAX_LENGTH. bool_fin. }
  forward.
  assert (Lok: length_ok n = true -> 0 < n <= MAX_LENGTH).
  { unfold length_ok. intros E. apply andb_true_iff in E as [E1 E2]. apply Z.ltb_lt in E1. apply Z.leb_le in E2. lia. }
  set (vb := length_ok n) in *.
  set (sz := if vb then n else 1).
  assert (Hsz: 1 <= sz <= MAX_LENGTH) by (unfold sz; destruct vb; [ specialize (Lok eq_refl); lia | unfold MAX_LENGTH; lia ]).
  forward_if (temp _t'3 (vl sz)).
  { forward. entailer!. try b2z_hyp. unfold sz. rewrite H0. reflexivity. }
  { forward. entailer!. try b2z_hyp. unfold sz. rewrite H0. reflexivity. }
  forward_call (tarray tuchar sz, gv).
  { simpl. unfold MAX_LENGTH in Hsz. rewrite Z.max_r by lia. repeat split; auto; rep_lia. }
  Intros q.
  destruct (eq_dec q nullval) as [Eq | Nq].
  { (* malloc returned NULL *)
    subst q. forward.
    forward_if (PROP (False) LOCAL () SEP ()).
    { forward. Exists (Int.repr 0). entailer!. }
    { else_false. }
    }
  try rewrite if_false by auto. Intros. forward.
  match goal with |- semax _ ?Pre _ _ => forward_if Pre end.
  { exfalso. auto. }
  { forward. entailer!. }
  forward_if (temp _t'5 (vl sz)).
  { forward. entailer!. try b2z_hyp. unfold sz. rewrite H0. reflexivity. }
  { forward. entailer!. try b2z_hyp. unfold sz. rewrite H0. reflexivity. }
  forward_call (q, sz, Ews).
  { rewrite if_false by auto. cancel. }
  { unfold MAX_LENGTH in Hsz; rep_lia. }
  Intros bs. rewrite if_false by auto.
  change (map (fun b => Vint (Int.repr b)) bs) with (bytes_val bs).
  (* the observation *)
  forward_call tt. Intros e1. forward.
  forward_call tt. Intros e2. forward.
  forward_call tt. Intros e3. forward.
  forward_call tt. Intros e4. forward.
  forward_call tt. Intros e5. forward.
  forward_call tt. Intros e6. forward.
  (* the result record *)
  forward. forward. forward. forward. forward. forward.
  change (Vlong (Int64.repr (Int.signed (Int.repr 7)))) with (vl 7).
  deadvars!.
  (* the arguments that may be NULL *)
  forward_call. Intros u1.
  forward_if (temp _t'13 (sel (u1 =? 0) q)).
  { forward. entailer!; sel_close. }
  { forward. entailer!; sel_close. }
  forward.
  forward_call. Intros u2.
  forward_if (temp _t'15 (sel (u2 =? 0) v_observation)).
  { forward. entailer!; sel_close. }
  { forward. entailer!; sel_close. }
  forward.
  forward_call. Intros u3.
  forward_if (temp _t'17 (sel (u3 =? 0) v_out)).
  { forward. entailer!; sel_close. }
  { forward. entailer!; sel_close. }
  forward.
  deadvars!.
  subst sz vb.
  eapply semax_pre;
    [ | apply (tail_init gv q v_out v_observation n bs e1 e2 e3 e4 e5 e6 (u1 =? 0) (u2 =? 0) (u3 =? 0));
        first [ reflexivity | assumption | auto ] ].
  match goal with E: Zlength bs = _ |- _ => rewrite <- E end. entailer!.
Qed.
