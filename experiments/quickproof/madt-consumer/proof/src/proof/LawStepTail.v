(* Law consumer_obligations: the step export after the answer of the transition's last word is recorded (word 15):
   the test of the transition, then the next state or the rejection. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosMadt.harness.consumer_obligations.code.
Require Import LeanosMadt.proof.Defs.
Require Import LeanosMadt.proof.MadtSpecs.
Require Import LeanosMadt.proof.LawProg LeanosMadt.proof.LawDefs LeanosMadt.proof.LawFacts LeanosMadt.proof.LawLib.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

Definition Delta_step : tycontext := func_tycontext f_leanos_qotom_madt_stream_byte_step_query Vlaw Gexp nil.
Definition Post_step gv x h st tl ex off byte word : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tulong
       (EX v: Z, PROP (u64_ok v) RETURN (vl v) SEP (Ora_law gv x (h ++ [(Step st tl ex off byte word, v)])))%argsassert)
    (stackframe_of f_leanos_qotom_madt_stream_byte_step_query).

(* The statement after `if (word < 15) { ...; return v; }`. *)
Definition s_step_tail : statement := ltac:(
  let b := eval cbv delta [f_leanos_qotom_madt_stream_byte_step_query] beta iota zeta
             in (fn_body f_leanos_qotom_madt_stream_byte_step_query) in
  match b with
  | context [Ssequence (Sifthenelse (Ebinop Olt (Etempvar _word tulong) (Econst_int (Int.repr 15) tint) tint) _ Sskip)
               ?rest] => exact rest
  end).

(* The oracle with the answer of the current word recorded. *)
Definition s_store (s: ost) (v: Z) : ost :=
  mk_ost (os_phase s) (os_byte s) (os_word s) (os_state s) (upd_Znth (os_word s) (os_answer s) v)
         (os_count s) (os_nmi s) (os_policy s) (os_bound s) (os_rejected s).

Ltac start_tail :=
  repeat match goal with
  | |- context [Sloop (Ssequence (Sifthenelse ?e Sskip Sbreak) ?s) Sskip] => fold (Swhile e s)
  | |- context [Ssequence ?s1 (Sloop (Ssequence (Sifthenelse ?e Sskip Sbreak) ?s2) ?s3) ] =>
      match s3 with
      | Sset ?i _ => match s1 with Sset ?i' _ => unify i i' | Sskip => idtac end
      end;
      fold (Sfor s1 e s2 s3)
  end;
  simplify_func_tycontext;
  abbreviate_semax.

Lemma step_tail {Espec: OracleKind} gv bytes ob h s p sh cur v:
  readable_share sh -> length_ok (Zlength bytes) = true -> Forall byte_ok bytes -> obs_ok ob -> ost_ok s ->
  nmi_ok bytes s -> run (bytes, ob) (start (bytes, ob)) h = Some (Go (Stream (os_byte s) (os_state s) cur)) ->
  go_inv (bytes, ob) (Stream (os_byte s) (os_state s) cur) s -> Zlength cur = 15 -> u64_ok v ->
  forall Delta R c, Delta = Delta_step ->
  R = Post_step gv (bytes, ob) h (os_state s) (44 + Zlength bytes) (o_executing ob) (44 + os_byte s)
        (Znth (os_byte s) bytes) (Zlength cur) ->
  c = s_step_tail ->
  semax Delta
    (PROP ()
     LOCAL (temp _v (vl v); temp _o (gv _oracle); gvars gv; temp _offset (vl (44 + os_byte s));
            temp _byte (vl (Znth (os_byte s) bytes)))
     SEP (ofields (gv _oracle) p (Zlength bytes) ob (s_store s v);
          data_at sh (tarray tuchar (Zlength bytes)) (bytes_val bytes) p))
    c R.
Proof.
  intros Hsh Hlen Hby Hob Hok Hnmi R G L15 Hv Delta Rp c -> -> ->.
  unfold s_step_tail, Delta_step, Post_step. start_tail.
  pose proof G as (P & B & W & S & A & Rj & I & C). simpl fst in I.
  pose proof Hok as (Rph & Rby & Rwo & Rco & Rre & Lst & Lan & Lnm & Lpo & Lbo & Fst & Fan & Fnm & Fpo & Fbo).
  pose proof Hlen as Hl. unfold length_ok in Hl. apply andb_true_iff in Hl as [Hl1 Hl2].
  apply Z.ltb_lt in Hl1. apply Z.leb_le in Hl2. unfold MAX_LENGTH in Hl2.
  unfold u64_ok in Rby, Hv.
  unfold ofields, s_store. ost_cbn. rewrite W, L15, P. Intros.
  set (r := upd_Znth 15 (os_answer s) v).
  assert (Lr: Zlength r = 16) by (unfold r; rewrite upd_Znth_Zlength; lia).
  assert (Fr: Forall u64_ok r) by (apply Forall_upd; auto).
  rng_list r 16.
  assert (Rb: 0 <= Znth (os_byte s) bytes <= Byte.max_unsigned) by (apply Forall_byte_Znth; auto).
  set (n := Zlength bytes) in *.
  forward. forward. forward.
  rewrite last_val by lia.
  freeze_but [_answer] false F3.
  forward.
  forward_if (temp _t'15 (Vint (Int.repr (Z.b2z (acc1 r))))).
  { forward. forward. entailer!. bool_fin. }
  { forward. entailer!. bool_fin. }
  forward_if (temp _t'16 (Vint (Int.repr (Z.b2z (acc2 n (os_byte s) r))))).
  { forward_if (temp _t'17 (Vint (Int.repr (if os_byte s + 1 =? n then 3 else 1)))).
    { forward. entailer!. bool_fin. }
    { forward. entailer!. bool_fin. }
    forward. forward. entailer!. bool_fin. }
  { forward. entailer!. bool_fin. }
  forward_if (temp _t'18 (Vint (Int.repr (Z.b2z (acc3 n (os_byte s) r))))).
  { forward. forward. entailer!. bool_fin. }
  { forward. entailer!. bool_fin. }
  forward_if (temp _t'19 (Vint (Int.repr (Z.b2z (acc4 n (os_byte s) r))))).
  { forward. forward. entailer!. bool_fin. }
  { forward. entailer!. bool_fin. }
  forward_if (temp _t'20 (Vint (Int.repr (Z.b2z (accept_b n (os_byte s) (Znth (os_byte s) bytes) r))))).
  { forward. forward. entailer!. rewrite accept_acc. bool_fin. }
  { forward. entailer!. rewrite accept_acc. bool_fin. }
  thaw F3. deadvars!.
  forward_if (PROP () LOCAL (temp _v (vl v))
     SEP (Ora_law gv (bytes, ob) (h ++ [(Step (os_state s) (44 + n) (o_executing ob) (44 + os_byte s)
                                           (Znth (os_byte s) bytes) (Zlength cur), v)]))).
  - (* accepted: the next state *)
    try b2z_hyp.
    freeze_but [_state; _answer] false F4.
    forward_for_simple_bound 12
      (EX k: Z, PROP ()
       LOCAL (temp _last (vl (if os_byte s + 1 =? n then 1 else 0)); temp _v (vl v); temp _o (gv _oracle); gvars gv)
       SEP (FRZL F4; field_at Ews t_oracle (DOT _answer) (map vl r) (gv _oracle);
            field_at Ews t_oracle (DOT _state) (map vl (sublist 3 (3 + k) r ++ sublist k 12 (os_state s)))
              (gv _oracle)))%assert.
    { replace (sublist 3 (3 + 0) r ++ sublist 0 12 (os_state s)) with (os_state s) by list_solve. entailer!. }
    { forward. forward. rewrite upd_Znth_map_vl.
      replace (upd_Znth i (sublist 3 (3 + i) r ++ sublist i 12 (os_state s)) (Znth (i + 3) r))
        with (sublist 3 (3 + (i + 1)) r ++ sublist (i + 1) 12 (os_state s)) by list_solve.
      entailer!. }
    thaw F4.
    replace (sublist 3 (3 + 12) r ++ sublist 12 12 (os_state s)) with (sublist 3 15 r) by list_solve.
    forward. forward. forward.
    destruct (os_byte s + 1 =? n) eqn:El.
    + forward_if.
      * forward.
        unfold Ora_law. Exists p sh (s_accept s n r). unfold ofields. ost_cbn. rewrite El.
        entailer!.
        split; [ apply ost_ok_accept; auto; unfold MAX_LENGTH; lia | ].
        rewrite (J_snoc_step _ _ _ _ _ _ _ _ R). apply Jp_stream_accept; auto.
      * else_false.
    + forward_if.
      * else_false.
      * forward.
        unfold Ora_law. Exists p sh (s_accept s n r). unfold ofields. ost_cbn. rewrite El.
        entailer!.
        split; [ apply ost_ok_accept; auto; unfold MAX_LENGTH; lia | ].
        rewrite (J_snoc_step _ _ _ _ _ _ _ _ R). apply Jp_stream_accept; auto.
  - (* rejected *)
    try b2z_hyp. forward. forward.
    unfold Ora_law. Exists p sh (s_reject s r). unfold ofields, r. ost_cbn. rewrite W, L15.
    entailer!.
    match goal with |- context [Step ?a ?b ?c ?d ?e 15] =>
      replace (Step a b c d e 15) with (Step a b c d e (Zlength cur)) by (rewrite L15; reflexivity) end.
    split; [ apply ost_ok_reject; auto | ].
    rewrite (J_snoc_step _ _ _ _ _ _ _ _ R). apply Jp_stream_reject; auto.
  - forward. Exists v. entailer!.
Qed.
