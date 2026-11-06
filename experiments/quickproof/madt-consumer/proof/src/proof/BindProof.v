(* The body proofs of the unit patch/madt_unit.c (include/qotom_bsp_consumer.h and its wrapper), for every oracle
   predicate Ora: qotom_bsp_publish (six field stores), qotom_bind_validated_madt_entries (the consumer, against the
   model `run` of Defs.v) and madt_bind (one call).  The consumer's proof follows the C: the argument checks (an
   invalid call publishes the input-bounds rejection and is handed no oracle), the observation's fields, the stream
   loop over the bytes (the invariant `run ... h = Some (Go (Stream i state nil))`, or `after_stream` past the last
   byte, with the arrays state and result holding the model's state and last answers) with its inner loop of 16
   step calls (`stream_at`) and the checks of each transition (`stream_end`, BindLemmas.v), the record walk (the
   invariant `walk_inv` relating the C loop to `records`, the NMI records packed as `packk`), the 5 policy calls
   (`policy_at`, `policy_end`) and the 6 finish calls (`bound_at`, `bound_end`).  Every early return publishes the
   outcome the model returns at that point. *)
Require Import VST.floyd.proofauto.
Require Import LeanosMadt.madt.code.
Require Import LeanosMadt.proof.Defs.
Require Import LeanosMadt.proof.MadtSpecs.
Require Import LeanosMadt.proof.BindLemmas.
#[local] Existing Instance MadtSpecs.CS.
Local Open Scope Z_scope.

Lemma body_qotom_bsp_publish (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_qotom_bsp_publish publish_spec.
Proof.
  start_function.
  destruct o as [[[[[st d] off] a] c] b].
  forward. forward. forward. forward. forward. forward. forward.
Qed.

Ltac close_ret INV :=
  rewrite INV;
  repeat match goal with H: ?p <> nullval |- context [maybe_at ?sh ?t ?v ?p] =>
    rewrite (maybe_at_nonnull sh t v p H) end;
  entailer!.

Lemma body_qotom_bind_validated_madt_entries (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_qotom_bind_validated_madt_entries (bind_spec Ora).
Proof.
  start_function.
  match goal with H: obs_ok ob |- _ => destruct H as (Uex & Uedx & Uav & Uab & Usid & Urt) end.
  forward_if.
  tc_ptr.
  { (* no result record *)
    subst out. forward.
    Exists (@nil answer) (reject 1 0 44).
    rewrite !invalid_out_null, !maybe_at_null. entailer!. }
  forward_if (temp _t'2 (Vint (Int.repr (b2z (isnull entries || isnull observation))))).
  tc_ptr.
  { forward; subst entries; rewrite isnull_null; entailer!. }
  { forward. entailer!. tc_ptr. entailer!. rewrite notbool_ptr by auto. rewrite (isnull_nonnull entries) by auto. reflexivity. }
  forward_if (temp _t'3 (Vint (Int.repr (b2z (isnull entries || isnull observation || (length =? 0)))))).
  { forward. entailer!. bfix. zrw. reflexivity. }
  { bfix. forward. entailer!. zrw. unfold u64_ok in H. rewrite <- (Int64.repr_unsigned Int64.zero), eq64_repr by (unfold u64_ok; rep_lia).
    change (Int64.unsigned Int64.zero) with 0. destruct (length =? 0); reflexivity. }
  forward_if (temp _t'4 (Vint (Int.repr (b2z (isnull entries || isnull observation || (length =? 0) || (65492 <? length)))))).
  { forward. entailer!. bfix. zrw. reflexivity. }
  { bfix. forward. entailer!. rewrite bool2val_b2z. unfold Int64.cmpu.
    rewrite ltu64_repr by (unfold u64_ok in *; rep_lia). zrw. reflexivity. }
  rewrite <- (invalid_chain entries observation out length) by (auto; unfold u64_ok in H; lia).
  forward_if.
  { (* the input bounds *)
    bfix. match goal with H: invalid_call _ _ _ _ = _ |- _ => rename H into INV end.
    rewrite (maybe_at_nonnull Tsh _ _ out) by auto.
    forward_call (out, rold, (1, 0, 44, 0, 0, 0)).
    { unfold u64_ok; repeat split; rep_lia. }
    forward.
    Exists (@nil answer) (reject 1 0 44).
    rewrite INV, (maybe_at_nonnull Tsh _ _ out) by auto. entailer!. }
  bfix. match goal with H: invalid_call _ _ _ _ = _ |- _ => rename H into INV end. try rewrite INV; try rewrite if_false_eq.
  destruct (valid_ok _ _ _ _ INV) as (Nent & Nobs & Nout & Lok).
  specialize (H1 Lok). subst length.
  rewrite (maybe_at_nonnull esh _ _ entries), (maybe_at_nonnull osh _ _ observation),
    (maybe_at_nonnull Tsh _ _ out) by auto.
  unfold obs_val.
  forward. forward. forward. forward. forward. forward.
  fold (obs_val ob).
  forward. forward. forward. forward. forward. forward. forward. forward. forward. forward. forward. forward.
  forward. forward. forward. forward. forward. forward. forward. forward. forward. forward. forward. forward.
  forward. forward. forward. forward.
  forward.
  assert (TL: Int64.add (Int64.repr (Int.unsigned (Int.repr 44))) (Int64.repr (Zlength bytes)) =
              Int64.repr (44 + Zlength bytes)) by (rewrite add64_repr; reflexivity).
  rewrite TL; clear TL.
  match goal with |- context [data_at Tsh (tarray tulong 12) ?X v_state] =>
    replace X with (map vl initial_state) by (unfold initial_state, vl; reflexivity) end.
  match goal with |- context [data_at Tsh (tarray tulong 16) ?X v_result] =>
    replace X with (map vl (Zrepeat 0 16)) by (unfold vl; reflexivity) end.
  assert (Hn: 0 < Zlength bytes <= 65492)
    by (unfold length_ok, MAX_LENGTH in Lok; apply andb_prop in Lok as [L1 L2];
        apply Z.ltb_lt in L1; apply Z.leb_le in L2; lia).
  deadvars!.
  forward_for_simple_bound (Zlength bytes) (EX i: Z, EX h: list answer, EX state: list Z, EX last: list Z,
    PROP (run (bytes, ob) (start (bytes, ob)) h =
            Some (if i <? Zlength bytes then Go (Stream i state nil) else after_stream bytes last state);
          Zlength state = 12; Forall u64_ok state; Zlength last = 16; Forall u64_ok last)
    LOCAL (temp _table_length (vl (44 + Zlength bytes)); temp _routing_authority (vl (o_routing ob));
           temp _sample_id (vl (o_sample_id ob)); temp _apic_base (vl (o_apic_base ob));
           temp _available (vl (o_available ob)); temp _cpuid_edx (vl (o_cpuid_edx ob));
           temp _executing (vl (o_executing ob));
           lvar _bound (tarray tulong 6) v_bound; lvar _nmi_policy (tarray tulong 5) v_nmi_policy;
           lvar _nmi (tarray tulong 4) v_nmi; lvar _result (tarray tulong 16) v_result;
           lvar _state (tarray tulong 12) v_state; gvars gv;
           temp _entries entries; temp _length (vl (Zlength bytes)); temp _out out)
    SEP (data_at_ Tsh (tarray tulong 6) v_bound; data_at_ Tsh (tarray tulong 5) v_nmi_policy;
         data_at_ Tsh (tarray tulong 4) v_nmi;
         data_at Tsh (tarray tulong 16) (map vl last) v_result;
         data_at Tsh (tarray tulong 12) (map vl state) v_state;
         Ora gv (bytes, ob) h;
         data_at esh (tarray tuchar (Zlength bytes)) (bytes_val bytes) entries;
         data_at osh t_obs (obs_val ob) observation; data_at Tsh t_result rold out))%assert.
  { Exists (@nil answer) initial_state (Zrepeat 0 16).
    rewrite (proj2 (Z.ltb_lt 0 (Zlength bytes))) by lia. rewrite run_start by auto.
    entailer!. split; repeat constructor; unfold u64_ok; rep_lia. }
  { (* byte i *)
    cbv beta. Intros h state last.
    match goal with H: run _ _ h = Some (if _ then _ else _) |- _ =>
      rewrite (proj2 (Z.ltb_lt i (Zlength bytes))) in H by lia; rename H into Hrun end.
    assert (Ebi: Znth i (bytes_val bytes) = Vint (Int.repr (Znth i bytes)))
      by (unfold bytes_val; rewrite Znth_map by lia; reflexivity).
    assert (Bi: byte_ok (Znth i bytes)) by (apply Forall_Znth; auto; lia).
    forward.
    { rewrite Znth_bytes_val by lia. entailer!. all: first [ apply tc_byte; auto | unfold byte_ok in *; rep_lia ]. }
    rewrite Znth_bytes_val by lia.
    forward.
    rewrite Int.unsigned_repr by (unfold byte_ok in Bi; rep_lia).
    forward.
    assert (TO: Int64.add (Int64.repr (Int.unsigned (Int.repr 44))) (Int64.repr i) = Int64.repr (44 + i))
      by (rewrite add64_repr; reflexivity).
    rewrite TO; clear TO.
    forward_for_simple_bound 16 (EX k: Z, EX h': list answer, EX cur: list Z,
      PROP (run (bytes, ob) (start (bytes, ob)) h' = Some (stream_at bytes i state cur); Zlength cur = k;
            Forall u64_ok cur)
      LOCAL (temp _offset (vl (44 + i)); temp _byte (vl (Znth i bytes)); temp _i (vl i);
             temp _table_length (vl (44 + Zlength bytes)); temp _routing_authority (vl (o_routing ob));
             temp _sample_id (vl (o_sample_id ob)); temp _apic_base (vl (o_apic_base ob));
             temp _available (vl (o_available ob)); temp _cpuid_edx (vl (o_cpuid_edx ob));
             temp _executing (vl (o_executing ob));
             lvar _bound (tarray tulong 6) v_bound; lvar _nmi_policy (tarray tulong 5) v_nmi_policy;
             lvar _nmi (tarray tulong 4) v_nmi; lvar _result (tarray tulong 16) v_result;
             lvar _state (tarray tulong 12) v_state; gvars gv;
             temp _entries entries; temp _length (vl (Zlength bytes)); temp _out out)
      SEP (data_at_ Tsh (tarray tulong 6) v_bound; data_at_ Tsh (tarray tulong 5) v_nmi_policy;
           data_at_ Tsh (tarray tulong 4) v_nmi;
           data_at Tsh (tarray tulong 16) (map vl cur ++ sublist k 16 (map vl last)) v_result;
           data_at Tsh (tarray tulong 12) (map vl state) v_state;
           Ora gv (bytes, ob) h';
           data_at esh (tarray tuchar (Zlength bytes)) (bytes_val bytes) entries;
           data_at osh t_obs (obs_val ob) observation; data_at Tsh t_result rold out))%assert.
    { Exists h (@nil Z).
      replace (map vl [] ++ sublist 0 16 (map vl last)) with (map vl last) by list_solve.
      entailer!. }
    { cbv beta. Intros.
      match goal with H: Zlength cur = ?k |- _ => subst k end.
      forward. forward. forward. forward. forward. forward. forward. forward. forward. forward. forward. forward.
      freeze FR := (data_at_ _ _ v_bound) (data_at_ _ _ v_nmi_policy) (data_at_ _ _ v_nmi) (data_at _ _ _ v_result)
        (data_at _ _ _ v_state) (data_at _ _ _ entries) (data_at _ _ _ observation) (data_at _ _ _ out).
      forward_call (gv, (bytes, ob), h', state, 44 + Zlength bytes, o_executing ob, 44 + i, Znth i bytes,
        Zlength cur).
      { apply stream_call; [ assumption | lia ]. }
      Intros v. thaw FR.
      forward.
      Exists (h' ++ [(Step state (44 + Zlength bytes) (o_executing ob) (44 + i) (Znth i bytes) (Zlength cur), v)])
        (cur ++ [v]).
      entailer!.
      { split; [ apply stream_answer; [ assumption | lia ] |
          split; [ rewrite Zlength_app, Zlength_cons, Zlength_nil; lia |
                   apply Forall_app; split; [ assumption | constructor; auto ] ] ]. }
      apply derives_refl'. f_equal. apply upd_prefix; [ lia | rewrite Zlength_map; auto ]. }
    Intros h' r.
    match goal with H: run _ _ h' = Some (stream_at _ _ _ r) |- _ => rename H into Hr end.
    match goal with H: Zlength r = 16 |- _ => rename H into Lr end.
    match goal with H: Forall u64_ok r |- _ => rename H into Ur end.
    rewrite stream_at_end in Hr by auto.
    replace (map vl r ++ sublist 16 16 (map vl last)) with (map vl r) by list_solve.
    forward.
    forward_if.
    { (* the transition is not well formed *)
      z64.
      forward_call (out, rold, (3, 0, 44 + i, 0, 0, 0)).
      { unfold u64_ok; repeat split; rep_lia. }
      forward.
      Exists h' (reject 3 0 (44 + i)).
      close_ret INV.
      apply consume_ret. rewrite Hr, se_r0 by assumption. reflexivity. }
    z64.
    forward.
    forward_if.
    { (* the stream rejects *)
      z64.
      forward.
      forward_call (out, rold, (2, Znth 2 r, 44 + i, 0, 0, 0)).
      { repeat split; u64. }
      forward.
      Exists h' (reject 2 (Znth 2 r) (44 + i)).
      close_ret INV.
      apply consume_ret. rewrite Hr, se_r1 by assumption. reflexivity. }
    z64.
    forward_if (temp _t'9 (Vint (Int.repr (if i + 1 =? Zlength bytes then 3 else 1)))).
    { forward. entailer!. z64. zrw. reflexivity. }
    { forward. entailer!. z64. zrw. reflexivity. }
    forward.
    forward_if (temp _t'10 (Vint (Int.repr (b2z (negb (Znth 1 r =? (if i + 1 =? Zlength bytes then 3 else 1)) ||
                                                  negb (Znth 2 r =? 0)))))).
    { forward. entailer!. z64. zrw. reflexivity. }
    { forward. forward. entailer!. z64. zrw. bnorm. bclose. }
    forward_if (temp _t'11 (Vint (Int.repr (b2z (negb (Znth 1 r =? (if i + 1 =? Zlength bytes then 3 else 1)) ||
                                                  negb (Znth 2 r =? 0) || negb (Znth 3 r =? 44 + i + 1)))))).
    { forward. entailer!. bfix. zrw. reflexivity. }
    { forward. forward. entailer!. bfix. zrw. bnorm. bclose. }
    forward_if (temp _t'12 (Vint (Int.repr (b2z (se_bad_cond bytes i r))))).
    { forward. entailer!. bfix. unfold se_bad_cond. zrw. reflexivity. }
    { forward. forward. entailer!. bfix. unfold se_bad_cond. zrw. bnorm. bclose. }
    forward_if.
    { (* the transition is not well formed *)
      bfix.
      forward_call (out, rold, (3, 0, 44 + i, 0, 0, 0)).
      { unfold u64_ok; repeat split; rep_lia. }
      forward.
      Exists h' (reject 3 0 (44 + i)).
      close_ret INV.
      apply consume_ret. rewrite Hr, se_bad by assumption. reflexivity. }
    bfix.
    rewrite (se_ok bytes i r) in Hr by assumption.
    rewrite se_next in Hr by lia.
    abbreviate_semax. deadvars!.
    forward_for_simple_bound 12 (EX w: Z,
      PROP ()
      LOCAL (temp _i (vl i);
             temp _table_length (vl (44 + Zlength bytes)); temp _routing_authority (vl (o_routing ob));
             temp _sample_id (vl (o_sample_id ob)); temp _apic_base (vl (o_apic_base ob));
             temp _available (vl (o_available ob)); temp _cpuid_edx (vl (o_cpuid_edx ob));
             temp _executing (vl (o_executing ob));
             lvar _bound (tarray tulong 6) v_bound; lvar _nmi_policy (tarray tulong 5) v_nmi_policy;
             lvar _nmi (tarray tulong 4) v_nmi; lvar _result (tarray tulong 16) v_result;
             lvar _state (tarray tulong 12) v_state; gvars gv;
             temp _entries entries; temp _length (vl (Zlength bytes)); temp _out out)
      SEP (data_at_ Tsh (tarray tulong 6) v_bound; data_at_ Tsh (tarray tulong 5) v_nmi_policy;
           data_at_ Tsh (tarray tulong 4) v_nmi;
           data_at Tsh (tarray tulong 16) (map vl r) v_result;
           data_at Tsh (tarray tulong 12) (map vl (sublist 3 (3 + w) r) ++ sublist w 12 (map vl state)) v_state;
           Ora gv (bytes, ob) h';
           data_at esh (tarray tuchar (Zlength bytes)) (bytes_val bytes) entries;
           data_at osh t_obs (obs_val ob) observation; data_at Tsh t_result rold out))%assert.
    { replace (map vl (sublist 3 (3 + 0) r) ++ sublist 0 12 (map vl state)) with (map vl state) by list_solve.
      entailer!. }
    { cbv beta. Intros.
      forward. forward.
      entailer!.
      apply derives_refl'. f_equal. apply upd_copy; auto; lia. }
    replace (map vl (sublist 3 (3 + 12) r) ++ sublist 12 12 (map vl state)) with (map vl (sublist 3 15 r)) by list_solve.
    Exists h' (sublist 3 15 r) r.
    entailer!.
    split; [ list_solve | apply Forall_sublist; auto ]. }
  (* the record walk *)
  Intros h state last.
  match goal with H: run _ _ h = Some (if _ then _ else _) |- _ =>
    rewrite Z.ltb_irrefl in H; rename H into Hrun end.
  match goal with H: Forall u64_ok state |- _ => rename H into Us end.
  match goal with H: Zlength state = 12 |- _ => rename H into Ls end.
  forward. forward. forward. forward. forward. forward.
  match goal with |- context [data_at Tsh (tarray tulong 4) ?X v_nmi] =>
    replace X with (map vl [0; 0; 0; 0]) by (unfold vl; reflexivity) end.
  deadvars!.
  forward_while (EX pos: Z, EX count: Z, EX nmi: list Z,
    PROP (0 <= pos <= Zlength bytes; 0 <= count <= pos; Zlength nmi = 4; walk_inv bytes pos count nmi)
    LOCAL (temp _offset__1 (Vlong (Int64.repr pos)); temp _nmi_count (Vlong (Int64.repr count));
           temp _table_length (vl (44 + Zlength bytes)); temp _routing_authority (vl (o_routing ob));
           temp _sample_id (vl (o_sample_id ob)); temp _apic_base (vl (o_apic_base ob));
           temp _available (vl (o_available ob)); temp _cpuid_edx (vl (o_cpuid_edx ob));
           temp _executing (vl (o_executing ob));
           lvar _bound (tarray tulong 6) v_bound; lvar _nmi_policy (tarray tulong 5) v_nmi_policy;
           lvar _nmi (tarray tulong 4) v_nmi; lvar _result (tarray tulong 16) v_result;
           lvar _state (tarray tulong 12) v_state; gvars gv;
           temp _entries entries; temp _length (vl (Zlength bytes)); temp _out out)
    SEP (data_at_ Tsh (tarray tulong 6) v_bound; data_at_ Tsh (tarray tulong 5) v_nmi_policy;
         data_at Tsh (tarray tulong 4) (map vl nmi) v_nmi;
         data_at Tsh (tarray tulong 16) (map vl last) v_result;
         data_at Tsh (tarray tulong 12) (map vl state) v_state;
         Ora gv (bytes, ob) h;
         data_at esh (tarray tuchar (Zlength bytes)) (bytes_val bytes) entries;
         data_at osh t_obs (obs_val ob) observation; data_at Tsh t_result rold out))%assert.
  { Exists 0 0 [0; 0; 0; 0]. entailer!. apply walk_start. }
  { entailer!. }
  { (* one record *)
    z64.
    forward_if.
    { (* a truncated record *)
      z64. forward.
      forward_call (out, rold, (3, 0, Znth 0 state, 0, 0, 0)).
      { repeat split; u64. }
      forward.
      Exists h (reject 3 0 (Znth 0 state)).
      close_ret INV.
      apply consume_ret. rewrite Hrun, after_none; [ reflexivity | ].
      z64. apply (walk_short bytes pos count nmi); auto; lia. }
    z64.
    assert (B1: byte_ok (Znth (pos + 1) bytes)) by (apply Forall_Znth; auto; lia).
    assert (B0: byte_ok (Znth pos bytes)) by (apply Forall_Znth; auto; lia).
    assert (B1': 0 <= Znth (pos + 1) bytes <= 255) by (unfold byte_ok in B1; rep_lia).
    forward.
    { rewrite Znth_bytes_val by lia. entailer!. all: first [ apply tc_byte; auto | unfold byte_ok in *; rep_lia ]. }
    rewrite Znth_bytes_val by lia.
    forward.
    rewrite Int.unsigned_repr by (unfold byte_ok in B1; rep_lia).
    forward_if (temp _t'15 (Vint (Int.repr (b2z ((Znth (pos + 1) bytes <? 2) ||
                                                  (Zlength bytes - pos <? Znth (pos + 1) bytes)))))).
    { forward. entailer!. z64. zrw. reflexivity. }
    { forward. entailer!. z64. zrw. bnorm. bclose. }
    forward_if.
    { (* a bad record length *)
      bfix. forward.
      forward_call (out, rold, (3, 0, Znth 0 state, 0, 0, 0)).
      { repeat split; u64. }
      forward.
      Exists h (reject 3 0 (Znth 0 state)).
      close_ret INV.
      apply consume_ret. rewrite Hrun, after_none; [ reflexivity | ].
      apply (walk_badlen bytes pos count nmi); auto; try lia.
      all: match goal with H: (_ || _)%bool = true |- _ =>
             apply orb_true_iff in H; destruct H as [H | H]; apply Z.ltb_lt in H; [ left | right ]; lia end. }
    bfix.
    match goal with H: ((_ <? 2) || _)%bool = false |- _ =>
      apply orb_false_iff in H; destruct H as [Lb1 Lb2]; apply Z.ltb_ge in Lb1, Lb2 end.
    assert (B0': 0 <= Znth pos bytes <= 255) by (unfold byte_ok in B0; rep_lia).
    forward.
    { rewrite Znth_bytes_val by lia. entailer!. all: first [ apply tc_byte; auto | unfold byte_ok in *; rep_lia ]. }
    rewrite Znth_bytes_val by lia.
    forward_if (EX count': Z, EX nmi': list Z,
      PROP (0 <= count' <= pos + Znth (pos + 1) bytes; Zlength nmi' = 4;
            walk_inv bytes (pos + Znth (pos + 1) bytes) count' nmi')
      LOCAL (temp _record_length (vl (Znth (pos + 1) bytes)); temp _offset__1 (Vlong (Int64.repr pos)); temp _nmi_count (Vlong (Int64.repr count'));
             temp _table_length (vl (44 + Zlength bytes)); temp _routing_authority (vl (o_routing ob));
             temp _sample_id (vl (o_sample_id ob)); temp _apic_base (vl (o_apic_base ob));
             temp _available (vl (o_available ob)); temp _cpuid_edx (vl (o_cpuid_edx ob));
             temp _executing (vl (o_executing ob));
             lvar _bound (tarray tulong 6) v_bound; lvar _nmi_policy (tarray tulong 5) v_nmi_policy;
             lvar _nmi (tarray tulong 4) v_nmi; lvar _result (tarray tulong 16) v_result;
             lvar _state (tarray tulong 12) v_state; gvars gv;
             temp _entries entries; temp _length (vl (Zlength bytes)); temp _out out)
      SEP (data_at_ Tsh (tarray tulong 6) v_bound; data_at_ Tsh (tarray tulong 5) v_nmi_policy;
             data_at Tsh (tarray tulong 4) (map vl nmi') v_nmi;
             data_at Tsh (tarray tulong 16) (map vl last) v_result;
             data_at Tsh (tarray tulong 12) (map vl state) v_state;
             Ora gv (bytes, ob) h;
             data_at esh (tarray tuchar (Zlength bytes)) (bytes_val bytes) entries;
             data_at osh t_obs (obs_val ob) observation; data_at Tsh t_result rold out)).
    { (* an NMI record *)
      z64.
      forward_if.
      { (* of the wrong length *)
        z64. forward.
        forward_call (out, rold, (3, 0, Znth 0 state, 0, 0, 0)).
        { repeat split; u64. }
        forward.
        Exists h (reject 3 0 (Znth 0 state)).
        close_ret INV.
        apply consume_ret. rewrite Hrun, after_none; [ reflexivity | ].
        z64. apply (walk_nmi_bad bytes pos count nmi); auto; lia. }
      z64.
      forward.
      forward_for_simple_bound 6 (EX k: Z,
        PROP ()
        LOCAL (temp _packed (vl (packk bytes pos (Z.to_nat k))); temp _record_length (vl (Znth (pos + 1) bytes));
               temp _offset__1 (Vlong (Int64.repr pos)); temp _nmi_count (Vlong (Int64.repr count)); temp _table_length (vl (44 + Zlength bytes)); temp _routing_authority (vl (o_routing ob));
             temp _sample_id (vl (o_sample_id ob)); temp _apic_base (vl (o_apic_base ob));
             temp _available (vl (o_available ob)); temp _cpuid_edx (vl (o_cpuid_edx ob));
             temp _executing (vl (o_executing ob));
             lvar _bound (tarray tulong 6) v_bound; lvar _nmi_policy (tarray tulong 5) v_nmi_policy;
             lvar _nmi (tarray tulong 4) v_nmi; lvar _result (tarray tulong 16) v_result;
             lvar _state (tarray tulong 12) v_state; gvars gv;
             temp _entries entries; temp _length (vl (Zlength bytes)); temp _out out)
        SEP (data_at_ Tsh (tarray tulong 6) v_bound; data_at_ Tsh (tarray tulong 5) v_nmi_policy;
             data_at Tsh (tarray tulong 4) (map vl nmi) v_nmi;
             data_at Tsh (tarray tulong 16) (map vl last) v_result;
             data_at Tsh (tarray tulong 12) (map vl state) v_state;
             Ora gv (bytes, ob) h;
             data_at esh (tarray tuchar (Zlength bytes)) (bytes_val bytes) entries;
             data_at osh t_obs (obs_val ob) observation; data_at Tsh t_result rold out))%assert.
      { entailer!. }
      { match goal with H: 0 <= ?k < 6 |- _ =>
          assert (Bk: byte_ok (Znth (pos + k) bytes)) by (apply Forall_Znth; auto; lia) end.
        forward.
        { rewrite Znth_bytes_val by lia. entailer!. all: first [ apply tc_byte; auto | unfold byte_ok in *; rep_lia ]. }
        rewrite Znth_bytes_val by lia.
        forward.
        { entailer!. apply shift_ok; lia. }
        entailer!. apply pack_goal; [ lia | unfold byte_ok in Bk; rep_lia ]. }
      forward_if (PROP ()
        LOCAL (temp _packed (vl (packk bytes pos (Z.to_nat 6))); temp _record_length (vl (Znth (pos + 1) bytes));
               temp _offset__1 (Vlong (Int64.repr pos)); temp _nmi_count (Vlong (Int64.repr count)); temp _table_length (vl (44 + Zlength bytes)); temp _routing_authority (vl (o_routing ob));
             temp _sample_id (vl (o_sample_id ob)); temp _apic_base (vl (o_apic_base ob));
             temp _available (vl (o_available ob)); temp _cpuid_edx (vl (o_cpuid_edx ob));
             temp _executing (vl (o_executing ob));
             lvar _bound (tarray tulong 6) v_bound; lvar _nmi_policy (tarray tulong 5) v_nmi_policy;
             lvar _nmi (tarray tulong 4) v_nmi; lvar _result (tarray tulong 16) v_result;
             lvar _state (tarray tulong 12) v_state; gvars gv;
             temp _entries entries; temp _length (vl (Zlength bytes)); temp _out out)
        SEP (data_at_ Tsh (tarray tulong 6) v_bound; data_at_ Tsh (tarray tulong 5) v_nmi_policy;
             data_at Tsh (tarray tulong 4) (map vl (if count <? 4 then upd_Znth count nmi (pack6 bytes pos) else nmi)) v_nmi;
             data_at Tsh (tarray tulong 16) (map vl last) v_result;
             data_at Tsh (tarray tulong 12) (map vl state) v_state;
             Ora gv (bytes, ob) h;
             data_at esh (tarray tuchar (Zlength bytes)) (bytes_val bytes) entries;
             data_at osh t_obs (obs_val ob) observation; data_at Tsh t_result rold out)).
      { z64. forward. rewrite (proj2 (Z.ltb_lt count 4)) by lia.
        entailer!. apply derives_refl'. f_equal. exact (nmi_store nmi count (pack6 bytes pos)). }
      { z64. forward. rewrite (proj2 (Z.ltb_ge count 4)) by lia. entailer!. }
      forward.
      Exists (count + 1) (if count <? 4 then upd_Znth count nmi (pack6 bytes pos) else nmi).
      entailer!.
      split; [ destruct (count <? 4); list_solve | apply walk_nmi; auto; lia ]. }
    { (* another record *)
      z64. forward.
      Exists count nmi.
      entailer!.
      apply walk_other; auto; lia. }
    Intros count' nmi'.
    forward.
    Exists (pos + Znth (pos + 1) bytes, count', nmi').
    entailer!. all: lia. }
  (* after the walk *)
  z64.
  match goal with H: Zlength nmi = 4 |- _ => rename H into Ln end.
  assert (Rec: records bytes = Some (count, nmi)) by (eapply walk_done; eauto; lia).
  rewrite (after_some _ _ _ _ _ Rec) in Hrun.
  deadvars!.
  rewrite (data_at__eq _ (tarray tulong 5) v_nmi_policy).
  change (default_val (tarray tulong 5)) with (Zrepeat Vundef 5).
  forward_for_simple_bound 5 (EX k: Z, EX h': list answer, EX cur: list Z,
    PROP (run (bytes, ob) (start (bytes, ob)) h' = Some (policy_at last state count nmi cur); Zlength cur = k;
          Forall u64_ok cur)
    LOCAL (temp _nmi_count (Vlong (Int64.repr count)); temp _table_length (vl (44 + Zlength bytes));
           temp _routing_authority (vl (o_routing ob));
           temp _sample_id (vl (o_sample_id ob)); temp _apic_base (vl (o_apic_base ob));
           temp _available (vl (o_available ob)); temp _cpuid_edx (vl (o_cpuid_edx ob));
           temp _executing (vl (o_executing ob));
           lvar _bound (tarray tulong 6) v_bound; lvar _nmi_policy (tarray tulong 5) v_nmi_policy;
           lvar _nmi (tarray tulong 4) v_nmi; lvar _result (tarray tulong 16) v_result;
           lvar _state (tarray tulong 12) v_state; gvars gv; temp _out out)
    SEP (data_at_ Tsh (tarray tulong 6) v_bound;
         data_at Tsh (tarray tulong 5) (map vl cur ++ sublist k 5 (Zrepeat Vundef 5)) v_nmi_policy;
         data_at Tsh (tarray tulong 4) (map vl nmi) v_nmi;
         data_at Tsh (tarray tulong 16) (map vl last) v_result;
         data_at Tsh (tarray tulong 12) (map vl state) v_state;
         Ora gv (bytes, ob) h';
         data_at esh (tarray tuchar (Zlength bytes)) (bytes_val bytes) entries;
         data_at osh t_obs (obs_val ob) observation; data_at Tsh t_result rold out))%assert.
  { Exists h (@nil Z).
    replace (map vl [] ++ sublist 0 5 (Zrepeat Vundef 5)) with (Zrepeat Vundef 5) by list_solve.
    entailer!. }
  { cbv beta. Intros.
    match goal with H: Zlength cur = ?k |- _ => subst k end.
    forward. forward. forward. forward.
    freeze FR := (data_at_ _ _ v_bound) (data_at _ _ _ v_nmi_policy) (data_at _ _ _ v_nmi) (data_at _ _ _ v_result)
      (data_at _ _ _ v_state) (data_at _ _ _ entries) (data_at _ _ _ observation) (data_at _ _ _ out).
    forward_call (gv, (bytes, ob), h', count, nmi, o_routing ob, Zlength cur).
    { eapply policy_call; [ eassumption | lia ]. }
    Intros v. thaw FR.
    forward.
    Exists (h' ++ [(Nmi count nmi (o_routing ob) (Zlength cur), v)]) (cur ++ [v]).
    entailer!.
    { split; [ eapply policy_answer; [ eassumption | lia ] |
        split; [ rewrite Zlength_app, Zlength_cons, Zlength_nil; lia |
                 apply Forall_app; split; [ assumption | constructor; auto ] ] ]. }
    apply derives_refl'. f_equal. apply upd_prefix; [ lia | reflexivity ]. }
  Intros h' p.
  match goal with H: run _ _ h' = Some (policy_at _ _ _ _ p) |- _ => rename H into Hp end.
  match goal with H: Zlength p = 5 |- _ => rename H into Lp end.
  match goal with H: Forall u64_ok p |- _ => rename H into Up end.
  rewrite policy_at_end in Hp by auto.
  replace (map vl p ++ sublist 5 5 (Zrepeat Vundef 5)) with (map vl p) by list_solve.
  forward.
  forward_if (temp _t'19 (Vint (Int.repr (b2z (negb (Znth 0 p =? 1) || (1 <? Znth 3 p)))))).
  { forward. entailer!. z64. zrw. reflexivity. }
  { forward. forward. entailer!. z64. zrw. bnorm. bclose. }
  forward_if (temp _t'20 (Vint (Int.repr (b2z (pe_c1 p))))).
  { forward. entailer!. bfix. unfold pe_c1. zrw. reflexivity. }
  { forward. forward. entailer!. bfix. unfold pe_c1. zrw. bnorm. bclose. }
  forward_if.
  { (* the policy answers are not well formed *)
    bfix. forward.
    forward_call (out, rold, (3, 0, Znth 0 state, 0, 0, 0)).
    { repeat split; u64. }
    forward.
    Exists h' (reject 3 0 (Znth 0 state)).
    close_ret INV.
    apply consume_ret. rewrite Hp, pe_1 by assumption. reflexivity. }
  bfix.
  forward.
  forward_if.
  { (* the NMI routing was not quarantined *)
    z64. forward. forward.
    forward_call (out, rold, (5, Znth 2 p, Znth 0 state, 0, 0, 0)).
    { repeat split; u64. }
    forward.
    Exists h' (reject 5 (Znth 2 p) (Znth 0 state)).
    close_ret INV.
    apply consume_ret. rewrite Hp, pe_2 by assumption. reflexivity. }
  z64.
  forward.
  forward_if (temp _t'23 (Vint (Int.repr (b2z (negb (Znth 2 p =? 0) || negb (Znth 3 p =? 1)))))).
  { forward. entailer!. z64. zrw. reflexivity. }
  { forward. forward. entailer!. z64. zrw. bnorm. bclose. }
  forward_if (temp _t'24 (Vint (Int.repr (b2z (pe_c3 p))))).
  { forward. entailer!. bfix. unfold pe_c3. zrw. reflexivity. }
  { forward. forward. entailer!. bfix. unfold pe_c3. zrw. bnorm. bclose. }
  forward_if.
  { (* the policy answers are not well formed *)
    bfix. forward.
    forward_call (out, rold, (3, 0, Znth 0 state, 0, 0, 0)).
    { repeat split; u64. }
    forward.
    Exists h' (reject 3 0 (Znth 0 state)).
    close_ret INV.
    apply consume_ret. rewrite Hp, pe_3 by assumption. reflexivity. }
  bfix.
  rewrite (pe_ok last state p) in Hp by assumption.
  rewrite <- (bound_at_nil ob) in Hp.
  (* the finish *)
  deadvars!.
  rewrite (data_at__eq _ (tarray tulong 6) v_bound).
  change (default_val (tarray tulong 6)) with (Zrepeat Vundef 6).
  forward_for_simple_bound 6 (EX k: Z, EX h'': list answer, EX cur: list Z,
    PROP (run (bytes, ob) (start (bytes, ob)) h'' = Some (bound_at ob last state cur); Zlength cur = k;
          Forall u64_ok cur)
    LOCAL (temp _table_length (vl (44 + Zlength bytes));
           temp _sample_id (vl (o_sample_id ob)); temp _apic_base (vl (o_apic_base ob));
           temp _available (vl (o_available ob)); temp _cpuid_edx (vl (o_cpuid_edx ob));
           temp _executing (vl (o_executing ob));
           lvar _bound (tarray tulong 6) v_bound; lvar _nmi_policy (tarray tulong 5) v_nmi_policy;
           lvar _nmi (tarray tulong 4) v_nmi; lvar _result (tarray tulong 16) v_result;
           lvar _state (tarray tulong 12) v_state; gvars gv; temp _out out)
    SEP (data_at Tsh (tarray tulong 6) (map vl cur ++ sublist k 6 (Zrepeat Vundef 6)) v_bound;
         data_at Tsh (tarray tulong 5) (map vl p) v_nmi_policy;
         data_at Tsh (tarray tulong 4) (map vl nmi) v_nmi;
         data_at Tsh (tarray tulong 16) (map vl last) v_result;
         data_at Tsh (tarray tulong 12) (map vl state) v_state;
         Ora gv (bytes, ob) h'';
         data_at esh (tarray tuchar (Zlength bytes)) (bytes_val bytes) entries;
         data_at osh t_obs (obs_val ob) observation; data_at Tsh t_result rold out))%assert.
  { Exists h' (@nil Z).
    replace (map vl [] ++ sublist 0 6 (Zrepeat Vundef 6)) with (Zrepeat Vundef 6) by list_solve.
    entailer!. }
  { cbv beta. Intros.
    match goal with H: Zlength cur = ?k |- _ => subst k end.
    forward. forward. forward. forward. forward. forward. forward. forward. forward. forward. forward. forward.
    forward. forward.
    freeze FR := (data_at _ _ _ v_bound) (data_at _ _ _ v_nmi_policy) (data_at _ _ _ v_nmi) (data_at _ _ _ v_result)
      (data_at _ _ _ v_state) (data_at _ _ _ entries) (data_at _ _ _ observation) (data_at _ _ _ out).
    forward_call (gv, (bytes, ob), h'', Znth 1 last, Znth 2 last, state, 44 + Zlength bytes, o_executing ob,
      o_cpuid_edx ob, o_available ob, o_apic_base ob, o_sample_id ob, Zlength cur).
    { apply bound_call; [ assumption | lia ]. }
    Intros v. thaw FR.
    forward.
    Exists (h'' ++ [(Finish (Znth 1 last) (Znth 2 last) state (44 + Zlength bytes) (o_executing ob) (o_cpuid_edx ob)
                     (o_available ob) (o_apic_base ob) (o_sample_id ob) (Zlength cur), v)]) (cur ++ [v]).
    entailer!.
    { split; [ apply bound_answer; [ assumption | lia ] |
        split; [ rewrite Zlength_app, Zlength_cons, Zlength_nil; lia |
                 apply Forall_app; split; [ assumption | constructor; auto ] ] ]. }
    apply derives_refl'. f_equal. apply upd_prefix; [ lia | reflexivity ]. }
  Intros h'' b.
  match goal with H: run _ _ h'' = Some (bound_at _ _ _ b) |- _ => rename H into Hb end.
  match goal with H: Zlength b = 6 |- _ => rename H into Lb end.
  match goal with H: Forall u64_ok b |- _ => rename H into Ub end.
  rewrite bound_at_end in Hb by auto.
  replace (map vl b ++ sublist 6 6 (Zrepeat Vundef 6)) with (map vl b) by list_solve.
  forward.
  forward_if (temp _t'27 (Vint (Int.repr (b2z (be_c1 b))))).
  { forward. entailer!. z64. unfold be_c1. zrw. reflexivity. }
  { forward. forward. entailer!. z64. unfold be_c1. zrw. bnorm. bclose. }
  forward_if.
  { (* the finish answers are not well formed *)
    bfix. forward.
    forward_call (out, rold, (3, 0, Znth 0 state, 0, 0, 0)).
    { repeat split; u64. }
    forward.
    Exists h'' (reject 3 0 (Znth 0 state)).
    close_ret INV.
    apply consume_ret. rewrite Hb, be_1 by assumption. reflexivity. }
  bfix.
  forward.
  forward_if (temp _t'29 (Vint (Int.repr (b2z (be_c2 b))))).
  { forward. entailer!. z64. unfold be_c2. zrw. reflexivity. }
  { forward. forward. entailer!. z64. unfold be_c2. zrw. bnorm. bclose. }
  forward_if.
  { (* the BSP binding rejects *)
    bfix. forward. forward.
    forward_call (out, rold, (4, Znth 2 b, Znth 0 state, 0, 0, 0)).
    { repeat split; u64. }
    forward.
    Exists h'' (reject 4 (Znth 2 b) (Znth 0 state)).
    close_ret INV.
    apply consume_ret. rewrite Hb, be_2 by assumption. reflexivity. }
  bfix.
  forward.
  forward_if (temp _t'31 (Vint (Int.repr (b2z (negb (Znth 1 b =? 1) || negb (Znth 2 b =? o_executing ob)))))).
  { forward. entailer!. z64. zrw. reflexivity. }
  { forward. forward. entailer!. z64. zrw. bnorm. bclose. }
  forward_if (temp _t'32 (Vint (Int.repr (b2z (negb (Znth 1 b =? 1) || negb (Znth 2 b =? o_executing ob) ||
                                                negb (Znth 3 b =? Znth 6 state)))))).
  { forward. entailer!. bfix. zrw. reflexivity. }
  { forward. forward. forward. entailer!. bfix. zrw. bnorm. bclose. }
  forward_if (temp _t'33 (Vint (Int.repr (b2z (be_c3 ob state b))))).
  { forward. entailer!. bfix. unfold be_c3. zrw. reflexivity. }
  { forward. forward. entailer!. bfix. unfold be_c3. zrw. bnorm. bclose. }
  forward_if.
  { (* the finish answers are not well formed *)
    bfix. forward.
    forward_call (out, rold, (3, 0, Znth 0 state, 0, 0, 0)).
    { repeat split; u64. }
    forward.
    Exists h'' (reject 3 0 (Znth 0 state)).
    close_ret INV.
    apply consume_ret. rewrite Hb, be_3 by assumption. reflexivity. }
  bfix.
  forward. forward. forward. forward.
  forward_call (out, rold, (0, 0, Znth 0 state, Znth 2 b, Znth 3 b, Znth 4 b)).
  { repeat split; u64. }
  forward.
  Exists h'' (0, 0, Znth 0 state, Znth 2 b, Znth 3 b, Znth 4 b).
  close_ret INV.
  apply consume_ret. rewrite Hb, be_ok by assumption. reflexivity.
Qed.

Lemma body_madt_bind (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_madt_bind (madt_bind_spec Ora).
Proof.
  start_function.
  forward_call (gv, entries, esh, bytes, length, observation, osh, ob, out, rold).
  Intros vret. destruct vret as [h o].
  forward.
  Exists h o. entailer!.
Qed.
