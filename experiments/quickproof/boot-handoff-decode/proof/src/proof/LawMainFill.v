(* Law handoff_decode_exact: main's fills of the storage: the copy and the copy_expect array, the words a decoder
   alone reads and info_expect, the three bitmaps and the law's, the two states and the law's, each word any 64-bit
   value; then the records and the call (rest_ok). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosHandoff.harness.handoff_decode_exact.code.
Require Import LeanosHandoff.proof.Defs.
Require Import LeanosHandoff.proof.HandoffSpecs.
Require Import LeanosHandoff.proof.LawProg LeanosHandoff.proof.LawDefs LeanosHandoff.proof.LawFacts
  LeanosHandoff.proof.LawLib LeanosHandoff.proof.LawLib2 LeanosHandoff.proof.LawLib3 LeanosHandoff.proof.LawZero
  LeanosHandoff.proof.LawMainDefs LeanosHandoff.proof.LawMainPre LeanosHandoff.proof.LawMainPre2.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[local] Existing Instance LawProg.LCS.

(* An array being filled word by word. *)
Lemma fill_step: forall (cl: list Z) n i v (z: val), Zlength cl = i -> 0 <= i < n ->
  upd_Znth i (map vl cl ++ Zrepeat z (n - i)) (vl v) = map vl (cl ++ [v]) ++ Zrepeat z (n - (i + 1)).
Proof. intros. subst. list_solve. Qed.

Lemma fill_step': forall (cl: list Z) n i v (z: val), Zlength cl = i -> 0 <= i < n ->
  upd_Znth i (map vl cl ++ Zrepeat z (n - i)) (Vlong (Int64.repr v)) = map vl (cl ++ [v]) ++ Zrepeat z (n - (i + 1)).
Proof. intros. apply fill_step; auto. Qed.

Lemma fill_get: forall (cl: list Z) n i v (z: val), Zlength cl = i -> 0 <= i < n ->
  Znth i (map vl (cl ++ [v]) ++ Zrepeat z (n - (i + 1))) = vl v.
Proof. intros. subst. list_solve. Qed.

Lemma fill_done: forall (cl: list Z) n (z: val), Zlength cl = n -> map vl cl ++ Zrepeat z (n - n) = map vl cl.
Proof. intros. rewrite Z.sub_diag. simpl. rewrite app_nil_r. reflexivity. Qed.

Lemma data_at__words: forall sh n p, 0 <= n ->
  data_at_ sh (tarray tulong n) p = data_at sh (tarray tulong n) (map vl nil ++ Zrepeat Vundef (n - 0)) p.
Proof. intros. rewrite Z.sub_0_r. unfold data_at_, field_at_, data_at. f_equal. Qed.

(* The two states being filled, row k word by word. *)
Lemma rows_start: forall (sl: list (list Z)) (z: val) k, Zlength sl = k -> 0 <= k < 2 ->
  map (map vl) sl ++ Zrepeat (Zrepeat z 41) (2 - k) =
  map (map vl) sl ++ [map vl nil ++ Zrepeat z (41 - 0)] ++ Zrepeat (Zrepeat z 41) (2 - k - 1).
Proof. intros. subst. assert (Zlength sl = 0 \/ Zlength sl = 1) as [E | E] by lia; rewrite E; reflexivity. Qed.

Lemma rows_store: forall (d: Inhabitant (list val)) (A: list (list val)) (r: list Z) (z: val) (C: list (list val))
    k i v, Zlength A = k -> Zlength r = i -> 0 <= i < 41 ->
  upd_Znth k (A ++ [map vl r ++ Zrepeat z (41 - i)] ++ C)
    (upd_Znth i (@Znth _ d k (A ++ [map vl r ++ Zrepeat z (41 - i)] ++ C)) (vl v)) =
  A ++ [map vl (r ++ [v]) ++ Zrepeat z (41 - (i + 1))] ++ C.
Proof.
  intros d A r z C k i v LA Lr I.
  rewrite (Znth_dflt d Inhabitant_list) by list_solve.
  replace (Znth k (A ++ [map vl r ++ Zrepeat z (41 - i)] ++ C)) with (map vl r ++ Zrepeat z (41 - i)) by list_solve.
  rewrite fill_step by auto. list_solve.
Qed.

Lemma rows_get: forall (d1: Inhabitant (list val)) (d2: Inhabitant val) (A: list (list val)) (r: list Z) (z: val)
    (C: list (list val)) k i v, Zlength A = k -> Zlength r = i -> 0 <= i < 41 ->
  @Znth _ d2 i (@Znth _ d1 k (A ++ [map vl (r ++ [v]) ++ Zrepeat z (41 - (i + 1))] ++ C)) = vl v.
Proof.
  intros d1 d2 A r z C k i v LA Lr I.
  rewrite (Znth_dflt d1 Inhabitant_list) by list_solve.
  replace (Znth k (A ++ [map vl (r ++ [v]) ++ Zrepeat z (41 - (i + 1))] ++ C))
    with (map vl (r ++ [v]) ++ Zrepeat z (41 - (i + 1))) by list_solve.
  rewrite (Znth_dflt d2 Inhabitant_val) by list_solve.
  apply fill_get; auto.
Qed.

Lemma rows_done: forall (sl: list (list Z)) (r: list Z) (z: val) k, Zlength r = 41 ->
  map (map vl) sl ++ [map vl r ++ Zrepeat z (41 - 41)] ++ Zrepeat (Zrepeat z 41) (2 - k - 1) =
  map (map vl) (sl ++ [r]) ++ Zrepeat (Zrepeat z 41) (2 - (k + 1)).
Proof. intros. rewrite fill_done by auto. rewrite map_app. rewrite <- app_assoc. f_equal. f_equal. f_equal. lia. Qed.

Ltac fill_vl := rewrite ?fill_step, ?fill_step' by (auto; lia).

Lemma tail_fill {Espec: OracleKind} (TR: @rest_ok Espec): @fill_ok Espec.
Proof.
  intros gv cc mg ad T0 cd cp cep ip iep up bp rp sp vtr vlr vcr vpj Hx Pcp Pcep Pip Piep Pup Pbp Prp Psp.
  unfold fill_pre, s_fill. start_tail_main.
  set (X := x0 cc mg ad T0 cd).
  pose proof Hx as (Rcc & Rmg & Rad & Rtt & Rcd & Ext).
  assert (Rcl: copy_len X = 0 \/ copy_len X = 8192)
    by (unfold copy_len; destruct (i_call X); auto).
  assert (Ril: 0 <= info_len X <= 8192).
  { unfold info_len, is_alloc, X, x0; cbn [i_call i_total]. destruct (call_of cc) eqn:C; try lia;
      (assert (N: cc <> 0) by (intro; subst; discriminate); destruct (Ext N) as [E1 E2];
       split; [ apply Z.div_pos | apply Z.div_le_upper_bound ]; lia). }
  unfold fields0, lraw. Intros.
  (* the copy *)
  rewrite !(data_at__words Ews (copy_len X)) by lia.
  freeze_but (@nil ident) [cp; cep] F1.
  forward_for_simple_bound (copy_len X)
    (EX i: Z, EX cl: list Z,
     PROP (Zlength cl = i; Forall u64_ok cl)
     LOCAL (temp _m (gv _law); temp _copy_words (vi (copy_len X)); temp _copy cp; temp _copy_expect cep;
            temp _info_words (vi (info_len X)); temp _info ip; temp _info_expect iep; temp _usable up;
            temp _blocked bp; temp _reserved rp; temp _states sp;
            lvar _total_record tuint vtr; lvar _length_record tuint vlr; lvar _current_record tuint vcr;
            lvar _projection t_projection vpj; gvars gv)
     SEP (FRZL F1; data_at Ews (tarray tulong (copy_len X)) (map vl cl ++ Zrepeat Vundef (copy_len X - i)) cp;
          data_at Ews (tarray tulong (copy_len X)) (map vl cl ++ Zrepeat Vundef (copy_len X - i)) cep))%assert.
  { Exists (@nil Z). entailer!. }
  { forward_call tt. Intros v. vl_temps. forward. fill_vl.
    forward. { rewrite fill_get by (auto; lia). entailer!. }
    rewrite fill_get by (auto; lia). vl_temps. forward. fill_vl.
    Exists (cl ++ [v]). entailer!. split; [ list_solve | apply Forall_u64_app1; auto ]. }
  Intros cl. rewrite !fill_done by auto.
  thaw F1.
  (* the words a decoder alone reads *)
  rewrite !(data_at__words Ews (info_len X)) by lia.
  freeze_but (@nil ident) [ip; iep] F2.
  forward_for_simple_bound (info_len X)
    (EX i: Z, EX il: list Z,
     PROP (Zlength il = i; Forall u64_ok il)
     LOCAL (temp _m (gv _law); temp _copy_words (vi (copy_len X)); temp _copy cp; temp _copy_expect cep;
            temp _info_words (vi (info_len X)); temp _info ip; temp _info_expect iep; temp _usable up;
            temp _blocked bp; temp _reserved rp; temp _states sp;
            lvar _total_record tuint vtr; lvar _length_record tuint vlr; lvar _current_record tuint vcr;
            lvar _projection t_projection vpj; gvars gv)
     SEP (FRZL F2; data_at Ews (tarray tulong (info_len X)) (map vl il ++ Zrepeat Vundef (info_len X - i)) ip;
          data_at Ews (tarray tulong (info_len X)) (map vl il ++ Zrepeat Vundef (info_len X - i)) iep))%assert.
  { Exists (@nil Z). entailer!. }
  { forward_call tt. Intros v. vl_temps. forward. fill_vl.
    forward. { rewrite fill_get by (auto; lia). entailer!. }
    rewrite fill_get by (auto; lia). vl_temps. forward. fill_vl.
    Exists (il ++ [v]). entailer!. split; [ list_solve | apply Forall_u64_app1; auto ]. }
  Intros il. rewrite !fill_done by auto.
  thaw F2.
  (* the bitmaps *)
  rewrite !(data_at__words Ews 64) by lia.
  change (Zrepeat z64 64) with (map vl nil ++ Zrepeat z64 (64 - 0)).
  freeze_but [_usable_expect; _blocked_expect; _reserved_expect] [up; bp; rp] F3.
  forward_for_simple_bound 64
    (EX b: Z, EX ul: list Z, EX bl: list Z, EX rl: list Z,
     PROP (Zlength ul = b; Forall u64_ok ul; Zlength bl = b; Forall u64_ok bl; Zlength rl = b; Forall u64_ok rl)
     LOCAL (temp _m (gv _law); temp _copy_words (vi (copy_len X)); temp _copy cp; temp _copy_expect cep;
            temp _info_words (vi (info_len X)); temp _info ip; temp _info_expect iep; temp _usable up;
            temp _blocked bp; temp _reserved rp; temp _states sp;
            lvar _total_record tuint vtr; lvar _length_record tuint vlr; lvar _current_record tuint vcr;
            lvar _projection t_projection vpj; gvars gv)
     SEP (FRZL F3;
          data_at Ews (tarray tulong 64) (map vl ul ++ Zrepeat Vundef (64 - b)) up;
          data_at Ews (tarray tulong 64) (map vl bl ++ Zrepeat Vundef (64 - b)) bp;
          data_at Ews (tarray tulong 64) (map vl rl ++ Zrepeat Vundef (64 - b)) rp;
          field_at Ews t_law (DOT _usable_expect) (map vl ul ++ Zrepeat z64 (64 - b)) (gv _law);
          field_at Ews t_law (DOT _blocked_expect) (map vl bl ++ Zrepeat z64 (64 - b)) (gv _law);
          field_at Ews t_law (DOT _reserved_expect) (map vl rl ++ Zrepeat z64 (64 - b)) (gv _law)))%assert.
  { Exists (@nil Z) (@nil Z) (@nil Z). entailer!. }
  { forward_call tt. Intros u. vl_temps. forward. fill_vl.
    forward_call tt. Intros bv. vl_temps. forward. fill_vl.
    forward_call tt. Intros r. vl_temps. forward. fill_vl.
    forward. { rewrite fill_get by (auto; lia). entailer!. }
    rewrite fill_get by (auto; lia). vl_temps. forward. fill_vl.
    forward. { rewrite fill_get by (auto; lia). entailer!. }
    rewrite fill_get by (auto; lia). vl_temps. forward. fill_vl.
    forward. { rewrite fill_get by (auto; lia). entailer!. }
    rewrite fill_get by (auto; lia). vl_temps. forward. fill_vl.
    Exists (ul ++ [u]) (bl ++ [bv]) (rl ++ [r]). entailer!.
    split_and; try list_solve; apply Forall_u64_app1; auto. }
  Intros ul bl rl. rewrite !fill_done by auto.
  thaw F3.
  (* the states *)
  change (Zrepeat (Zrepeat z64 41) 2) with (map (map vl) nil ++ Zrepeat (Zrepeat z64 41) (2 - 0)).
  replace (data_at_ Ews t_states sp) with (data_at Ews t_states (map (map vl) nil ++ Zrepeat (Zrepeat Vundef 41) (2 - 0)) sp)
    by (unfold data_at_, field_at_, data_at; f_equal).
  freeze_but [_states_expect] [sp] F4.
  forward_for_simple_bound 2
    (EX k: Z, EX sl: list (list Z),
     PROP (Zlength sl = k; Forall state_ok sl)
     LOCAL (temp _m (gv _law); temp _copy_words (vi (copy_len X)); temp _copy cp; temp _copy_expect cep;
            temp _info_words (vi (info_len X)); temp _info ip; temp _info_expect iep; temp _usable up;
            temp _blocked bp; temp _reserved rp; temp _states sp;
            lvar _total_record tuint vtr; lvar _length_record tuint vlr; lvar _current_record tuint vcr;
            lvar _projection t_projection vpj; gvars gv)
     SEP (FRZL F4; data_at Ews t_states (map (map vl) sl ++ Zrepeat (Zrepeat Vundef 41) (2 - k)) sp;
          field_at Ews t_law (DOT _states_expect) (map (map vl) sl ++ Zrepeat (Zrepeat z64 41) (2 - k)) (gv _law)))%assert.
  { Exists (@nil (list Z)). entailer!. }
  { Intros. rewrite (rows_start sl Vundef i) by first [ assumption | lia ]. rewrite (rows_start sl z64 i) by first [ assumption | lia ].
    forward_for_simple_bound 41
      (EX j: Z, EX r: list Z,
       PROP (Zlength r = j; Forall u64_ok r)
       LOCAL (temp _k (vi i); temp _m (gv _law); temp _copy_words (vi (copy_len X)); temp _copy cp; temp _copy_expect cep;
            temp _info_words (vi (info_len X)); temp _info ip; temp _info_expect iep; temp _usable up;
            temp _blocked bp; temp _reserved rp; temp _states sp;
            lvar _total_record tuint vtr; lvar _length_record tuint vlr; lvar _current_record tuint vcr;
            lvar _projection t_projection vpj; gvars gv)
       SEP (FRZL F4;
            data_at Ews t_states (map (map vl) sl ++ [map vl r ++ Zrepeat Vundef (41 - j)] ++
                                  Zrepeat (Zrepeat Vundef 41) (2 - i - 1)) sp;
            field_at Ews t_law (DOT _states_expect) (map (map vl) sl ++ [map vl r ++ Zrepeat z64 (41 - j)] ++
                                  Zrepeat (Zrepeat z64 41) (2 - i - 1)) (gv _law)))%assert.
    { Exists (@nil Z). entailer!. }
    { Intros. forward_call tt. Intros v. vl_temps. forward.
      match goal with |- context [data_at Ews t_states ?V sp] =>
        replace V with (map (map vl) sl ++ [map vl (r ++ [v]) ++ Zrepeat Vundef (41 - (i0 + 1))] ++
                        Zrepeat (Zrepeat Vundef 41) (2 - i - 1))
          by (symmetry; apply rows_store; rewrite ?Zlength_map; auto; lia) end.
      forward.
      { rewrite rows_get by (rewrite ?Zlength_map; auto; lia). entailer!. }
      rewrite rows_get by (rewrite ?Zlength_map; auto; lia). vl_temps.
      forward.
      match goal with |- context [field_at Ews t_law (DOT _states_expect) ?V (gv _law)] =>
        replace V with (map (map vl) sl ++ [map vl (r ++ [v]) ++ Zrepeat z64 (41 - (i0 + 1))] ++
                        Zrepeat (Zrepeat z64 41) (2 - i - 1))
          by (symmetry; apply rows_store; rewrite ?Zlength_map; auto; lia) end.
      Exists (r ++ [v]). entailer!. split; [ list_solve | apply Forall_u64_app1; auto ]. }
    Intros r. rewrite !rows_done by auto.
    Exists (sl ++ [r]). entailer!. split; [ list_solve | apply Forall_app; split; auto; constructor; auto; split; auto ]. }
  Intros sl. rewrite Z.sub_diag. cbn [Zrepeat repeat Z.to_nat]. rewrite !app_nil_r.
  thaw F4.
  (* the rest of main *)
  set (x := xin cc mg ad T0 cd il cl ul bl rl sl 0 0 0).
  assert (Fx: filled x).
  { unfold filled, x, xin; cbn [i_copy i_info i_usable i_blocked i_reserved i_states].
    assert (Ls: Zlength sl = 2) by assumption.
    destruct sl as [ | r0 [ | r1 [ | r2 sl']]]; try (rewrite ?Zlength_cons, ?Zlength_nil in Ls; rep_lia).
    match goal with H: Forall state_ok _ |- _ => inversion H as [ | ? ? S0 H']; subst; inversion H' as [ | ? ? S1 _]; subst end.
    split_and; auto. }
  assert (Ox: x0_ok (call_code (i_call x)) (i_magic x) (i_address x) (i_total x) (i_candidate x))
    by (unfold x, xin; cbn [i_call i_magic i_address i_total i_candidate]; rewrite call_code_of by lia; exact Hx).
  eapply semax_pre; [ | apply (TR gv x cp cep ip iep up bp rp sp vtr vlr vcr vpj); auto ].
  unfold rest_pre, fields1, lraw. change (copy_len X) with (copy_len x). change (info_len X) with (info_len x).
  unfold x, xin, X, x0; cbn [i_call i_magic i_address i_total i_candidate i_copy i_info i_usable i_blocked
    i_reserved i_states].
  entailer!.
Qed.