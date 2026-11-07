(* Law table_copy_exact: the body of root_copied against the model's root_copied (LawRoot). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosAcpi.harness.table_copy_exact.code.
Require Import LeanosAcpi.proof.Defs.
Require Import LeanosAcpi.proof.AcpiSpecs.
Require Import LeanosAcpi.proof.LawProg LeanosAcpi.proof.LawDefs LeanosAcpi.proof.LawFacts LeanosAcpi.proof.LawLib
  LeanosAcpi.proof.LawModel LeanosAcpi.proof.LawRoot LeanosAcpi.proof.LawOra LeanosAcpi.proof.LawLib2 LeanosAcpi.proof.LawExp.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

(* The root's envelope check fails. *)
Definition env_bad (x: inputs) (bs: list Z) (len: Z) : bool :=
  (negb (little (sublist 4 8 bs) =? len) || negb (sig_at bs 0 (rc_sig x)))%bool.

Lemma isptr_offset0: forall p, isptr p -> offset_val 0 p = p.
Proof. intros. apply isptr_offset_val_zero; auto. Qed.

(* rw_bools, but never rewriting a constant. *)
Ltac rwb :=
  repeat match goal with
  | E: ?b = true |- context [?b] =>
      lazymatch b with true => fail | false => fail | _ => match type of b with bool => rewrite E end end
  | E: ?b = false |- context [?b] =>
      lazymatch b with true => fail | false => fail | _ => match type of b with bool => rewrite E end end
  end.

Ltac int_norm :=
  repeat match goal with
  | E: context [Int.sub (Int.repr ?a) (Int.repr ?b)] |- _ => rewrite (sub_repr a b) in E
  | E: context [Int.modu (Int.repr ?a) (Int.repr ?b)] |- _ =>
      unfold Int.modu in E; rewrite (Int.unsigned_repr a), (Int.unsigned_repr b) in E by rep_lia
  | E: context [Int.divu (Int.repr ?a) (Int.repr ?b)] |- _ =>
      unfold Int.divu in E; rewrite (Int.unsigned_repr a), (Int.unsigned_repr b) in E by rep_lia
  end.

Lemma divu_repr': forall a b, 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Int.divu (Int.repr a) (Int.repr b) = Int.repr (a / b).
Proof. intros. unfold Int.divu. rewrite !Int.unsigned_repr by auto. reflexivity. Qed.

Lemma modu_repr': forall a b, 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Int.modu (Int.repr a) (Int.repr b) = Int.repr (a mod b).
Proof. intros. unfold Int.modu. rewrite !Int.unsigned_repr by auto. reflexivity. Qed.

Definition Grc : funspecs := [signature_spec; little_spec; byte_sum_spec; stop_spec; begin_table_spec].
Definition Delta_rc : tycontext := func_tycontext f_root_copied nil Grc nil.
Definition Post_rc (q: val) (x: inputs) (pl: place) (re te: val) (s: lst) (m: mem) : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tvoid
       (EX s': lst,
        PROP (J x pl re te (root_copied x (w_length s) (w_cursor s) m) s')
        RETURN ()
        SEP (lfields q x pl re te (m_header m) s';
             data_at Ews (tarray tuchar (root_capacity x)) (bytes_val (m_root m)) re))%argsassert)
    (stackframe_of f_root_copied).

(* root_copied after storing entries_done, width and count: the addresses, then the first table. *)
Definition s_rc_tail : statement := ltac:(
  let b := eval cbv delta [f_root_copied] beta iota zeta in (fn_body f_root_copied) in
  match b with
  | context [Ssequence (Sassign (Efield (Ederef (Etempvar _m ?t1) ?t2) _count tuint) (Etempvar _count tuint)) ?rest] =>
      exact rest
  end).

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

Lemma rc_tail {Espec: OracleKind} q x pl re te s m count:
  rc_pre x pl re te s m (w_length s) (w_cursor s) ->
  validate (w_length s) (m_root m) (Some (rc_sig x)) = S_OK ->
  decode_entries (i_kind x) (w_length s) = inr (count, rc_w x) ->
  0 <= count <= 256 -> rc_w x * count = w_length s - 36 ->
  forall Delta R c, Delta = Delta_rc -> R = Post_rc q x pl re te s m -> c = s_rc_tail ->
  semax Delta
    (PROP ()
     LOCAL (temp _count (Vint (Int.repr count)); temp _width (Vint (Int.repr (rc_w x)));
            temp _n (Vint (Int.repr (w_length s))); temp _r re; temp _m q)
     SEP (lfields q x pl re te (m_header m) (rc_s2 s (w_length s) (w_cursor s) count (rc_w x));
          data_at Ews (tarray tuchar (root_capacity x)) (bytes_val (m_root m)) re))
    c R.
Proof.
  intros P Vok Dinr Cr CW Delta R0 c -> -> ->.
  unfold s_rc_tail, Delta_rc, Post_rc. start_tail.
  pose proof P as (L & F & R & SI & TI & Ln & Cu & LO & I & Pre & Pte & Ptb).
  destruct_lst_ok' L. unfold u32_ok, u64_ok in L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, L13, L14, L15, L16, L17, L18,
      L21, L22, L29.
  pose proof F as (F1 & F2 & F3 & F4 & F5 & F6).
  pose proof TI as (K & Aaddr & T1 & T2 & T3 & T4 & T5).
  unfold len_ok in LO. cbn [capacity_of] in LO.
  assert (Rr: root_capacity x <= Int.max_unsigned) by (destruct I as (_ & _ & _ & I4 & _); auto).
  unfold HEADER_BYTES, MAX_SDT_BYTES in LO.
  pose proof (rc_w_range x) as Wr.
  destruct Cr as [C0 Cr].
  assert (Rc: count * rc_w x <= Int.max_unsigned) by (destruct Wr; nia).
  unfold lfields, rc_s2, rc_s1. lst_cbn. Intros. unfold vi, vl.
  freeze_but [_expect; _verdict; _addresses] [re] FR.
  set (vec := sublist HEADER_BYTES (Zlength (m_root m)) (m_root m)).
    assert (Fvec: Forall byte_ok vec) by (apply Forall_sublist; auto).
    freeze_but [_addresses; _expect; _verdict] [re] FR2.
    forward_for_simple_bound count
      (EX i: Z, PROP (decode_addresses vec (rc_w x) count = decode_from vec (rc_w x) (range_from i count)
                                                                 (entries_pre vec (rc_w x) i);
                      Forall (fun a => 0 < a <= MAX_U32) (entries_pre vec (rc_w x) i))
       LOCAL (temp _r re; temp _n (Vint (Int.repr (w_length s))); temp _width (Vint (Int.repr (rc_w x)));
              temp _count (Vint (Int.repr count)); temp _m q)
       SEP (FRZL FR2; data_at Ews (tarray tuchar (root_capacity x)) (bytes_val (m_root m)) re;
            field_at Ews t_law (DOT _addresses)
              (map (fun v => Vlong (Int64.repr v)) (entries_pre vec (rc_w x) i ++ sublist i MAX_ENTRIES (w_addresses s))) q;
            field_at Ews t_law (DOT _expect) (Vint (Int.repr (w_expect s))) q;
            field_at Ews t_law (DOT _verdict) (Vint (Int.repr (w_verdict s))) q))%assert.
    { entailer!.
      { rewrite decode_start. reflexivity. }
      rewrite entries_pre_0, app_nil_l, (sublist_same 0 MAX_ENTRIES) by auto. apply derives_refl. }
    { (* entry i *)
      assert (Bi: 36 + i * rc_w x + rc_w x <= w_length s) by (destruct Wr; nia).
      forward_call (Ews, offset_val (36 + i * rc_w x) re, re, m_root m, root_capacity x, 36 + i * rc_w x, rc_w x).
      all: try (repeat split; auto; try (destruct Wr; lia); try (rewrite offset_offset_val; f_equal; f_equal; rep_lia)).
      Intros vret. subst vret.
      assert (Ra: 0 <= little (sublist (36 + i * rc_w x) (36 + i * rc_w x + rc_w x) (m_root m)) <= Int64.max_unsigned).
      { apply little_u64; [ apply Forall_sublist; auto | rewrite Zlength_sublist by (destruct Wr; nia); destruct Wr; lia ]. }
      assert (Ea: little (sublist (36 + i * rc_w x) (36 + i * rc_w x + rc_w x) (m_root m)) = entry_at vec (rc_w x) i).
      { unfold vec. rewrite entry_at_root by (unfold HEADER_BYTES; destruct Wr; nia). reflexivity. }
      rewrite Ea in *. unfold vl.
      match goal with E: decode_addresses _ _ _ = _ |- _ => rename E into Dd end.
      rewrite (decode_step vec (rc_w x) i count _ ltac:(lia)) in Dd.
      match goal with E: Forall _ (entries_pre _ _ _) |- _ => rename E into Fp end.
      pose proof (Zlength_entries_pre vec (rc_w x) i ltac:(lia)) as Lp.
      pose proof (Forall_prefix_u64 (entries_pre vec (rc_w x) i) (w_addresses s) i MAX_ENTRIES Lp
                    ltac:(unfold MAX_ENTRIES; lia) L19 Fp L20) as (FA & LA).
      forward_if (temp _t'9 (Vint (Int.repr (Z.b2z ((entry_at vec (rc_w x) i =? 0) ||
                                                      (MAX_U32 <? entry_at vec (rc_w x) i)))))).
      { forward. entailer!. wordp. match goal with E: entry_at _ _ _ = 0 |- _ => rewrite E end. reflexivity. }
      { forward. entailer!. wordp. unfold MAX_U32. change (Int.unsigned (Int.repr (-1))) with 4294967295. bool_fin. }
      forward_if.
      { (* not an address *)
        try b2z_hyp.
        forward_call (q, Vint (Int.repr (w_expect s)), Vint (Int.repr (w_verdict s)), S_ROOT_ENTRY_ADDRESS).
        all: try (unfold u32_ok, S_ROOT_ENTRY_ADDRESS; rep_lia).
        forward.
        set (A := entries_pre vec (rc_w x) i ++ sublist i MAX_ENTRIES (w_addresses s)) in *.
        assert (HJ: J x pl re te (root_copied x (w_length s) (w_cursor s) m)
                      (s_stop (set_addresses (rc_s2 s (w_length s) (w_cursor s) count (rc_w x)) A) S_ROOT_ENTRY_ADDRESS)).
        { apply (rc_ret3 x pl re te s m (w_length s) (w_cursor s) count (rc_w x) S_ROOT_ENTRY_ADDRESS A P Vok Dinr);
            auto; [ | unfold S_ROOT_ENTRY_ADDRESS, VERDICT_TABLES; lia ].
          fold vec. rewrite Dd. rwb. reflexivity. }
        Exists (s_stop (set_addresses (rc_s2 s (w_length s) (w_cursor s) count (rc_w x)) A) S_ROOT_ENTRY_ADDRESS).
        thaw FR2. thaw FR. unfold lfields, s_stop, rc_s2, rc_s1. lst_cbn. unfold vi, vl. entailer!. }
      try b2z_hyp.
      forward_for_simple_bound i
        (EX j: Z, PROP (forall j', 0 <= j' < j -> Znth j' (entries_pre vec (rc_w x) i) <> entry_at vec (rc_w x) i)
         LOCAL (temp _a (Vlong (Int64.repr (entry_at vec (rc_w x) i))); temp _i (Vint (Int.repr i));
                temp _r re; temp _n (Vint (Int.repr (w_length s))); temp _width (Vint (Int.repr (rc_w x)));
                temp _count (Vint (Int.repr count)); temp _m q)
         SEP (FRZL FR2; data_at Ews (tarray tuchar (root_capacity x)) (bytes_val (m_root m)) re;
              field_at Ews t_law (DOT _addresses)
                (map (fun v => Vlong (Int64.repr v)) (entries_pre vec (rc_w x) i ++ sublist i MAX_ENTRIES (w_addresses s))) q;
              field_at Ews t_law (DOT _expect) (Vint (Int.repr (w_expect s))) q;
              field_at Ews t_law (DOT _verdict) (Vint (Int.repr (w_verdict s))) q))%assert.
      { entailer!. all: (intros; lia). }
      { (* j *)
        cbv beta. Intros.
        match goal with H: 0 <= ?k < i |- _ => rename k into j end.
        assert (Jr: 0 <= j < Zlength (entries_pre vec (rc_w x) i ++ sublist i MAX_ENTRIES (w_addresses s)))
          by (rewrite LA; unfold MAX_ENTRIES; lia).
        forward.
        try (rewrite Znth_map by lia). try (rewrite Znth_app1 by lia).
        assert (Rj: 0 <= Znth j (entries_pre vec (rc_w x) i) <= Int64.max_unsigned)
          by (apply (Forall_Znth' _ _ j (proj1 (proj1 (Forall_app _ _ _) FA))); lia).
        forward_if.
        { (* a duplicate *)
          forward_call (q, Vint (Int.repr (w_expect s)), Vint (Int.repr (w_verdict s)), S_ROOT_ENTRY_DUPLICATE).
          all: try (unfold u32_ok, S_ROOT_ENTRY_DUPLICATE; rep_lia).
          forward. wordp.
          set (A := entries_pre vec (rc_w x) i ++ sublist i MAX_ENTRIES (w_addresses s)) in *.
          assert (HJ: J x pl re te (root_copied x (w_length s) (w_cursor s) m)
                        (s_stop (set_addresses (rc_s2 s (w_length s) (w_cursor s) count (rc_w x)) A)
                           S_ROOT_ENTRY_DUPLICATE)).
          { apply (rc_ret3 x pl re te s m (w_length s) (w_cursor s) count (rc_w x) S_ROOT_ENTRY_DUPLICATE A P Vok Dinr);
              auto; [ | unfold S_ROOT_ENTRY_DUPLICATE, VERDICT_TABLES; lia ].
            fold vec. rewrite Dd. rwb.
            rewrite (existsb_true (entry_at vec (rc_w x) i) (entries_pre vec (rc_w x) i) j) by (auto; lia).
            reflexivity. }
          Exists (s_stop (set_addresses (rc_s2 s (w_length s) (w_cursor s) count (rc_w x)) A) S_ROOT_ENTRY_DUPLICATE).
          thaw FR2. thaw FR. unfold lfields, s_stop, rc_s2, rc_s1. lst_cbn. unfold vi, vl. entailer!. }
        forward. entailer!. wordp. intros j' J'. destruct (Z.eq_dec j' j); [ subst; auto | ].
        match goal with E: forall _, _ -> _ |- _ => apply E; lia end. }
      Intros.
      match goal with H: forall j', 0 <= j' < i -> _ |- _ => rename H into ND end.
      forward.
      assert (NE: existsb (Z.eqb (entry_at vec (rc_w x) i)) (entries_pre vec (rc_w x) i) = false).
      { apply existsb_false. intros j' J'. rewrite Lp in J'. auto. }
      rewrite (upd_Znth_map (fun v => Vlong (Int64.repr v))).
      rewrite (upd_prefix _ _ i _ MAX_ENTRIES) by (auto; unfold MAX_ENTRIES; lia).
      rewrite <- (entries_pre_succ vec (rc_w x) i) by lia.
      entailer!.
      match goal with E: ((entry_at _ _ _ =? 0) || _)%bool = false |- _ => rename E into Hb end.
      rewrite Hb, NE in Dd. cbv iota in Dd.
      split.
      - rewrite entries_pre_succ by lia. exact Dd.
      - rewrite entries_pre_succ by lia. apply Forall_app; split; auto.
        apply orb_false_iff in Hb as [H3a H3b]. apply Z.eqb_neq in H3a. apply Z.ltb_ge in H3b.
        assert (0 <= entry_at vec (rc_w x) i) by lia.
        constructor; [ lia | constructor ]. }
    (* every entry decoded *)
    Intros.
    match goal with E: decode_addresses _ _ _ = _ |- _ => rename E into Dd end. rewrite decode_end in Dd.
    match goal with E: Forall _ (entries_pre _ _ _) |- _ => rename E into Fp end.
    pose proof (Zlength_entries_pre vec (rc_w x) count C0) as Lp.
    pose proof (Forall_prefix_u64 (entries_pre vec (rc_w x) count) (w_addresses s) count MAX_ENTRIES Lp
                  ltac:(unfold MAX_ENTRIES; lia) L19 Fp L20) as (FA & LA).
    forward_if.
    { (* no entry *)
      forward_call (q, Vint (Int.repr (w_expect s)), Vint (Int.repr (w_verdict s)), S_SEQUENCE).
      all: try (unfold u32_ok, S_SEQUENCE; rep_lia).
      forward. wordp. try subst count.
      set (A := entries_pre vec (rc_w x) 0 ++ sublist 0 MAX_ENTRIES (w_addresses s)) in *.
      assert (HJ: J x pl re te (root_copied x (w_length s) (w_cursor s) m)
                    (s_stop (set_addresses (rc_s2 s (w_length s) (w_cursor s) 0 (rc_w x)) A) S_SEQUENCE)).
      { apply (rc_seq x pl re te s m (w_length s) (w_cursor s) (rc_w x) A P Vok Dinr); auto. }
      Exists (s_stop (set_addresses (rc_s2 s (w_length s) (w_cursor s) 0 (rc_w x)) A) S_SEQUENCE).
      thaw FR2. thaw FR. unfold lfields, s_stop, rc_s2, rc_s1. lst_cbn. unfold vi, vl. entailer!. }
    wordp.
    thaw FR2. thaw FR.
    set (A := entries_pre vec (rc_w x) count ++ sublist count MAX_ENTRIES (w_addresses s)) in *.
    assert (Rcap: table_capacity x <= Int.max_unsigned) by (destruct I as (_ & _ & _ & _ & I5 & _); auto).
    forward_call (q, 0, w_arena s, table_capacity x, p_tables pl, te, A, w_offsets s,
                  Vint (Int.repr (w_is_root s)), Vint (Int.repr (w_table s)), Vlong (Int64.repr (w_sdt_address s)),
                  w_dest s, w_dexp s, Vint (Int.repr (w_capacity s)), Vlong (Int64.repr (w_cursor s)),
                  Vlong (Int64.repr (w_byte s)), Vint (Int.repr (w_word s)), Vint (Int.repr (w_expect s)),
                  Vint (Int.repr (w_verdict s))).
    all: try (unfold u32_ok, MAX_ENTRIES in *; repeat split; auto; rep_lia).
    assert (HJ: J x pl re te (root_copied x (w_length s) (w_cursor s) m)
                  (bt_state x pl te (set_addresses (rc_s2 s (w_length s) (w_cursor s) count (rc_w x)) A) 0)).
    { apply (rc_tables x pl re te s m (w_length s) (w_cursor s) count (rc_w x) (entries_pre vec (rc_w x) count)
               P Vok Dinr Dd); lia. }
    Exists (bt_state x pl te (set_addresses (rc_s2 s (w_length s) (w_cursor s) count (rc_w x)) A) 0).
    unfold bt_state in *.
    destruct (table_capacity x <=? w_arena (set_addresses (rc_s2 s (w_length s) (w_cursor s) count (rc_w x)) A)) eqn:Eb.
    + assert (Eb': (table_capacity x <=? w_arena s) = true) by exact Eb. rewrite Eb'.
      unfold lfields, s_stop, rc_s2, rc_s1. lst_cbn. unfold vi, vl. entailer!.
    + assert (Eb': (table_capacity x <=? w_arena s) = false) by exact Eb. rewrite Eb'.
      unfold lfields, rc_s2, rc_s1. lst_cbn. unfold vi, vl. entailer!.
Qed.

Lemma body_root_copied : semax_body nil [signature_spec; little_spec; byte_sum_spec; stop_spec; begin_table_spec]
  f_root_copied root_copied_spec.
Proof.
  start_function.
  rename H into P.
  pose proof P as (L & F & R & SI & TI & Ln & Cu & LO & I & Pre & Pte & Ptb).
  subst len cursor.
  destruct_lst_ok' L. unfold u32_ok, u64_ok in L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, L13, L14, L15, L16, L17, L18,
      L21, L22, L29.
  pose proof F as (F1 & F2 & F3 & F4 & F5 & F6).
  pose proof TI as (K & Aaddr & T1 & T2 & T3 & T4 & T5).
  unfold len_ok in LO. cbn [capacity_of] in LO.
  assert (Rr: root_capacity x <= Int.max_unsigned) by (destruct I as (_ & _ & _ & I4 & _); auto).
  unfold HEADER_BYTES, MAX_SDT_BYTES in LO.
  unfold lfields. Intros. unfold vi, vl.
  freeze_but [_root_expect; _length; _root_done; _root_length; _cursor; _root_cursor; _kind; _expect; _verdict;
              _entries_done; _width; _count; _addresses] [re] FR.
  assert (Zs: Zlength (rc_sig x) = 4) by (unfold rc_sig; destruct (i_kind x =? 1); reflexivity).
  assert (Vc: forall st, validate (w_length s) (m_root m) (Some (rc_sig x)) = st ->
                J x pl re te (root_copied x (w_length s) (w_cursor s) m) (s_stop (rc_s1 s (w_length s) (w_cursor s)) st) \/
                st = S_OK).
  { intros st V. destruct (Z.eq_dec st S_OK) as [E | N]; [ right; auto | left ].
    apply (rc_ret1 x pl re te s m (w_length s) (w_cursor s) st P V N).
    subst st. rewrite validate_c in * by (unfold HEADER_BYTES; lia).
    repeat match goal with |- context [if ?b then _ else _] => destruct b end;
      unfold S_SDT_ENVELOPE, S_SDT_CHECKSUM, S_OK, VERDICT_TABLES in *; lia. }
  forward. forward. forward. forward. forward. forward. forward.
  forward_if (temp _t'1 (Vint (Int.repr (if sig_at (m_root m) 0 (rc_sig x) then 1 else 0)))).
  - forward_call (Ews, re, re, m_root m, root_capacity x, 0, 82, 83, 68, 84).
    { unfold byte_ok; repeat split; rep_lia. }
    forward. entailer!. wordp. unfold rc_sig, RSDT. rewrite (proj2 (Z.eqb_eq _ _) H).
    destruct (sig_at (m_root m) 0 [82; 83; 68; 84]); reflexivity.
  - forward_call (Ews, re, re, m_root m, root_capacity x, 0, 88, 83, 68, 84).
    { unfold byte_ok; repeat split; rep_lia. }
    forward. entailer!. wordp. unfold rc_sig, XSDT. rewrite (proj2 (Z.eqb_neq _ _) H).
    destruct (sig_at (m_root m) 0 [88; 83; 68; 84]); reflexivity.
  - forward.
    forward_call (Ews, offset_val 4 re, re, m_root m, root_capacity x, 4, 4).
    all: try (repeat split; auto; rep_lia).
    assert (Ll: 0 <= little (sublist 4 8 (m_root m)) <= Int64.max_unsigned).
    { apply little_u64; [ apply Forall_sublist; auto | rewrite Zlength_sublist by lia; lia ]. }
    forward_if (temp _t'5 (Vint (Int.repr (Z.b2z (env_bad x (m_root m) (w_length s)))))).
    { forward. entailer!. wordp. unfold env_bad. change (4 + 4) with 8.
      destruct (Z.eqb_spec (little (sublist 4 8 (m_root m))) (w_length s)); [ congruence | reflexivity ]. }
    { forward. entailer!. wordp. unfold env_bad. change (4 + 4) with 8.
      destruct (Z.eqb_spec (little (sublist 4 8 (m_root m))) (w_length s)); [ | congruence ]. simpl.
      destruct (sig_at (m_root m) 0 (rc_sig x)); reflexivity. }
    forward_if.
    { (* the envelope *)
      try b2z_hyp.
      forward_call (q, Vint (Int.repr (w_expect s)), Vint (Int.repr (w_verdict s)), S_SDT_ENVELOPE).
      all: try (unfold u32_ok, S_SDT_ENVELOPE; rep_lia).
      forward.
      assert (HJ: J x pl re te (root_copied x (w_length s) (w_cursor s) m)
                    (s_stop (rc_s1 s (w_length s) (w_cursor s)) S_SDT_ENVELOPE)).
      { destruct (Vc S_SDT_ENVELOPE) as [HJ | HJ]; [ | auto | discriminate ].
        rewrite validate_c by (unfold HEADER_BYTES; lia).
        match goal with E: env_bad _ _ _ = true |- _ => unfold env_bad in E; change (4 + 4) with 8; rewrite E end.
        reflexivity. }
      Exists (s_stop (rc_s1 s (w_length s) (w_cursor s)) S_SDT_ENVELOPE).
      thaw FR. unfold lfields, s_stop, rc_s1. lst_cbn. unfold vi, vl. entailer!. }
    try b2z_hyp.
    match goal with E: env_bad _ _ _ = false |- _ => rename E into Eenv end.
    forward_call (Ews, re, re, m_root m, root_capacity x, 0, w_length s).
    all: try (repeat split; auto; rep_lia).
    replace (0 + w_length s) with (w_length s) by lia.
    assert (Rs: 0 <= fold_left Z.add (sublist 0 (w_length s) (m_root m)) 0 <= 255 * w_length s).
    { pose proof (sum_bound (sublist 0 (w_length s) (m_root m)) ltac:(apply Forall_sublist; auto)) as SB.
      rewrite Zlength_sublist in SB by lia. lia. }
    remember (fold_left Z.add (sublist 0 (w_length s) (m_root m)) 0) as sum eqn:Esum.
    pose proof (Z.mod_pos_bound sum 256 ltac:(lia)) as Rm.
    forward_if.
    { (* the checksum *)
      forward_call (q, Vint (Int.repr (w_expect s)), Vint (Int.repr (w_verdict s)), S_SDT_CHECKSUM).
      all: try (unfold u32_ok, S_SDT_CHECKSUM; rep_lia).
      forward.
      assert (HJ: J x pl re te (root_copied x (w_length s) (w_cursor s) m)
                    (s_stop (rc_s1 s (w_length s) (w_cursor s)) S_SDT_CHECKSUM)).
      { destruct (Vc S_SDT_CHECKSUM) as [HJ | HJ]; [ | auto | discriminate ].
        rewrite validate_c by (unfold HEADER_BYTES; lia).
        unfold env_bad in Eenv. rewrite Eenv. try rewrite <- Esum.
        try (match goal with E: context [Int.modu (Int.repr ?a) (Int.repr 256)] |- _ =>
               unfold Int.modu in E; rewrite (Int.unsigned_repr a), (Int.unsigned_repr 256) in E by rep_lia end).
        wordp.
        match goal with |- context [?t mod 256 =? 0] => destruct (Z.eqb_spec (t mod 256) 0) end;
          [ exfalso; auto | reflexivity ]. }
      Exists (s_stop (rc_s1 s (w_length s) (w_cursor s)) S_SDT_CHECKSUM).
      thaw FR. unfold lfields, s_stop, rc_s1. lst_cbn. unfold vi, vl. entailer!. }
    try (match goal with E: context [Int.modu (Int.repr ?a) (Int.repr 256)] |- _ =>
           unfold Int.modu in E; rewrite (Int.unsigned_repr a), (Int.unsigned_repr 256) in E by rep_lia end).
    wordp.
    assert (Vok: validate (w_length s) (m_root m) (Some (rc_sig x)) = S_OK).
    { rewrite validate_c by (unfold HEADER_BYTES; lia). unfold env_bad in Eenv. rewrite Eenv. try rewrite <- Esum.
      match goal with |- context [?t mod 256 =? 0] => destruct (Z.eqb_spec (t mod 256) 0) end;
        [ reflexivity | contradiction ]. }
    forward.
    forward_if (temp _t'7 (Vint (Int.repr (rc_w x)))).
    { forward. entailer!. wordp. unfold rc_w.
      match goal with E: i_kind x = 1 |- _ => rewrite E end. reflexivity. }
    { forward. entailer!. wordp. unfold rc_w.
      match goal with E: i_kind x <> 1 |- _ => rewrite (proj2 (Z.eqb_neq _ _) E) end. reflexivity. }
    forward.
    pose proof (rc_w_range x) as Wr.
    assert (Dc := decode_entries_c x (w_length s) K ltac:(unfold HEADER_BYTES; lia)).
    pose proof (Z.mod_pos_bound (w_length s - 36) (rc_w x) ltac:(destruct Wr; lia)) as Wm.
    forward_if.
    { apply prop_right. intro E.
      change Int.zero with (Int.repr 0) in E; apply repr_inj_unsigned in E; destruct Wr; rep_lia. }
    { (* the width *)
      forward_call (q, Vint (Int.repr (w_expect s)), Vint (Int.repr (w_verdict s)), S_ROOT_WIDTH).
      all: try (unfold u32_ok, S_ROOT_WIDTH; rep_lia).
      forward.
      int_norm. wordp.
      assert (HJ: J x pl re te (root_copied x (w_length s) (w_cursor s) m)
                    (s_stop (rc_s1 s (w_length s) (w_cursor s)) S_ROOT_WIDTH)).
      { apply (rc_ret2 x pl re te s m (w_length s) (w_cursor s) S_ROOT_WIDTH P Vok);
          [ | unfold S_ROOT_WIDTH, VERDICT_TABLES; lia ].
        rewrite Dc. unfold HEADER_BYTES.
        match goal with E: (w_length s - 36) mod rc_w x <> 0 |- _ => rewrite (proj2 (Z.eqb_neq _ _) E) end.
        reflexivity. }
      Exists (s_stop (rc_s1 s (w_length s) (w_cursor s)) S_ROOT_WIDTH).
      thaw FR. unfold lfields, s_stop, rc_s1. lst_cbn. unfold vi, vl. entailer!. }
    int_norm. wordp.
    forward.
    { entailer!. match goal with E: Int.repr (rc_w x) = Int.zero |- _ =>
        change Int.zero with (Int.repr 0) in E; apply repr_inj_unsigned in E; destruct Wr; rep_lia end. }
    unfold HEADER_BYTES in Dc.
    rewrite sub_repr, divu_repr' by (destruct Wr; rep_lia).
    assert (CW: rc_w x * ((w_length s - 36) / rc_w x) = w_length s - 36).
    { pose proof (Z_div_mod_eq_full (w_length s - 36) (rc_w x)). lia. }
    set (count := (w_length s - 36) / rc_w x) in *.
    assert (C0: 0 <= count) by (unfold count; apply Z.div_pos; destruct Wr; lia).
    clearbody count.
    rewrite (proj2 (Z.eqb_eq _ _) H0) in Dc. cbn [negb] in Dc. cbv iota in Dc.
    assert (Rc: count * rc_w x <= Int.max_unsigned) by (destruct Wr; nia).
    forward_if.
    { (* too many entries *)
      forward_call (q, Vint (Int.repr (w_expect s)), Vint (Int.repr (w_verdict s)), S_ROOT_ENTRIES).
      all: try (unfold u32_ok, S_ROOT_ENTRIES; rep_lia).
      forward.
      wordp.
      assert (HJ: J x pl re te (root_copied x (w_length s) (w_cursor s) m)
                    (s_stop (rc_s1 s (w_length s) (w_cursor s)) S_ROOT_ENTRIES)).
      { apply (rc_ret2 x pl re te s m (w_length s) (w_cursor s) S_ROOT_ENTRIES P Vok);
          [ | unfold S_ROOT_ENTRIES, VERDICT_TABLES; lia ].
        rewrite Dc. unfold MAX_ENTRIES. rewrite (proj2 (Z.ltb_lt _ _)) by (destruct Wr; nia). reflexivity. }
      Exists (s_stop (rc_s1 s (w_length s) (w_cursor s)) S_ROOT_ENTRIES).
      thaw FR. unfold lfields, s_stop, rc_s1. lst_cbn. unfold vi, vl. entailer!. }
    wordp.
    assert (Dinr: decode_entries (i_kind x) (w_length s) = inr (count, rc_w x)).
    { rewrite Dc. unfold MAX_ENTRIES. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
    forward. forward. forward.
    eapply semax_pre;
      [ | apply (rc_tail q x pl re te s m count P Vok Dinr ltac:(lia) ltac:(lia)); reflexivity ].
    thaw FR. unfold lfields, rc_s2, rc_s1. lst_cbn. unfold vi, vl. entailer!.
Qed.
