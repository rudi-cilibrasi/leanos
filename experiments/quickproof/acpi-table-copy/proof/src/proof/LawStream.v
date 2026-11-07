(* Law table_copy_exact: the body of the harness's copy stream export against stream_spec Ora_law: its checks
   follow from the call the model expects (stream_call), and the answer it records keeps J (LawModel), through
   root_copied and table_copied at the end of an SDT's stream. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosAcpi.harness.table_copy_exact.code.
Require Import LeanosAcpi.proof.Defs.
Require Import LeanosAcpi.proof.AcpiSpecs.
Require Import LeanosAcpi.proof.LawProg LeanosAcpi.proof.LawDefs LeanosAcpi.proof.LawFacts LeanosAcpi.proof.LawLib
  LeanosAcpi.proof.LawModel LeanosAcpi.proof.LawOra LeanosAcpi.proof.LawLib2 LeanosAcpi.proof.LawExp
  LeanosAcpi.proof.LawExp2.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

Definition Gstream : funspecs :=
  [gp_assert_spec; any_u64_spec; little_spec; transition_spec; stop_spec; root_copied_spec; table_copied_spec].

Ltac to_lfields q x pl re te hx s' extra :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx _))) _ _ =>
    apply semax_pre with (PROPx P (LOCALx Q (SEPx (lfields q x pl re te hx s' :: extra)))) end.

Lemma body_stream : semax_body Vlaw Gstream f_leanos_boot_machine_acpi_copy_stream_step_query
  (stream_spec Ora_law).
Proof.
  start_function.
  rename H into Nc.
  unfold Ora_law. Intros p s re te.
  match goal with H: run _ _ _ = Some _ |- _ => rename H into Hrun end.
  match goal with H: J _ _ _ _ _ _ |- _ => rename H into HJ end.
  match goal with H: inputs_ok _ |- _ => rename H into Ix end.
  try subst ctx.
  destruct (next_call_J _ _ _ _ _ _ _ _ Hrun HJ Nc) as (st & m & -> & Ec & G & L & F & R).
  destruct (stream_call x st _ _ _ _ _ _ _ _ _ Ec)
    as (g & len & bs & cursor & byte & cur & -> & -> & -> & -> & -> & -> & -> & -> & -> & ->).
  cbn [mem_of] in *.
  pose proof G as (SI & TI & CI).
  pose proof CI as (C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9).
  pose proof SI as (S1 & S2 & S3 & S4 & S5).
  subst len cursor byte bs.
  destruct_lst_ok' L. unfold u32_ok, u64_ok in L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, L13, L14, L15, L16, L17, L18,
      L21, L22, L29.
  pose proof F as (F1 & F2 & F3 & F4 & F5 & F6).
  unfold len_ok, HEADER_BYTES, MAX_SDT_BYTES in C9. destruct C9 as ((C9a & C9b) & C9c).
  assert (O: 0 <= cursor_of g) by (destruct g; simpl; [ lia | unfold tgt_inv, tab_inv in TI; lia ]).
  assert (LB: Zlength (base_mem m g) = base_cap x g) by (apply base_cap_fit; auto).
  assert (Fit: cursor_of g + w_length s <= base_cap x g) by (rewrite capacity_base in C9c; lia).
  pose proof (chunk_bytes_range (w_length s) (w_byte s) C7) as (N1 & N2).
  set (n := chunk_bytes (w_length s) (w_byte s)) in *.
  sep_apply (arrays_to_base x m re te g).
  unfold lfields. Intros.
  freeze_but [_expect; _byte; _length; _word; _destination_expect; _cursor; _sdt_address; _answer; _verdict; _is_root]
    [base_exp re te g] FR.
  unfold vi, vl. rewrite <- S2, <- C4.
  forward.
  forward.
  forward_if (temp _t'1 (Vint (Int.repr 1))).
  { forward. forward. forward. entailer!. bool_fin. }
  { exfalso. wordp. unfold E_STREAM in C0. lia. }
  forward_call Int.one.
  assert (Lc: 0 <= w_word s < 5) by lia.
  forward.
  forward_if (temp _t'2 (Vint (Int.repr (stream_word (w_word s))))).
  { forward. forward. entailer!. unfold stream_word. wordp. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
  { forward. forward. entailer!. unfold stream_word. wordp. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
  assert (Rsw: 0 <= stream_word (w_word s) <= 6) by (unfold stream_word; destruct (_ <? 2); lia).
  forward_call Int.one.
  all: try (entailer!; simpl; rewrite ?Int.unsigned_repr by rep_lia; rewrite Int64.eq_true; reflexivity).
  forward. forward.
  forward_if (temp _t'3 (Vlong (Int64.repr (w_byte s + n)))).
  { forward. forward. entailer!. wordp. unfold n, chunk_bytes. f_equal. f_equal. lia. }
  { forward. forward. entailer!. wordp. unfold n, chunk_bytes. f_equal. f_equal. lia. }
  forward.
  forward. forward.
  assert (Tm: terminal (w_length s) (w_byte s) = (if w_byte s + n =? w_length s then 1 else 0)) by reflexivity.
  assert (Pd: isptr (w_dexp s)) by (rewrite S4; apply dexp_isptr; auto).
  forward. forward. forward.
  forward_call (Ews, offset_val (cursor_of g + w_byte s) (base_exp re te g), base_exp re te g, base_mem m g,
                base_cap x g, cursor_of g + w_byte s, n).
  { entailer!. rewrite S4 in *. pose proof (dexp_byte re te g (w_byte s) Pre) as DB.
    destruct (dexp_of re te g) eqn:Ed; try contradiction. simpl. rewrite <- DB. unfold vi. simpl.
    rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia. repeat f_equal; lia. }
  all: try (repeat split; auto; try lia; try (rewrite LB; lia); try solve [ destruct g; simpl; auto ]).
  rewrite <- (chunk_in_base m g (w_length s) (w_byte s) n) by (try rewrite LB; lia).
  assert (Elast: Int.signed (Int.repr (Z.b2z (zeq (w_byte s + n) (Int.unsigned (Int.repr (w_length s)))))) =
                 terminal (w_length s) (w_byte s)).
  { rewrite Int.unsigned_repr by rep_lia. unfold terminal. fold n.
    destruct (zeq (w_byte s + n) (w_length s)); destruct (Z.eqb_spec (w_byte s + n) (w_length s)); try lia; reflexivity. }
  rewrite Elast.
  set (chunk := little (sublist (w_byte s) (w_byte s + n) (region m (dest_of g) (w_length s)))) in *.
  assert (Rch: 0 <= chunk <= Int64.max_unsigned).
  { apply little_u64. rewrite region_base. apply Forall_sublist, Forall_sublist. destruct g; simpl; auto.
    rewrite Zlength_sublist; [ lia | lia | ]. rewrite region_base, Zlength_sublist; lia. }
  assert (Rtm: 0 <= terminal (w_length s) (w_byte s) <= 1) by (unfold terminal; destruct (_ =? _); lia).
  forward.
  forward.
  forward_if (temp _t'5 (Vint (Int.repr 1))).
  { repeat forward. all: (entailer!; bool_fin). }
  { exfalso. wordp. lia. }
  forward_if (temp _t'6 (Vint (Int.repr 1))).
  { repeat forward. all: (entailer!; bool_fin). }
  { exfalso. wordp. lia. }
  forward_call Int.one.
  forward.
  forward_if (temp _t'7 (Vint (Int.repr 1))).
  { repeat forward. all: (entailer!; bool_fin). }
  { exfalso. wordp. lia. }
  forward_if (temp _t'8 (Vint (Int.repr 1))).
  { repeat forward. all: (entailer!; bool_fin). }
  { exfalso. wordp. lia. }
  forward_call Int.one.
  forward_if (temp _t'9 (Vint (Int.repr 1))).
  { repeat forward. all: (entailer!; bool_fin). }
  { exfalso. wordp. lia. }
  forward_call Int.one.
  forward_call tt. Intros v.
  forward. forward.
  unfold vl. rewrite (upd_Znth_map (fun v => Vlong (Int64.repr v))).
  forward.
  assert (Rv: u64_ok v) by auto.
  pose proof (run_snoc x h _ m _ (Word v) Hrun Ec (fits_word_stream _ _ _ _ _ _ _ _ _ v)) as Hr'.
  pose proof (chunk_step_bytes x g (w_length s) (region m (dest_of g) (w_length s)) (w_cursor s) (w_byte s) cur m
                (Word v)) as (B1 & B2 & B3).
  destruct (Z_lt_ge_dec (Zlength cur) 4) as [Lt | Ge].
  - (* a word before the last *)
    forward_if (PROP (False) LOCAL () SEP ()).
    { forward. forward. forward.
      pose proof (J_stream_more x pl re te g _ _ _ _ cur m s v HJ Lt Rv) as HJ'.
      Exists v. unfold Ora_law.
      Exists (step x (Copying g (CChunk (w_length s) (region m (dest_of g) (w_length s)) (w_cursor s) (w_byte s) cur))
                m (Word v))
        (set_word (set_answer s (upd_Znth (Zlength cur) (w_answer s) v)) (Zlength cur + 1)) re te.
      rewrite B1, B2, B3. thaw FR. sep_apply (arrays_unbase x m re te g).
      unfold lfields. lst_cbn. unfold vi, vl. rewrite ?C4. entailer!. }
    { exfalso. wordp. lia. }
  - (* the last word *)
    assert (Lw4: Zlength cur = 4) by lia.
    match goal with |- semax _ ?Pre _ _ => forward_if Pre end.
    { exfalso. wordp. lia. }
    { forward. entailer!. }
    rewrite C4, (answers_full cur s v L Lw4 C5).
    assert (Fc: Forall u64_ok cur) by (rewrite <- C5; apply Forall_sublist; auto).
    assert (Fa: Forall u64_ok (cur ++ [v])) by (apply Forall_app; split; auto).
    assert (La: Zlength (cur ++ [v]) = 5) by list_solve.
    forward_call (gv _law, cur ++ [v], w_cursor s, chunk, w_byte s + n, terminal (w_length s) (w_byte s)).
    all: try (unfold u64_ok in *; repeat split; auto; rep_lia).
    rewrite law_transition_eq.
    set (t := transition (cur ++ [v]) chunk (w_cursor s) (w_byte s) n (terminal (w_length s) (w_byte s))) in *.
    assert (Rt: 0 <= t < VERDICT_TABLES) by apply transition_u32.
    forward_if.
    + (* rejected *)
      assert (Tn: t <> S_OK) by (unfold S_OK; intro E; rewrite E in *; contradiction).
      forward_call (gv _law, Vint (Int.repr (w_expect s)), Vint (Int.repr (w_verdict s)), t).
      all: try (unfold u32_ok, VERDICT_TABLES in *; rep_lia).
      assert (HJ': J x pl re te (step x (Copying g (CChunk (w_length s) (region m (dest_of g) (w_length s))
                                                       (w_cursor s) (w_byte s) cur)) m (Word v))
                     (s_stop (set_answer s (cur ++ [v])) t)) by (apply J_stream_reject; auto).
      forward. Exists v.
      unfold Ora_law.
      Exists (step x (Copying g (CChunk (w_length s) (region m (dest_of g) (w_length s)) (w_cursor s) (w_byte s) cur))
                m (Word v)) (s_stop (set_answer s (cur ++ [v])) t) re te.
      rewrite B1, B2, B3. thaw FR. sep_apply (arrays_unbase x m re te g).
      unfold lfields, s_stop. lst_cbn. unfold vi, vl. rewrite ?C4. entailer!.
    + (* accepted *)
      assert (T0: t = S_OK).
      { unfold S_OK. match goal with H: Int.repr t = Int.repr 0 |- _ => apply repr_inj_unsigned in H end; auto.
        all: unfold VERDICT_TABLES in Rt; rep_lia. }
      destruct (transition_ok _ _ _ _ _ _ T0) as (T2 & T3 & T4).
      forward. forward. forward. forward. forward.
      thaw FR. sep_apply (arrays_unbase x m re te g). Intros.
      match type of Hr' with context [h ++ [(?c, Word v)]] =>
        forward_if (PROP () LOCAL (temp _v (Vlong (Int64.repr v))) SEP (Ora_law gv (gv _law) pl x (h ++ [(c, Word v)])))
      end.
      * (* the last chunk *)
        assert (Tm1: terminal (w_length s) (w_byte s) <> 0) by assumption.
        destruct (stream_last x pl re te g (w_length s) (region m (dest_of g) (w_length s)) (w_cursor s) (w_byte s)
                    cur m s v HJ Lw4 Rv T0 Tm1) as (Est & Lok & Mf & Mr & Si & Ti & Wl & Wc & Lo & Z2).
        rewrite Est in Hr'.
        forward.
        destruct g as [ | l ]; cbn [sdt_copied] in Hr'.
        -- (* the root *)
           forward_if.
           2: { exfalso. match goal with H: Int.repr (w_is_root s) = Int.zero |- _ => rewrite S1 in H; inversion H end. }
           to_lfields (gv _law) x pl re te (m_header m) (s_accept s (cur ++ [v]))
             [data_at Ews (tarray tuchar (root_capacity x)) (bytes_val (m_root m)) re;
              data_at Ews (tarray tuchar (table_capacity x)) (bytes_val (m_tables m)) te].
           { unfold lfields, s_accept. lst_cbn. unfold vi, vl. entailer!. }
           forward_call (gv _law, x, pl, re, te, s_accept s (cur ++ [v]), m, w_length s, Znth 3 (cur ++ [v])).
           all: try (unfold rc_pre; exact (conj Lok (conj Mf (conj Mr (conj Si (conj Ti (conj Wl (conj Wc (conj Lo (conj Ix (conj Pre (conj Pte H5)))))))))))).
           Intros s'.
           destruct (root_copied_bytes x (w_length s) (Znth 3 (cur ++ [v])) m) as (RB1 & RB2 & RB3).
           unfold Ora_law. Exists (root_copied x (w_length s) (Znth 3 (cur ++ [v])) m) s' re te.
           rewrite RB1, RB2, RB3. entailer!.
        -- (* table l_entry l *)
           forward_if.
           { exfalso. match goal with H: Int.repr (w_is_root s) <> Int.zero |- _ => rewrite S1 in H; contradiction end. }
           to_lfields (gv _law) x pl re te (m_header m) (s_accept s (cur ++ [v]))
             [data_at Ews (tarray tuchar (root_capacity x)) (bytes_val (m_root m)) re;
              data_at Ews (tarray tuchar (table_capacity x)) (bytes_val (m_tables m)) te].
           { unfold lfields, s_accept. lst_cbn. unfold vi, vl. entailer!. }
           forward_call (gv _law, x, pl, re, te, m_header m, l, s_accept s (cur ++ [v]), m, w_length s,
                         Znth 3 (cur ++ [v])).
           all: try (unfold tc_pre; exact (conj Lok (conj Mf (conj Mr (conj Si (conj Ti (conj Wl (conj Wc (conj Lo Ix))))))))).
           Intros s'.
           destruct (table_copied_bytes x l (w_length s) (Znth 3 (cur ++ [v])) m) as (RB1 & RB2 & RB3).
           unfold Ora_law. Exists (table_copied x l (w_length s) (Znth 3 (cur ++ [v])) m) s' re te.
           rewrite RB1, RB2, RB3. entailer!.
      * (* the next chunk *)
        assert (Tm0: terminal (w_length s) (w_byte s) = 0).
        { match goal with H: Int64.repr (terminal _ _) = Int64.zero |- _ =>
            apply (f_equal Int64.unsigned) in H; rewrite Int64.unsigned_repr, Int64.unsigned_zero in H by rep_lia;
            exact H end. }
        assert (HJ': J x pl re te (step x (Copying g (CChunk (w_length s) (region m (dest_of g) (w_length s))
                                                         (w_cursor s) (w_byte s) cur)) m (Word v))
                       (s_accept s (cur ++ [v]))) by (apply J_stream_next; auto).
        forward.
        unfold Ora_law.
        Exists (step x (Copying g (CChunk (w_length s) (region m (dest_of g) (w_length s)) (w_cursor s) (w_byte s) cur))
                  m (Word v)) (s_accept s (cur ++ [v])) re te.
        rewrite B1, B2, B3. unfold lfields, s_accept. lst_cbn. unfold vi, vl. entailer!.
      * forward. Exists v. entailer!.
Qed.
