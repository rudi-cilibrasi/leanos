(* Law handoff_decode_exact: main after the function returned: its checks (the protocol ended with the status, the
   copy and the words a decoder alone reads as the law's arrays, the bitmaps and the states as the law's, the three
   records as the outcome's), from the law's oracle at a complete run (returns: ret_inv, the pointers of its arrays
   pinned to main's) and what the call's specification gave. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosHandoff.harness.handoff_decode_exact.code.
Require Import LeanosHandoff.proof.Defs.
Require Import LeanosHandoff.proof.HandoffSpecs.
Require Import LeanosHandoff.proof.LawProg LeanosHandoff.proof.LawDefs LeanosHandoff.proof.LawFacts
  LeanosHandoff.proof.LawLib LeanosHandoff.proof.LawLib2 LeanosHandoff.proof.LawLib3 LeanosHandoff.proof.LawZero
  LeanosHandoff.proof.LawMainDefs LeanosHandoff.proof.LawMainPre LeanosHandoff.proof.LawMainPre2
  LeanosHandoff.proof.LawMainPre3.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[local] Existing Instance LawProg.LCS.

Lemma hc_xm: forall x cep iep, has_copy (xm x cep iep) = has_copy x.
Proof. reflexivity. Qed.

Lemma i_info_xm1: forall x cep iep, has_copy x = true -> i_info (xm x cep iep) = enc_ptr cep.
Proof. intros x cep iep H. unfold xm; cbn [i_info]. rewrite H. reflexivity. Qed.

Lemma i_info_xm0: forall x cep iep, has_copy x = false -> i_info (xm x cep iep) = i_info x.
Proof. intros x cep iep H. unfold xm; cbn [i_info]. rewrite H. reflexivity. Qed.

Lemma i_copy_xm0: forall x cep iep, has_copy x = false -> i_copy (xm x cep iep) = enc_ptr iep.
Proof. intros x cep iep H. unfold xm; cbn [i_copy]. rewrite H. reflexivity. Qed.

(* The two expectation arrays, the law's and main's own, at main's pointers. *)
Lemma arrays_uniform: forall x cep iep ce ie m, filled x -> isptr cep -> isptr iep ->
  ptr_ok (xm x cep iep) ce ie ->
  (arrays (xm x cep iep) ce ie m * own_obj x cep iep)%logic |--
  (data_at Ews (tarray tulong (copy_len x)) (map vl (if has_copy x then m_copy m else i_copy x)) cep *
   data_at Ews (tarray tulong (info_len x)) (map vl (i_info x)) iep)%logic.
Proof.
  intros x cep iep ce ie m Fx Pc Pi (_ & Pp).
  pose proof Fx as (F1 & _ & F3 & _).
  unfold arrays, info_obj, own_obj. rewrite hc_xm in *.
  destruct (has_copy x) eqn:Hc; cbv iota in Pp |- *.
  - rewrite (i_info_xm1 x cep iep Hc), dec_enc in Pp by auto. subst ce.
    replace (copy_len x) with COPY_WORDS by (unfold copy_len, has_copy in *; destruct (i_call x); congruence).
    rewrite sepcon_emp. apply derives_refl.
  - rewrite (i_copy_xm0 x cep iep Hc), dec_enc in Pp by auto. subst ie.
    rewrite (i_info_xm0 x cep iep Hc), F3. rewrite emp_sepcon, sepcon_comm. apply derives_refl.
Qed.

Lemma ora_unfold: forall gv ctx rctx x h, Ora_law gv ctx rctx x h =
  (EX p: progress, EX s: lst, EX ce: val, EX ie: val,
    !! (ctx = gv _law /\ rctx = gv _law /\ inputs_ok x /\ x_fit x /\ run x (start x) h = Some p /\ J x p s /\
        ptr_ok x ce ie) &&
    (lfields (gv _law) x ce ie (mem_of p) s * arrays x ce ie (mem_of p)))%logic.
Proof. reflexivity. Qed.

Lemma words_get: forall (d: Inhabitant val) (L: list Z) i, 0 <= i < Zlength L ->
  @Znth val d i (map vl L) = vl (Znth i L).
Proof.
  intros d L i I. rewrite (Znth_dflt d Inhabitant_val) by (rewrite Zlength_map; lia).
  rewrite Znth_map by lia. reflexivity.
Qed.

Lemma states_get: forall (d1: Inhabitant (list val)) (d2: Inhabitant val) (S: list (list Z)) k i,
  0 <= k < Zlength S -> 0 <= i < Zlength (Znth k S) ->
  @Znth val d2 i (@Znth (list val) d1 k (states_val S)) = vl (Znth i (Znth k S)).
Proof.
  intros d1 d2 S k i K I. unfold states_val. rewrite (Znth_dflt d1 Inhabitant_list) by (rewrite Zlength_map; lia).
  rewrite Znth_map by lia. apply words_get; auto.
Qed.

Lemma is_copy_1: forall x, call_code (i_call x) = 1 -> is_copy x = true.
Proof. intros x H. unfold is_copy. destruct (i_call x); simpl in H; congruence || reflexivity. Qed.

Lemma is_copy_n1: forall x, call_code (i_call x) <> 1 -> is_copy x = false.
Proof. intros x H. unfold is_copy. destruct (i_call x); simpl in H; congruence || reflexivity. Qed.

Lemma out_tot_b: forall x cep iep m,
  out_total_record (xm x cep iep) m = if m_extent_ok m then m_total m else i_total_record x.
Proof. reflexivity. Qed.

Lemma out_len_b: forall x cep iep st m,
  out_length_record (xm x cep iep) st m = if is_copy x && (st =? S_OK) then m_total m else i_length_record x.
Proof. reflexivity. Qed.

Lemma out_cur_b: forall x cep iep st m,
  out_current_record (xm x cep iep) st m =
  if negb (is_copy x) && (st =? S_OK) then m_at m else i_current_record x.
Proof. reflexivity. Qed.

(* A check's side condition: its argument true. *)
Ltac gp_side :=
  match goal with
  | |- ENTAIL _, _ |-- _ => entailer!; rewrite ?Int.eq_true, ?Int64.eq_true; try reflexivity; try cmp_close
  | _ => idtac
  end.

(* A load of word i of main's array or of the law's. *)
Ltac ld_side := match goal with |- ENTAIL _, _ |-- _ => entailer! | _ => idtac end.
Ltac ld_word := forward; rewrite ?words_get by lia; ld_side.
Ltac ld_state := forward; rewrite ?states_get by lia; ld_side.

Lemma tail_check {Espec: OracleKind}: @check_ok Espec.
Proof.
  intros gv x h st m cp cep ip iep up bp rp sp vtr vlr vcr vpj Hr Fx Pcep Piep.
  unfold check_pre, s_check. start_tail_main.
  rewrite (ora_unfold gv (gv _law) (gv _law) (xm x cep iep) h). Intros p s ce ie.
  match goal with H: run _ (start _) h = Some p |- _ => rename H into Hrun end.
  match goal with H: J _ p s |- _ => rename H into HJ end.
  match goal with H: ptr_ok _ ce ie |- _ => rename H into Po end.
  match goal with H: inputs_ok _ |- _ => rename H into Ix end.
  assert (Ep: p = Return st m)
    by (unfold returns in Hr; rewrite Hrun in Hr; destruct p; [ discriminate | inversion Hr; reflexivity ]).
  subst p. destruct HJ as (Hs & Hm & (Ge & Gv)). cbn [mem_of] in Hm |- *.
  sep_apply (arrays_uniform x cep iep ce ie m Fx Pcep Piep Po).
  unfold lfields. Intros.
  change (i_call (xm x cep iep)) with (i_call x).
  rewrite Ge, Gv. unfold E_NOTHING.
  pose proof Hs as (_ & _ & _ & Lv & _). rewrite Gv in Lv. unfold u32_ok in Lv.
  pose proof Hm as (Mt & Mcl & Mcf & Mul & Muf & Mbl & Mbf & Mrl & Mrf & Msl & Ms0 & Ms1 & Mat).
  pose proof Fx as (F1 & F2 & F3 & F4 & _).
  pose proof (call_code_range (i_call x)) as Rc.
  pose proof Ix as (_ & _ & It & _). cbn [xm i_total] in It. unfold u32_ok in It.
  assert (Rcl: 0 <= copy_len x <= 8192) by (unfold copy_len; destruct (i_call x); lia).
  assert (Ril: 0 <= info_len x <= Int.max_signed)
    by (unfold info_len; destruct (is_alloc x); [ rep_lia | split; [ apply Z.div_pos | apply Z.div_le_upper_bound ]; rep_lia ]).
  assert (LL: Zlength (if has_copy x then m_copy m else i_copy x) = copy_len x).
  { destruct (has_copy x) eqn:Hc; [ rewrite (Mcl Hc) | exact F1 ].
    unfold copy_len, has_copy in *; destruct (i_call x); congruence. }
  assert (Lrow: forall k, 0 <= k < 2 -> Zlength (Znth k (m_states m)) = 41).
  { intros k K. assert (k = 0 \/ k = 1) as [-> | ->] by lia; [ apply Ms0 | apply Ms1 ]. }
  (* the protocol ended, with the status *)
  forward. forward_call Int.one; gp_side.
  forward. forward_call Int.one; gp_side.
  (* the copy *)
  freeze_but (@nil ident) [cp; cep] FC.
  forward_for_simple_bound (copy_len x)
    (EX i: Z, PROP () LOCAL (temp _status (vi st); temp _m (gv _law); temp _copy_words (vi (copy_len x)); temp _copy cp;
            temp _copy_expect cep; temp _info_words (vi (info_len x)); temp _info ip; temp _info_expect iep;
            temp _usable up; temp _blocked bp; temp _reserved rp; temp _states sp;
            temp _total_prior (vi (i_total_record x)); temp _length_prior (vi (i_length_record x));
            temp _current_prior (vi (i_current_record x));
            lvar _total_record tuint vtr; lvar _length_record tuint vlr; lvar _current_record tuint vcr;
            lvar _projection t_projection vpj; gvars gv)
     SEP (FRZL FC;
          data_at Ews (tarray tulong (copy_len x)) (map vl (if has_copy x then m_copy m else i_copy x)) cp;
          data_at Ews (tarray tulong (copy_len x)) (map vl (if has_copy x then m_copy m else i_copy x)) cep))%assert.
  { entailer!. }
  { ld_word. ld_word. vl_temps. forward_call Int.one; gp_side. }
  thaw FC.
  (* the words a decoder alone reads *)
  freeze_but (@nil ident) [ip; iep] FI.
  forward_for_simple_bound (info_len x)
    (EX i: Z, PROP () LOCAL (temp _status (vi st); temp _m (gv _law); temp _copy_words (vi (copy_len x)); temp _copy cp;
            temp _copy_expect cep; temp _info_words (vi (info_len x)); temp _info ip; temp _info_expect iep;
            temp _usable up; temp _blocked bp; temp _reserved rp; temp _states sp;
            temp _total_prior (vi (i_total_record x)); temp _length_prior (vi (i_length_record x));
            temp _current_prior (vi (i_current_record x));
            lvar _total_record tuint vtr; lvar _length_record tuint vlr; lvar _current_record tuint vcr;
            lvar _projection t_projection vpj; gvars gv)
     SEP (FRZL FI;
          data_at Ews (tarray tulong (info_len x)) (map vl (i_info x)) ip;
          data_at Ews (tarray tulong (info_len x)) (map vl (i_info x)) iep))%assert.
  { entailer!. }
  { ld_word. ld_word. vl_temps. forward_call Int.one; gp_side. }
  thaw FI.
  (* the bitmaps *)
  freeze_but [_usable_expect; _blocked_expect; _reserved_expect] [up; bp; rp] FB.
  forward_for_simple_bound 64
    (EX b: Z, PROP () LOCAL (temp _status (vi st); temp _m (gv _law); temp _copy_words (vi (copy_len x)); temp _copy cp;
            temp _copy_expect cep; temp _info_words (vi (info_len x)); temp _info ip; temp _info_expect iep;
            temp _usable up; temp _blocked bp; temp _reserved rp; temp _states sp;
            temp _total_prior (vi (i_total_record x)); temp _length_prior (vi (i_length_record x));
            temp _current_prior (vi (i_current_record x));
            lvar _total_record tuint vtr; lvar _length_record tuint vlr; lvar _current_record tuint vcr;
            lvar _projection t_projection vpj; gvars gv)
     SEP (FRZL FB;
          data_at Ews (tarray tulong 64) (map vl (m_usable m)) up;
          data_at Ews (tarray tulong 64) (map vl (m_blocked m)) bp;
          data_at Ews (tarray tulong 64) (map vl (m_reserved m)) rp;
          field_at Ews t_law (DOT _usable_expect) (map vl (m_usable m)) (gv _law);
          field_at Ews t_law (DOT _blocked_expect) (map vl (m_blocked m)) (gv _law);
          field_at Ews t_law (DOT _reserved_expect) (map vl (m_reserved m)) (gv _law)))%assert.
  { entailer!. }
  { ld_word. ld_word. vl_temps.
    forward_if (temp _t'41 (Vint Int.one)).
    { ld_word. ld_word. vl_temps. forward. entailer!; cmp_close. }
    { else_false. }
    forward_if (temp _t'42 (Vint Int.one)).
    { ld_word. ld_word. vl_temps. forward. entailer!; cmp_close. }
    { else_false. }
    forward_call Int.one; gp_side. }
  thaw FB.
  (* the states *)
  freeze_but [_states_expect] [sp] FS.
  forward_for_simple_bound 2
    (EX k: Z, PROP () LOCAL (temp _status (vi st); temp _m (gv _law); temp _copy_words (vi (copy_len x)); temp _copy cp;
            temp _copy_expect cep; temp _info_words (vi (info_len x)); temp _info ip; temp _info_expect iep;
            temp _usable up; temp _blocked bp; temp _reserved rp; temp _states sp;
            temp _total_prior (vi (i_total_record x)); temp _length_prior (vi (i_length_record x));
            temp _current_prior (vi (i_current_record x));
            lvar _total_record tuint vtr; lvar _length_record tuint vlr; lvar _current_record tuint vcr;
            lvar _projection t_projection vpj; gvars gv)
     SEP (FRZL FS; data_at Ews t_states (states_val (m_states m)) sp;
          field_at Ews t_law (DOT _states_expect) (states_val (m_states m)) (gv _law)))%assert.
  { entailer!. }
  { assert (Lk: Zlength (Znth i (m_states m)) = 41) by (apply Lrow; lia).
    forward_for_simple_bound 41
      (EX j: Z, PROP () LOCAL (temp _k__1 (vi i); temp _status (vi st); temp _m (gv _law); temp _copy_words (vi (copy_len x)); temp _copy cp;
            temp _copy_expect cep; temp _info_words (vi (info_len x)); temp _info ip; temp _info_expect iep;
            temp _usable up; temp _blocked bp; temp _reserved rp; temp _states sp;
            temp _total_prior (vi (i_total_record x)); temp _length_prior (vi (i_length_record x));
            temp _current_prior (vi (i_current_record x));
            lvar _total_record tuint vtr; lvar _length_record tuint vlr; lvar _current_record tuint vcr;
            lvar _projection t_projection vpj; gvars gv)
       SEP (FRZL FS; data_at Ews t_states (states_val (m_states m)) sp;
            field_at Ews t_law (DOT _states_expect) (states_val (m_states m)) (gv _law)))%assert.
    { entailer!. }
    { ld_state. ld_state. vl_temps. forward_call Int.one; gp_side. }
    entailer!. }
  thaw FS.
  (* the three records *)
  forward.
  forward_if (temp _t'43 (vi (out_total_record (xm x cep iep) m))).
  { try b2z_hyp. forward. forward. entailer!. rewrite out_tot_b.
    match goal with E: m_extent_ok m = true |- _ => rewrite E end. reflexivity. }
  { try b2z_hyp. forward. entailer!. rewrite out_tot_b.
    match goal with E: m_extent_ok m = false |- _ => rewrite E end. reflexivity. }
  forward. forward_call Int.one; gp_side.
  forward.
  forward_if (temp _t'44 (Vint (Int.repr (Z.b2z (is_copy x && (st =? S_OK)))))).
  { u64c. forward. entailer!. rewrite (is_copy_1 x) by assumption. unfold S_OK. cmp_close. }
  { u64c. forward. entailer!. rewrite (is_copy_n1 x) by assumption. reflexivity. }
  forward_if (temp _t'45 (vi (out_length_record (xm x cep iep) st m))).
  { try b2z_hyp. forward. forward. entailer!. rewrite out_len_b.
    match goal with E: (is_copy x && _) = true |- _ => rewrite E end. reflexivity. }
  { try b2z_hyp. forward. entailer!. rewrite out_len_b.
    match goal with E: (is_copy x && _) = false |- _ => rewrite E end. reflexivity. }
  forward. forward_call Int.one; gp_side.
  forward.
  forward_if (temp _t'46 (Vint (Int.repr (Z.b2z (negb (is_copy x) && (st =? S_OK)))))).
  { u64c. forward. entailer!. rewrite (is_copy_n1 x) by assumption. unfold S_OK. cmp_close. }
  { u64c. forward. entailer!. rewrite (is_copy_1 x) by assumption. reflexivity. }
  forward_if (temp _t'47 (vi (out_current_record (xm x cep iep) st m))).
  { try b2z_hyp. forward. forward. entailer!. rewrite out_cur_b.
    match goal with E: (negb (is_copy x) && _) = true |- _ => rewrite E end. reflexivity. }
  { try b2z_hyp. forward. entailer!. rewrite out_cur_b.
    match goal with E: (negb (is_copy x) && _) = false |- _ => rewrite E end. reflexivity. }
  forward. forward_call Int.one; gp_side.
  forward. Exists (Int.repr 0). entailer!.
Qed.
