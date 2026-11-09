(* The body proofs of the unit patch/caps_unit.c (boot/pci-capabilities.h and its wrapper), for every device
   predicate Dev: pci_capability_finish, pci_collect_capabilities (the walker, against the functional model `walk` of
   Defs.v) and caps_collect (one call).  The walker's proof follows the C: the snapshot reset, the argument chain
   (ARGUMENT), the four header reads (READ_FAILED, HEADER_CHANGED) under the invariant hdr_inv, and the list loop
   (POINTER, CYCLE, the capacity guard, READ_FAILED, ABSENT, OK) under the invariant chain_inv, with the `seen` bitmask
   represented by seen_rep and the headers written so far by hdrs (CollectLemmas.v). *)
Require Import VST.floyd.proofauto.
Require Import LeanosCaps.caps.code.
Require Import LeanosCaps.proof.Defs.
Require Import LeanosCaps.proof.CapsSpecs.
Require Import LeanosCaps.proof.CollectLemmas.
#[local] Existing Instance CapsSpecs.CS.
Local Open Scope Z_scope.

Lemma body_pci_capability_finish (Dev: val -> Z * Z * Z -> list answer -> mpred) :
  semax_body Vprog (Gprog Dev) f_pci_capability_finish finish_spec.
Proof.
  start_function.
  unfold maybe_at.
  destruct (Val.eq result nullval).
  - subst. forward_if (PROP () LOCAL (temp _status (Vint (Int.repr st))) SEP ()).
    + contradiction.
    + forward. entailer!.
    + forward.
  - forward_if (PROP () LOCAL (temp _status (Vint (Int.repr st))) SEP (data_at Tsh t_result (result_val st off) result)).
    + forward. forward. unfold result_val. entailer!. apply derives_refl.
    + contradiction.
    + forward. unfold maybe_at. destruct (Val.eq result nullval); [ contradiction | apply derives_refl ].
Qed.

(* ---------- tactics for the walker ---------- *)

(* offsets[i] and masks[i] of the header loop, as the i-th check of header_checks. *)
Ltac fix_znth := repeat match goal with |- context [Znth ?i ?L] =>
   lazymatch L with context [header_checks] => idtac | _ => fail end;
   first [ replace (Znth i L) with (Vint (Int.repr (hc_off i)))
             by (destruct (hc_cases i ltac:(lia)) as [ -> | [ -> | [ -> | -> ] ] ]; reflexivity)
         | replace (Znth i L) with (Vint (Int.repr (hc_mask i)))
             by (destruct (hc_cases i ltac:(lia)) as [ -> | [ -> | [ -> | -> ] ] ];
                 first [ reflexivity | rewrite repr_m1; reflexivity ]) ] end.

(* The type check of a load of offsets[i] or masks[i]. *)
Ltac tc_off := entailer!;
  match goal with |- context [Znth ?j _] =>
    let Hj := fresh "Hj" in
    assert (Hj: j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by lia;
    destruct Hj as [Hj | [Hj | [Hj | Hj]]]; rewrite Hj; simpl;
    first [ exact I | rewrite Int.unsigned_repr by rep_lia; rep_lia ]
  end.

(* A branch whose condition contradicts what is known. *)
Ltac dead := first [ discriminate | contradiction
  | exfalso; match goal with H: ?a <> ?b |- _ => apply H; reflexivity end | exfalso; lia ].

(* The postcondition at a return past the argument checks. *)
Ltac close_ret :=
  repeat match goal with
  | H: ?p <> nullval |- context [maybe_at ?sh ?t ?v ?p] => rewrite (maybe_at_nonnull sh t v p H)
  | H: ?p <> nullval |- context [maybe_read ?D ?p] => rewrite (maybe_read_nonnull D p H)
  end;
  first [ match goal with H: negb (args_ok ?a ?b ?c) = false |- context [negb (args_ok ?a ?b ?c)] => rewrite H end
        | match goal with H: args_ok ?a ?b ?c = true |- context [args_ok ?a ?b ?c] => rewrite H end ];
  cbn [orb negb]; entailer!.

(* The division check of initial->words[offsets[i] / 4]. *)
Ltac divs_tc := match goal with X: _ /\ Int.repr 4 = Int.mone |- _ =>
  destruct X as [_ X]; apply (f_equal Int.unsigned) in X; vm_compute in X; discriminate end.

(* The header comparison (value & masks[i]) != (initial->words[offsets[i] / 4] & masks[i]) on Z. *)
Ltac cmp_hyp i := match goal with H: context [Int.and (Int.repr _) (Int.repr (hc_mask i))] |- _ =>
  change (let (q, _) := Z.div_eucl (hc_off i) 4 in q) with (hc_off i / 4) in H;
  rewrite and_repr_eq in H by (auto; unfold u32_ok in *; lia) end.

Lemma body_pci_collect_capabilities (Dev: val -> Z * Z * Z -> list answer -> mpred) :
  semax_body Vprog (Gprog Dev) f_pci_collect_capabilities (collect_spec Dev).
Proof.
  start_function.
  unfold u8_ok, u32_ok in *.
  forward_if (EX hs0: list (reptype t_cap),
    PROP (Zlength hs0 = 48)
    LOCAL (lvar _raw tuint v_raw; lvar _value tuint v_value; lvar _masks (tarray tuint 4) v_masks;
           lvar _offsets (tarray tuchar 4) v_offsets; temp _read read; temp _context ctx; temp _initial initial;
           temp _snapshot snapshot; temp _result result)
    SEP (data_at_ Tsh tuint v_raw; data_at_ Tsh tuint v_value; data_at_ Tsh (tarray tuint 4) v_masks;
         data_at_ Tsh (tarray tuchar 4) v_offsets; maybe_read Dev read; Dev ctx (bus, dev, fn) [];
         maybe_at ish t_header (header_val bus dev fn words) initial;
         maybe_at Tsh t_snapshot (snapshot_val 0 hs0) snapshot; maybe_at Tsh t_result rold result)).
  tc_ptr.
  { rewrite (maybe_at_nonnull Tsh t_snapshot _ snapshot) by (intro; subst; contradiction).
    forward.
    Exists (snd sold). rewrite (maybe_at_nonnull _ _ _ snapshot) by (intro; subst; contradiction). entailer!.
    match goal with H: value_fits t_snapshot _ |- _ => apply value_fits_snapshot in H; exact H end. }
  { forward. subst snapshot. Exists (Zrepeat (default_val t_cap) 48). rewrite !maybe_at_null. entailer!. }
  Intros hs0.
  forward_if (temp _t'2 (Vint (Int.repr (b2z (isnull read || isnull initial))))).
  tc_ptr.
  { forward; subst read; rewrite isnull_null; entailer!. }
  { forward. entailer!. tc_ptr. entailer!. rewrite notbool_ptr by auto. rewrite (isnull_nonnull read) by auto. reflexivity. }
  forward_if (temp _t'3 (Vint (Int.repr (b2z (isnull read || isnull initial || isnull snapshot))))).
  { t_then. }
  { t_ptr. }
  destruct (isnull read || isnull initial || isnull snapshot)%bool eqn:N3.
  { (* some pointer is NULL: ARGUMENT *)
    forward_if (temp _t'4 (Vint (Int.repr 1))); [ forward; entailer! | bfix; discriminate | ].
    forward_if (temp _t'5 (Vint (Int.repr 1))); [ forward; entailer! | discriminate | ].
    forward_if (temp _t'6 (Vint (Int.repr 1))); [ forward; entailer! | discriminate | ].
    forward_if (temp _t'7 (Vint (Int.repr 1))); [ forward; entailer! | discriminate | ].
    forward_if; [ | discriminate ].
    forward_call (result, rold, 1, 0); try (unfold u8_ok; rep_lia).
    forward.
    Exists (@nil answer) 1 0 (@nil (Z * Z)) hs0.
    entailer!; try (rewrite orb_true_l; repeat split; reflexivity); try apply derives_refl. }
  (* read, initial and snapshot are not NULL *)
  apply orb_false_iff in N3; destruct N3 as [N3 Nsnap]; apply orb_false_iff in N3; destruct N3 as [Nread Ninit].
  apply isnull_false in Nread, Ninit, Nsnap.
  rewrite (maybe_read_nonnull Dev read) by auto.
  rewrite (maybe_at_nonnull ish t_header _ initial) by auto.
  rewrite (maybe_at_nonnull Tsh t_snapshot _ snapshot) by auto.
  unfold header_val.
  assert (W0: 0 <= Znth 0 words <= Int.max_unsigned) by (apply Forall_Znth; auto; lia).
  assert (W1: 0 <= Znth 1 words <= Int.max_unsigned) by (apply Forall_Znth; auto; lia).
  assert (W3: 0 <= Znth 3 words <= Int.max_unsigned) by (apply Forall_Znth; auto; lia).
  assert (W13: 0 <= Znth 13 words <= Int.max_unsigned) by (apply Forall_Znth; auto; lia).
  forward_if (temp _t'4 (Vint (Int.repr (b2z (negb (dev <=? 31)))))).
  { exfalso; lia. }
  { forward. { entailer!. rep_lia. }
    forward. entailer!. rewrite bool2val_b2z. bdecide. }
  forward_if (temp _t'5 (Vint (Int.repr (b2z (negb (dev <=? 31) || negb (fn <=? 7)))))).
  { t_then. }
  { bfix. forward. { entailer!. rep_lia. }
    forward. entailer!. rewrite bool2val_b2z. brw. bdecide. }
  forward_if (temp _t'6 (Vint (Int.repr (b2z (negb (dev <=? 31) || negb (fn <=? 7) ||
                                               negb (Z.land (Z.shiftr (Znth 3 words) 16) 127 <=? 1)))))).
  { t_then. }
  { bfix. forward. forward. entailer!.
    pose proof (land127_range (Z.shiftr (Znth 3 words) 16)).
    rewrite bool2val_b2z, shru_repr, and_repr, ltu_repr by (try apply shiftr_range; rep_lia).
    brw. bdecide. }
  forward_if (temp _t'7 (Vint (Int.repr (b2z (negb (dev <=? 31) || negb (fn <=? 7) ||
                                               negb (Z.land (Z.shiftr (Znth 3 words) 16) 127 <=? 1) ||
                                               (Z.land (Znth 0 words) 65535 =? 65535)))))).
  { t_then. }
  { bfix. forward. forward. entailer!.
    pose proof (land65535_range (Znth 0 words)).
    rewrite bool2val_b2z, eq_repr by rep_lia. brw. bdecide. }
  rewrite args_disj.
  forward_if.
  { (* args_ok fails: ARGUMENT *)
    bfix. apply negb_true_iff in H9.
    forward_call (result, rold, 1, 0); try (unfold u8_ok; rep_lia).
    forward.
    Exists (@nil answer) 1 0 (@nil (Z * Z)) hs0.
    rewrite H9.
    rewrite (maybe_read_nonnull Dev read), (maybe_at_nonnull ish t_header _ initial),
      (maybe_at_nonnull Tsh t_snapshot _ snapshot) by auto.
    entailer!. simpl; repeat split; reflexivity. }
  bfix. apply negb_false_iff in H9. rename H9 into Hargs.
  deadvars!.
  forward. forward. forward. forward. forward. forward. forward. forward.
  match goal with |- context [data_at Tsh (tarray tuchar 4) ?X v_offsets] =>
    replace X with (map (fun c => Vint (Int.repr (fst c))) header_checks) by reflexivity end.
  match goal with |- context [data_at Tsh (tarray tuint 4) ?X v_masks] =>
    replace X with (map (fun c => Vint (Int.repr (snd c))) header_checks) by (rewrite repr_m1; reflexivity) end.
  forward_for_simple_bound 4 (EX i: Z, EX h: list answer,
    PROP (hdr_inv words i h)
    LOCAL (lvar _raw tuint v_raw; lvar _value tuint v_value; lvar _masks (tarray tuint 4) v_masks;
           lvar _offsets (tarray tuchar 4) v_offsets; temp _read read; temp _context ctx; temp _initial initial;
           temp _snapshot snapshot; temp _result result)
    SEP (data_at_ Tsh tuint v_raw; data_at_ Tsh tuint v_value;
         data_at Tsh (tarray tuint 4) (map (fun c => Vint (Int.repr (snd c))) header_checks) v_masks;
         data_at Tsh (tarray tuchar 4) (map (fun c => Vint (Int.repr (fst c))) header_checks) v_offsets;
         func_ptr' (read_spec Dev) read; Dev ctx (bus, dev, fn) h;
         data_at ish t_header (Vint (Int.repr bus), (Vint (Int.repr dev), (Vint (Int.repr fn),
           map (fun w => Vint (Int.repr w)) words))) initial;
         data_at Tsh t_snapshot (snapshot_val 0 hs0) snapshot; maybe_at Tsh t_result rold result))%assert.
  { Exists (@nil answer). entailer!. apply hdr_inv_0. }
  { cbv beta. Intros h.
    destruct (hc_facts i) as (Ho1 & Ho2 & Ho3 & Hm); [ lia | ].
    forward. { entailer!. rep_lia. }
    forward. { entailer!. rep_lia. }
    forward. { entailer!. rep_lia. }
    forward. { tc_off. }
    fix_znth.
    assert (Lh: Zlength h = i) by apply H10.
    forward_call (ctx, (bus, dev, fn), h, hc_off i, v_value).
    Intros vret. destruct vret as [ok v]. cbn [fst snd] in *.
    clear Lh.
    destruct ok.
    2: { forward_if; [ | dead ].
         forward. { tc_off. }
         fix_znth.
         forward_call (result, rold, 2, hc_off i); try (unfold u8_ok; rep_lia).
         forward.
         Exists (h ++ [(hc_off i, false, v)]) 2 (hc_off i) (@nil (Z * Z)) hs0.
         close_ret.
         apply hdr_read_failed; auto; lia. }
    forward_if; [ dead | ].
    forward.
    forward. { tc_off. }
    fix_znth.
    forward. { tc_off. }
    fix_znth.
    assert (Dq: Int.divs (Int.repr (hc_off i)) (Int.repr 4) = Int.repr (hc_off i / 4))
      by (unfold Int.divs; rewrite !Int.signed_repr by rep_lia; rewrite Z.quot_div_nonneg by lia; reflexivity).
    assert (0 <= Int.signed (Int.divs (Int.repr (hc_off i)) (Int.repr 4)) < Zlength words)
      by (rewrite Dq, Int.signed_repr by rep_lia; lia).
    forward. { entailer!. divs_tc. }
    rewrite Dq, Int.signed_repr by rep_lia.
    forward. { tc_off. }
    fix_znth.
    assert (Ww: 0 <= Znth (hc_off i / 4) words <= Int.max_unsigned) by (apply Forall_Znth; auto; lia).
    forward_if.
    { cmp_hyp i.
      forward. { tc_off. }
      fix_znth.
      forward_call (result, rold, 3, hc_off i); try (unfold u8_ok; rep_lia).
      forward.
      Exists (h ++ [(hc_off i, true, v)]) 3 (hc_off i) (@nil (Z * Z)) hs0.
      close_ret.
      apply hdr_changed; auto; lia. }
    { cmp_hyp i.
      forward.
      Exists (h ++ [(hc_off i, true, v)]).
      entailer!.
      apply hdr_pass; auto; lia. } }
  Intros h.
  forward. forward. forward.
  forward_if (temp _t'11 (Vint (Int.repr (list_head words)))).
  { forward. forward. entailer!.
    match goal with H: Int.and _ _ <> Int.zero |- _ => rewrite and_repr in H;
      assert (Z.land (Znth 1 words) 1048576 <> 0) by (intro E; rewrite E in H; apply H; reflexivity) end.
    unfold list_head. destruct (Z.eqb_spec (Z.land (Znth 1 words) 1048576) 0); [ contradiction | ].
    rewrite zext8_land. reflexivity. }
  { forward. entailer!.
    match goal with H: Int.and _ _ = Int.zero |- _ => rewrite and_repr in H; apply (f_equal Int.unsigned) in H;
      rewrite Int.unsigned_repr in H by (pose proof (land_range (Znth 1 words) 1048576 W1 ltac:(rep_lia)); rep_lia);
      change (Int.unsigned Int.zero) with 0 in H; unfold list_head; rewrite H; reflexivity end. }
  pose proof (list_head_range words) as LH.
  forward.
  rewrite zext8_small by auto.
  forward_while (EX count: Z, EX next: Z, EX acc: list (Z * Z), EX sv: int64, EX h': list answer,
    PROP (0 <= count <= 48; Zlength acc = count; Zlength h' = (4 + count)%Z; 0 <= next <= 255;
          Forall voff (map fst acc); seen_rep sv (map fst acc); chain_inv words h' next count acc)
    LOCAL (temp _offset (Vint (Int.repr next)); temp _seen (Vlong sv); temp _count (Vint (Int.repr count));
           lvar _raw tuint v_raw; lvar _value tuint v_value; lvar _masks (tarray tuint 4) v_masks;
           lvar _offsets (tarray tuchar 4) v_offsets; temp _read read; temp _context ctx; temp _initial initial;
           temp _snapshot snapshot; temp _result result)
    SEP (data_at_ Tsh tuint v_raw; data_at_ Tsh tuint v_value;
         data_at Tsh (tarray tuint 4) (map (fun c => Vint (Int.repr (snd c))) header_checks) v_masks;
         data_at Tsh (tarray tuchar 4) (map (fun c => Vint (Int.repr (fst c))) header_checks) v_offsets;
         func_ptr' (read_spec Dev) read; Dev ctx (bus, dev, fn) h';
         data_at ish t_header (Vint (Int.repr bus), (Vint (Int.repr dev), (Vint (Int.repr fn),
           map (fun w => Vint (Int.repr w)) words))) initial;
         data_at Tsh t_snapshot (snapshot_val 0 (hdrs acc hs0)) snapshot; maybe_at Tsh t_result rold result))%assert.
  { Exists 0 (list_head words) (@nil (Z * Z)) (Int64.repr 0) h.
    rewrite hdrs_nil by auto.
    entailer!.
    split; [ apply H9 | split; [ apply seen_rep_nil | apply chain_inv_start; auto ] ]. }
  { entailer!. }
  { (* the loop body *)
    apply typed_true_uchar in HRE. rename HRE into Hn0.
    assert (LHd: Zlength (hdrs acc hs0) = 48) by (apply Zlength_hdrs; lia).
    forward_if (temp _t'13 (Vint (Int.repr (b2z (bad_ptr next))))).
    { forward. entailer!. unfold bad_ptr. rewrite (proj2 (Z.ltb_lt next 64)) by lia. reflexivity. }
    { forward. entailer!.
      unfold bad_ptr. rewrite (proj2 (Z.ltb_ge next 64)) by lia. change Int.zero with (Int.repr 0) at 1.
      rewrite eq_repr by (pose proof (land3_range next); rep_lia). destruct (Z.land next 3 =? 0); reflexivity. }
    forward_if.
    { (* not a capability pointer: POINTER *)
      bfix.
      assert (Wf: walk words h' = Some (S_POINTER, next, [])) by (eapply chain_pointer; eauto).
      forward_call (result, rold, 4, next); try (unfold u8_ok; rep_lia).
      forward.
      Exists h' 4 next (@nil (Z * Z)) (hdrs acc hs0).
      close_ret. }
    bfix. rename H17 into Hptr.
    pose proof (bad_ptr_voff next H13 Hptr) as Vn.
    pose proof (voff_bitidx next Vn) as Bn.
    forward.
    { entailer!. destruct Vn as [Vn1 Vn2].
      pose proof (bit_range next ltac:(lia)).
      rewrite bit_divs, Int.unsigned_repr by (unfold bitidx; rep_lia).
      change (Int.unsigned Int64.iwordsize') with 64. unfold bitidx.
      split; [ lia | intros [_ X]; apply (f_equal Int.unsigned) in X; vm_compute in X; discriminate ]. }
    rewrite bit_unsigned by auto.
    forward_if.
    { (* already seen: CYCLE *)
      assert (Wf: walk words h' = Some (S_CYCLE, next, [])) by (eapply chain_cycle; eauto; eapply seen_hit; eauto).
      forward_call (result, rold, 5, next); try (unfold u8_ok; rep_lia).
      forward.
      Exists h' 5 next (@nil (Z * Z)) (hdrs acc hs0).
      close_ret. }
    assert (Ncy: existsb (Z.eqb next) (map fst acc) = false) by (eapply seen_miss; eauto).
    forward_if.
    { (* the array is full: POINTER *)
      assert (Wf: walk words h' = Some (S_POINTER, next, []))
        by (match goal with E: count = 48, C: chain_inv _ _ _ count _ |- _ => rewrite E in C; eapply chain_full; eauto end).
      forward_call (result, rold, 4, next); try (unfold u8_ok; rep_lia).
      forward.
      Exists h' 4 next (@nil (Z * Z)) (hdrs acc hs0).
      close_ret. }
    assert (Hc48: 0 <= count < 48) by lia.
    forward.
    forward. { entailer!. rep_lia. }
    forward. { entailer!. rep_lia. }
    forward. { entailer!. rep_lia. }
    destruct Vn as [Vn1 Vn2].
    forward_call (ctx, (bus, dev, fn), h', next, v_raw).
    Intros vret. destruct vret as [ok v]. cbn [fst snd] in *.
    destruct ok.
    2: { (* the read failed: READ_FAILED *)
      forward_if; [ | dead ].
      assert (Wf: walk words (h' ++ [(next, false, v)]) = Some (S_READ_FAILED, next, []))
        by (eapply chain_read_failed; eauto).
      forward_call (result, rold, 2, next); try (unfold u8_ok; rep_lia).
      forward.
      Exists (h' ++ [(next, false, v)]) 2 next (@nil (Z * Z)) (hdrs acc hs0).
      close_ret. }
    forward_if; [ dead | ].
    forward.
    forward_if.
    { (* no capability here: ABSENT *)
      match goal with H: Int.and (Int.repr v) (Int.repr 255) = Int.repr 255 |- _ =>
        apply and255_eq in H; [ | auto ] end.
      assert (Wf: walk words (h' ++ [(next, true, v)]) = Some (S_ABSENT, next, []))
        by (eapply chain_absent; eauto).
      forward_call (result, rold, 6, next); try (unfold u8_ok; rep_lia).
      forward.
      Exists (h' ++ [(next, true, v)]) 6 next (@nil (Z * Z)) (hdrs acc hs0).
      close_ret. }
    assert (Nab: Z.land v 255 <> 255).
    { intro E. match goal with H: Int.and (Int.repr v) (Int.repr 255) <> Int.repr 255 |- _ => apply H end.
      rewrite and_repr, E. reflexivity. }
    forward.
    forward.
    forward.
    rewrite zext8_small by lia.
    match goal with |- context [data_at Tsh t_snapshot ?X snapshot] =>
      replace X with (snapshot_val 0 (hdrs ((next, v) :: acc) hs0)) end.
    2: { unfold snapshot_val. cbn [fst snd]. f_equal. subst count. symmetry. apply hdrs_store; auto; lia. }
    forward.
    forward.
    forward.
    rewrite next_ptr by auto.
    Exists (count + 1, Z.land (Z.shiftr v 8) 255, (next, v) :: acc,
            Int64.or sv (Int64.shl (Int64.repr 1) (Int64.repr (bitidx next))), h' ++ [(next, true, v)]).
    entailer!.
    pose proof (land255_range (Z.shiftr v 8)).
    repeat match goal with |- _ /\ _ => split end.
    all: first [ lia | (rewrite Zlength_cons; lia) | (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia)
               | (constructor; [ split; auto | auto ]) | (apply seen_rep_cons; auto; split; auto)
               | (apply chain_step; auto) ]. }
  (* the list ended: OK *)
  apply typed_false_uchar in HRE; [ subst next | auto ].
  forward.
  forward_call (result, rold, 0, 0); try (unfold u8_ok; rep_lia).
  forward.
  Exists h' 0 0 (rev acc) (sublist (Zlength acc) 48 hs0).
  assert (Wf: walk words h' = Some (S_OK, 0, rev acc)) by (eapply chain_ok; eauto).
  rewrite Zlength_rev.
  close_ret.
  rewrite Zlength_sublist by (pose proof (Zlength_nonneg acc); lia); lia.
Qed.

Lemma body_caps_collect (Dev: val -> Z * Z * Z -> list answer -> mpred) :
  semax_body Vprog (Gprog Dev) f_caps_collect (caps_collect_spec Dev).
Proof.
  start_function.
  forward_call.
  Intros vret. destruct vret as [[[[h st] off] caps] rest]. cbn [fst snd] in *.
  forward.
  Exists h st off caps rest.
  entailer!.
Qed.
