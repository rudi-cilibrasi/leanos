(* The body proof of pci_enumerate_segment (boot/pci-enumeration.h) for every device predicate Dev, against the scan
   model of Defs.v: the snapshot reset, the argument check (INVALID_ARGUMENT), then the bus/device/function loops with
   the identity read (READ_FAILED), the absence test, the capacity test (CAPACITY_EXCEEDED), the header stores and the
   word loop (READ_FAILED), and the final publication of the count (OK). *)
Require Import VST.floyd.proofauto.
Require Import LeanosEnum.enum.code.
Require Import LeanosEnum.proof.Defs.
Require Import LeanosEnum.proof.EnumSpecs.
Require Import LeanosEnum.proof.ScanLemmas.
Require Import LeanosEnum.proof.ScanSnap.
#[local] Existing Instance EnumSpecs.CS.
Local Open Scope Z_scope.

(* The invariant of the three function loops (bus, device, function): the device has answered the reads h, after
   which the scan reads the identity of function bus * 256 + device * 8 + function next, having found the headers fs
   (latest first); count = |fs|; the snapshot's count is 0 and its headers hs publish fs (pub_ok).  Inside the word
   loop the snapshot is split at headers[|fs|] (snap_split), which holds the staging header `stage n ws`. *)
Lemma body_segment (Dev: val -> list answer -> mpred) :
  semax_body Vprog (Gprog Dev) f_pci_enumerate_segment (enum_spec Dev).
Proof.
  start_function.
  forward.
  forward_if (EX hs0: list (reptype t_header),
    PROP (Zlength hs0 = 16)
    LOCAL (temp _count (Vint (Int.repr 0)); lvar _value tuint v_value; lvar _identity tuint v_identity;
           temp _read read; temp _context ctx; temp _snapshot snapshot; temp _result result)
    SEP (data_at_ Tsh tuint v_value; data_at_ Tsh tuint v_identity; maybe_read Dev read; Dev ctx [];
         maybe_at Tsh t_snapshot (snapshot_val 0 hs0) snapshot; maybe_at Tsh t_result rold result)).
  tc_ptr.
  { rewrite (maybe_at_nonnull Tsh t_snapshot _ snapshot) by (intro; subst; contradiction).
    forward.
    Exists (snd sold). rewrite (maybe_at_nonnull _ _ _ snapshot) by (intro; subst; contradiction).
    entailer!.
    match goal with H: value_fits t_snapshot _ |- _ => apply value_fits_snapshot in H; exact H end. }
  { forward. subst snapshot. Exists (Zrepeat (default_val t_header) 16). rewrite !maybe_at_null. entailer!. }
  Intros hs0.
  forward_if (temp _t'2 (Vint (Int.repr (b2z (isnull read || isnull snapshot))))).
  tc_ptr.
  { forward; subst read; rewrite isnull_null; entailer!. }
  { forward. entailer!. tc_ptr. entailer!. rewrite notbool_ptr by auto. rewrite (isnull_nonnull read) by auto. reflexivity. }
  destruct (isnull read || isnull snapshot)%bool eqn:N2.
  { (* some pointer is NULL: INVALID_ARGUMENT *)
    forward_if; [ | discriminate ].
    forward_call (result, rold, 3, 0, 0, 0, 0); try (unfold u8_ok; rep_lia).
    forward.
    Exists (@nil answer) 3 0 0 (@nil found) hs0.
    unfold result_at. destruct bdf_zero as (B0 & D0 & F0). rewrite B0, D0, F0, Zlength_nil, app_nil_l.
    entailer!. }
  apply orb_false_iff in N2; destruct N2 as [Nread Nsnap].
  apply isnull_false in Nread, Nsnap.
  forward_if; [ dead | ].
  rewrite (maybe_read_nonnull Dev read) by auto.
  rewrite (maybe_at_nonnull Tsh t_snapshot _ snapshot) by auto.
  forward_for_simple_bound 256 (EX bus: Z, EX h: list answer, EX fs: list found, EX hs: list (reptype t_header),
    PROP (run start h = Some (Go ((bus * 256)%Z, 0, fs)); pub_ok fs hs)
    LOCAL (temp _count (Vint (Int.repr (Zlength fs))); lvar _value tuint v_value; lvar _identity tuint v_identity;
           temp _read read; temp _context ctx; temp _snapshot snapshot; temp _result result)
    SEP (data_at_ Tsh tuint v_value; data_at_ Tsh tuint v_identity; func_ptr' (read_spec Dev) read; Dev ctx h;
         data_at Tsh t_snapshot (snapshot_val 0 hs) snapshot; maybe_at Tsh t_result rold result))%assert.
  { Exists (@nil answer) (@nil found) hs0. entailer!. apply pub_ok_nil; auto. }
  { cbv beta. Intros h fs hs.
    forward_for_simple_bound 32 (EX dev: Z, EX h: list answer, EX fs: list found, EX hs: list (reptype t_header),
      PROP (run start h = Some (Go ((i * 256 + dev * 8)%Z, 0, fs)); pub_ok fs hs)
      LOCAL (temp _bus (Vint (Int.repr i)); temp _count (Vint (Int.repr (Zlength fs))); lvar _value tuint v_value;
             lvar _identity tuint v_identity; temp _read read; temp _context ctx; temp _snapshot snapshot;
             temp _result result)
      SEP (data_at_ Tsh tuint v_value; data_at_ Tsh tuint v_identity; func_ptr' (read_spec Dev) read; Dev ctx h;
           data_at Tsh t_snapshot (snapshot_val 0 hs) snapshot; maybe_at Tsh t_result rold result))%assert.
    { Exists h fs hs. entailer!. all: rewrite ?Z.add_0_r; auto. }
    { cbv beta. rename i into bus. rename i0 into dev. Intros h0 fs0 hs1. clear h fs hs H5 H6.
      forward_for_simple_bound 8 (EX fn: Z, EX h: list answer, EX fs: list found, EX hs: list (reptype t_header),
        PROP (run start h = Some (Go ((bus * 256 + dev * 8 + fn)%Z, 0, fs)); pub_ok fs hs)
        LOCAL (temp _device (Vint (Int.repr dev)); temp _bus (Vint (Int.repr bus));
               temp _count (Vint (Int.repr (Zlength fs))); lvar _value tuint v_value;
               lvar _identity tuint v_identity; temp _read read; temp _context ctx; temp _snapshot snapshot;
               temp _result result)
        SEP (data_at_ Tsh tuint v_value; data_at_ Tsh tuint v_identity; func_ptr' (read_spec Dev) read; Dev ctx h;
             data_at Tsh t_snapshot (snapshot_val 0 hs) snapshot; maybe_at Tsh t_result rold result))%assert.
      { Exists h0 fs0 hs1. entailer!. all: rewrite ?Z.add_0_r; auto. }
      { cbv beta. rename i into fn. Intros h1 fs1 hs2. clear h0 fs0 hs1 H8 H9.
        assert (Bn: bus_of (bus * 256 + dev * 8 + fn) = bus) by (apply bus_of_idx; lia).
        assert (Dn: dev_of (bus * 256 + dev * 8 + fn) = dev) by (apply dev_of_idx; lia).
        assert (Fn: fn_of (bus * 256 + dev * 8 + fn) = fn) by (apply fn_of_idx; lia).
        assert (Rn: 0 <= bus * 256 + dev * 8 + fn < FUNCTIONS) by (unfold FUNCTIONS; lia).
        forward. forward. forward.
        set (n := bus * 256 + dev * 8 + fn) in *.
        assert (Eb: Int.zero_ext 8 (Int.zero_ext 8 (Int.repr bus)) = Int.repr (bus_of n))
          by (rewrite Bn, !zext8_small by lia; reflexivity).
        assert (Ed: Int.zero_ext 8 (Int.zero_ext 8 (Int.repr dev)) = Int.repr (dev_of n))
          by (rewrite Dn, !zext8_small by lia; reflexivity).
        assert (Ef: Int.zero_ext 8 (Int.zero_ext 8 (Int.repr fn)) = Int.repr (fn_of n))
          by (rewrite Fn, !zext8_small by lia; reflexivity).
        rewrite Eb, Ed, Ef. clear Eb Ed Ef.
        assert (NR: next_read h1 = Some (n, 0)) by (eapply next_read_id; eauto).
        forward_call (ctx, h1, n, 0, v_identity).
        Intros vret. destruct vret as [ok v]. cbn [fst snd] in *.
        destruct ok.
        2: { (* the identity read failed: READ_FAILED *)
          forward_if; [ | dead ].
          forward_call (result, rold, 1, bus_of n, dev_of n, fn_of n, 0); try (unfold u8_ok; rep_lia).
          forward.
          Exists (h1 ++ [(n, 0, false, v)]) 1 n 0 (@nil found) hs2.
          rewrite (maybe_read_nonnull Dev read), (maybe_at_nonnull Tsh t_snapshot _ snapshot) by auto.
          rewrite Zlength_nil, app_nil_l. unfold result_at.
          entailer!.
          split; [ destruct H10; auto | apply (scan_id_fail h1 n fs1); auto ]. }
        forward_if; [ dead | ].
        forward.
        forward_if.
        { (* absent: continue *)
          assert (A: Z.land v 65535 = 65535).
          { rewrite zext16_land in H11.
            apply repr_inj_unsigned in H11; [ exact H11 | pose proof (land65535_range v); rep_lia | rep_lia ]. }
          forward.
          Exists (h1 ++ [(n, 0, true, v)]) fs1 hs2.
          entailer!.
          replace (bus * 256 + dev * 8 + (fn + 1)) with (n + 1) by (unfold n; lia).
          apply run_id_absent; auto. }
        assert (A: Z.land v 65535 <> 65535) by (intro E; apply H11; rewrite zext16_land, E; reflexivity).
        clear H11.
        forward_if.
        { (* the snapshot is full: CAPACITY_EXCEEDED *)
          assert (Full: Zlength fs1 = CAPACITY).
          { destruct H10 as [_ [L _]]. pose proof (Zlength_nonneg fs1).
            apply repr_inj_unsigned in H11; [ exact H11 | rep_lia | rep_lia ]. }
          forward_call (result, rold, 2, bus_of n, dev_of n, fn_of n, 0); try (unfold u8_ok; rep_lia).
          forward.
          Exists (h1 ++ [(n, 0, true, v)]) 2 n 0 (@nil found) hs2.
          rewrite (maybe_read_nonnull Dev read), (maybe_at_nonnull Tsh t_snapshot _ snapshot) by auto.
          rewrite Zlength_nil, app_nil_l. unfold result_at.
          entailer!.
          split; [ destruct H10; auto | apply (scan_id_full h1 n fs1); auto ]. }
        assert (Lt: Zlength fs1 < 16).
        { destruct H10 as [_ [L _]]. assert (Zlength fs1 <> 16) by (intro E; apply H11; rewrite E; reflexivity). lia. }
        clear H11.
        forward.
        assert_PROP (field_compatible t_snapshot [] snapshot) as FC by entailer!.
        rewrite (header_addr snapshot (Zlength fs1)) by (auto; pose proof (Zlength_nonneg fs1); lia).
        rewrite (snap_split Tsh 0 hs2 snapshot (Zlength fs1)) by (try (destruct H10; auto); pose proof (Zlength_nonneg fs1); lia).
        sep_apply (data_at_data_at_ Tsh t_header (Znth (Zlength fs1) hs2) (hdr_ptr snapshot (Zlength fs1))).
        forward. forward. forward. forward. forward.
        rewrite (zext8_small (bus_of n)) by (rewrite Bn; lia).
        rewrite (zext8_small (dev_of n)) by (rewrite Dn; lia).
        rewrite (zext8_small (fn_of n)) by (rewrite Fn; lia).
        match goal with |- context [upd_Znth 0 ?L (Vint (Int.repr v))] =>
          replace (upd_Znth 0 L (Vint (Int.repr v))) with (wvals [v]) by reflexivity end.
        sep_apply (data_at_data_at_ Tsh tuint (Vint (Int.repr v)) v_identity).
        assert (Hk: 0 <= (Zlength fs1) < 16) by (pose proof (Zlength_nonneg fs1); lia).
        assert (Hhs: Zlength hs2 = 16) by (destruct H10; auto).
        forward_for_simple_bound 16 (EX w: Z, EX h: list answer, EX ws: list Z,
          PROP (run start h = Some (Go ((n + 1)%Z, wstate w, (n, ws) :: fs1)); Zlength ws = w)
          LOCAL (temp _header (hdr_ptr snapshot (Zlength fs1)); temp _f (Vint (Int.repr (fn_of n)));
                 temp _d (Vint (Int.repr (dev_of n))); temp _b (Vint (Int.repr (bus_of n)));
                 temp _function (Vint (Int.repr fn)); temp _device (Vint (Int.repr dev));
                 temp _bus (Vint (Int.repr bus)); temp _count (Vint (Int.repr (Zlength fs1)));
                 lvar _value tuint v_value; lvar _identity tuint v_identity;
                 temp _read read; temp _context ctx; temp _snapshot snapshot; temp _result result)
          SEP (Dev ctx h; data_at_ Tsh tuint v_identity; data_at_ Tsh tuint v_value; func_ptr' (read_spec Dev) read;
               field_at Tsh t_snapshot [StructField _count] (Vint (Int.repr 0)) snapshot;
               data_at Tsh (tarray t_header (Zlength fs1)) (sublist 0 (Zlength fs1) hs2) (field_address t_snapshot [StructField _headers] snapshot);
               data_at Tsh t_header (stage n ws) (hdr_ptr snapshot (Zlength fs1));
               data_at Tsh (tarray t_header (16 - (Zlength fs1 + 1))) (sublist (Zlength fs1 + 1) 16 hs2) (hdr_ptr snapshot (Zlength fs1 + 1));
               maybe_at Tsh t_result rold result))%assert.
        { Exists (h1 ++ [(n, 0, true, v)]) [v]. entailer!.
          apply run_id_found; auto; unfold CAPACITY; lia. }
        { cbv beta. rename i into w. Intros h2 ws.
          match goal with Hl: Zlength ws = w |- _ => subst w end.
          forward.
          rewrite offset_cast by lia.
          assert (NRw: next_read h2 = Some (n, 4 * Zlength ws)) by (eapply next_read_w; [ eassumption | unfold WORDS; lia ]).
          forward_call (ctx, h2, n, 4 * Zlength ws, v_value).
          Intros vret. destruct vret as [ok x]. cbn [fst snd] in *.
          destruct ok.
          2: { (* a dword read failed: READ_FAILED *)
            forward_if; [ | dead ].
            forward_call (result, rold, 1, bus_of n, dev_of n, fn_of n, 4 * Zlength ws); try (unfold u8_ok; rep_lia).
            forward.
            Exists (h2 ++ [(n, 4 * Zlength ws, false, x)]) 1 n (4 * Zlength ws) (@nil found) (upd_Znth (Zlength fs1) hs2 (stage n ws)).
            rewrite (maybe_read_nonnull Dev read), (maybe_at_nonnull Tsh t_snapshot _ snapshot) by auto.
            rewrite Zlength_nil, app_nil_l. unfold result_at.
            rewrite <- (snap_join Tsh 0 hs2 snapshot (Zlength fs1) (stage n ws)) by auto.
            entailer!.
            split; [ rewrite Zlength_upd_Znth; auto | ].
            apply (scan_w_fail h2 n (Zlength ws) ws fs1); [ assumption | unfold WORDS; lia ]. }
          forward_if; [ dead | ].
          forward.
          unfold stage.
          forward.
          rewrite wvals_upd by (unfold WORDS; lia).
          Exists (h2 ++ [(n, 4 * Zlength ws, true, x)]) (ws ++ [x]).
          entailer!.
          split; [ apply run_w_ok; [ assumption | unfold WORDS; lia ] | ].
          rewrite Zlength_app, Zlength_cons, Zlength_nil; lia. }
        Intros h2 ws.
        forward.
        Exists h2 ((n, ws) :: fs1) (upd_Znth (Zlength fs1) hs2 (header_val (n, ws))).
        rewrite <- (snap_join Tsh 0 hs2 snapshot (Zlength fs1) (header_val (n, ws))) by auto.
        match goal with Hl: Zlength ws = 16 |- _ => rewrite (stage_full n ws Hl) end.
        rewrite Zlength_cons.
        entailer!.
        split; [ | apply pub_ok_cons; auto ].
        replace (bus * 256 + dev * 8 + (fn + 1)) with (n + 1) by (unfold n; lia).
        match goal with Hr: run start h2 = _ |- _ => rewrite wstate_16 in Hr; exact Hr end. }
      Intros h1 fs1 hs2. Exists h1 fs1 hs2. entailer!.
      replace (bus * 256 + (dev + 1) * 8) with (bus * 256 + dev * 8 + 8) by lia. auto. }
    Intros h0 fs0 hs1. Exists h0 fs0 hs1. entailer!. replace ((i + 1) * 256) with (i * 256 + 32 * 8) by lia. auto. }
  Intros h fs hs.
  change (256 * 256) with FUNCTIONS in H4.
  forward.
  forward_call (result, rold, 0, 0, 0, 0, 0); try (unfold u8_ok; rep_lia).
  forward.
  Exists h 0 0 0 (rev fs) (sublist (Zlength fs) 16 hs).
  rewrite Zlength_rev. rewrite <- (pub_ok_split fs hs H5).
  unfold result_at. destruct bdf_zero as (B0 & D0 & F0). rewrite B0, D0, F0.
  rewrite (maybe_read_nonnull Dev read), (maybe_at_nonnull Tsh t_snapshot _ snapshot) by auto.
  entailer!.
  split; [ | apply scan_done; auto ].
  destruct H5 as [L [L2 _]]. rewrite Zlength_sublist by (pose proof (Zlength_nonneg fs); lia). unfold CAPACITY; lia.
Qed.
