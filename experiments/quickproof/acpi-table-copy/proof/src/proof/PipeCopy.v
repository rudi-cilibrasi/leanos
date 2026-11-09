(* The body of acpi_copy_sdt: the address check, the header copy, the length checks, the body copy (to the first
   `length` bytes of the destination, split out of it for the call), the stream loop over the chunks with its five
   stream calls and their checks, the write-back of the exposed bytes (the bytes the chunk was composed of), and the
   record written on success; against `begin_sdt` and `step` one answer at a time. *)
Require Import VST.floyd.proofauto.
Require Import LeanosAcpi.acpi.code.
Require Import LeanosAcpi.proof.Defs.
Require Import LeanosAcpi.proof.AcpiSpecs.
Require Import LeanosAcpi.proof.InternalSpecs.
Require Import LeanosAcpi.proof.PipeLemmas.
Require Import LeanosAcpi.proof.PipeModel.
Require Import LeanosAcpi.proof.PipeFast.
#[local] Ltac simplify_remove_localdef_temp ::= fast_remove_localdef_temp.
#[local] Existing Instance AcpiSpecs.CS.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[local] Opaque run step sdt_copied root_copied table_copied sublist little transition validate decode_addresses.

Ltac gen_hist R n := match type of R with run _ _ ?t = _ => revert R; generalize t; intros n R end.

Ltac tfail ST :=
  match goal with S: run _ _ _ = Some (if negb (transition ?l ?c ?cu ?b ?nn ?t =? S_OK) then _ else _) |- _ =>
    let T := fresh "T" in
    assert (T: transition l c cu b nn t = ST) by tsolve;
    match type of S with run ?x ?p ?hs = _ =>
      match goal with |- semax _ _ _ (normal_ret_assert _) => idtac | _ => idtac end;
      let S6 := fresh "S6" in
      match type of S with
      | context [Return _ None ?m'] =>
        assert (S6: run x p hs = Some (Return ST None m')) by (rewrite S, T; reflexivity)
      end
    end
  end.

Ltac fix_status st :=
  let E := fresh in
  assert (E: (st =? S_OK) = false) by reflexivity; rewrite ?E; clear E; rewrite ?if_false_eq;
  let SO := fresh "SO" in assert (SO: status_ok st) by reflexivity.

Lemma body_acpi_copy_sdt (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_acpi_copy_sdt (copy_sdt_spec Ora).
Proof.
  start_function.
  rename H1 into Hrun0. rename H2 into A64. rename H3 into DF0.
  assert (DF: dest_fits x g) by (destruct g; simpl; auto).
  pose proof (capacity_range x g H DF) as CAP.
  pose proof (cursor_range x g H DF) as CUR.
  unfold u64_ok in A64.
  forward_if.
  { (* the address is wider than 32 bits *)
    u64h.
    assert (R: run x (begin_sdt x g m) [] = Some (Return S_SDT_ADDRESS_WIDTH None m))
      by (rewrite begin_sdt_fail by (unfold MAX_U32; lia); apply run_nil).
    pose proof (copy_frame_refl g m) as F.
    forward.
    Exists (@nil answer) S_SDT_ADDRESS_WIDTH m 0 0. fix_status S_SDT_ADDRESS_WIDTH.
    rewrite app_nil_r. entailer!; try discriminate. }
  u64h.
  assert (BG: begin_sdt x g m = Go (Copying g CHeader) m) by (apply begin_sdt_go; unfold MAX_U32; lia).
  rewrite BG in Hrun0.
  assert (Hrun0': run x (start x) h = Some (begin_sdt x g m)) by (rewrite BG; auto).
  rewrite <- (holds_header x h _ m H0 Hrun0).
  forward_call (gv, ctx, pl, sh, x, h, address_of x g, DHeader, HEADER_BYTES).
  { rewrite (next_call_go _ _ _ _ Hrun0). reflexivity. }
  Intros vret. destruct vret as [ret hb]. cbn [fst snd] in *.
  set (hs1 := [(Copy (address_of x g) DHeader HEADER_BYTES, Copied ret hb)]).
  set (m1 := write m DHeader hb).
  assert (R1: run x (begin_sdt x g m) hs1 = Some (step x (Copying g CHeader) m (Copied ret hb))).
  { rewrite BG. apply run_one. apply fits_copy. auto. }
  rewrite step_header in R1. fold m1 in R1.
  change (dest_ptr pl DHeader) with (p_header pl).
  assert (M1: mem_ok x m1) by (apply mem_ok_header; auto).
  assert (F1: copy_frame g m m1) by (apply copy_frame_header; destruct H0; lia).
  assert (HB: m_header m1 = hb) by reflexivity.
  replace (bytes_val hb) with (bytes_val (m_header m1)) by (rewrite HB; reflexivity).
  rewrite <- (region_header m hb g (capacity_of x g)). fold m1.
  clearbody m1 hs1.
  forward_if.
  { (* the header copy failed *)
    apply ret_zero in H5; auto. rewrite (proj2 (Z.eqb_eq ret 0) H5) in R1.
    forward. Exists hs1 S_PHYSICAL m1 0 0. fix_status S_PHYSICAL. entailer!; try discriminate. }
  apply ret_nonzero in H5. rewrite (proj2 (Z.eqb_neq ret 0) H5) in R1.
  assert (L36: Zlength (m_header m1) = 36) by (rewrite HB; auto).
  assert (BH: Forall byte_ok (m_header m1)) by (rewrite HB; auto).
  do 4 (forward; [ entailer!; unfold HEADER_BYTES; lia
                 | entailer!; rewrite Znth_bytes_val by lia; apply tc_byte, byte_at; auto; lia
                 | rewrite Znth_bytes_val by lia ]).
  forward.
  rewrite length32 by (auto; lia). rewrite HB.
  set (len := little (sublist 4 8 hb)) in *.
  assert (LU: u32_ok len) by (apply length32_u32; auto; unfold HEADER_BYTES in *; lia).
  clearbody len.
  replace (bytes_val hb) with (bytes_val (m_header m1)) by (rewrite HB; reflexivity).
  unfold u32_ok in LU.
  forward_if (temp _t'2 (Vint (bint ((len <? HEADER_BYTES) || (MAX_SDT_BYTES <? len))))).
  { forward. entailer!. rewrite (proj2 (Z.ltb_lt len HEADER_BYTES)) by (unfold HEADER_BYTES; lia). reflexivity. }
  { forward. entailer!. rewrite (proj2 (Z.ltb_ge len HEADER_BYTES)) by (unfold HEADER_BYTES; lia).
    rewrite zlt_ltb, bool2val_bint. reflexivity. }
  forward_if (temp _t'3 (Vint (bint ((len <? HEADER_BYTES) || (MAX_SDT_BYTES <? len) || (capacity_of x g <? len))))).
  { forward. entailer!. bfix. match goal with H: (_ || _) = true |- _ => rewrite H end. reflexivity. }
  { forward. entailer!. bfix. match goal with H: (_ || _) = false |- _ => rewrite H end.
    rewrite zlt_ltb, bool2val_bint. reflexivity. }
  forward_if.
  { (* the length is out of bounds *)
    bfix. match goal with H: (_ || _ || _) = true |- _ => rewrite H in R1 end.
    forward. Exists hs1 S_SDT_LENGTH m1 0 0. fix_status S_SDT_LENGTH. entailer!; try discriminate. }
  bfix. match goal with H: (_ || _ || _) = false |- _ => rename H into LB end.
  rewrite LB in R1.
  apply orb_false_iff in LB as [LB LC]. apply orb_false_iff in LB as [LA LB].
  apply Z.ltb_ge in LA. apply Z.ltb_ge in LB. apply Z.ltb_ge in LC. unfold HEADER_BYTES, MAX_SDT_BYTES in LA, LB.
  (* the body copy, to the first len bytes of the destination *)
  assert (Lreg: Zlength (region m1 (dest_of g) (capacity_of x g)) = capacity_of x g) by (apply Zlength_region; auto).
  assert_PROP (field_compatible (tarray tuchar (capacity_of x g)) [] (dest_ptr pl (dest_of g))) as FCd by entailer!.
  rewrite (split2_bytes sh (region m1 (dest_of g) (capacity_of x g)) (capacity_of x g) len) by (auto; lia).
  Intros.
  rewrite (region_prefix x m1 g len) by (auto; lia).
  rewrite <- (holds_at x h (begin_sdt x g m) hs1 _ _ (dest_of g) len Hrun0' R1).
  forward_call (gv, ctx, pl, sh, x, h ++ hs1, address_of x g, dest_of g, len).
  { rewrite (next_call_at _ _ _ _ _ _ Hrun0' R1). reflexivity. }
  Intros vret. destruct vret as [ret2 bs]. cbn [fst snd] in *.
  rewrite <- app_assoc.
  set (hs2 := hs1 ++ [(Copy (address_of x g) (dest_of g) len, Copied ret2 bs)]).
  assert (R2: run x (begin_sdt x g m) hs2 = Some (step x (Copying g (CBody len)) m1 (Copied ret2 bs))).
  { apply (run_snoc' x _ hs1 _ _ _ R1). apply fits_copy. auto. }
  rewrite step_body in R2.
  set (m2 := write m1 (dest_of g) bs) in R2.
  assert (M2: mem_ok x m2) by (apply mem_ok_dest; auto; lia).
  assert (F2: copy_frame g m m2) by (apply copy_frame_write with x; auto; lia).
  assert (H2h: m_header m2 = m_header m1) by apply m_header_write_dest.
  match goal with H: Zlength bs = len |- _ => rename H into Lbs end.
  rewrite <- Lbs.
  sep_apply (split2_region sh x m1 g bs (dest_ptr pl (dest_of g)) M1 DF ltac:(lia) FCd).
  fold m2. rewrite <- H2h.
  assert (BR: Forall byte_ok (region m2 (dest_of g) (capacity_of x g))) by (apply Forall_region with x; auto).
  assert (LR: Zlength (region m2 (dest_of g) (capacity_of x g)) = capacity_of x g) by (apply Zlength_region; auto).
  assert (RBz: forall i, 0 <= i < len -> Znth i (region m2 (dest_of g) (capacity_of x g)) = Znth i bs).
  { intros. apply Znth_prefix with len; [ rewrite <- Lbs; apply region_body; auto; lia | lia | rewrite LR; lia ]. }
  rewrite Lbs.
  change (h ++ hs1 ++ [(Copy (address_of x g) (dest_of g) len, Copied ret2 bs)]) with (h ++ hs2).
  clearbody m2 hs2. clear HB.
  deadvars!.
  forward_if.
  { (* the body copy failed *)
    match goal with H: Int.repr ret2 = Int.zero |- _ => apply ret_zero in H; [ rename H into Z0 | auto ] end.
    rewrite (proj2 (Z.eqb_eq ret2 0) Z0) in R2.
    forward. Exists hs2 S_PHYSICAL m2 0 0. fix_status S_PHYSICAL. entailer!; try discriminate. }
  match goal with H: Int.repr ret2 <> Int.zero |- _ => apply ret_nonzero in H; rename H into Z0 end.
  rewrite (proj2 (Z.eqb_neq ret2 0) Z0) in R2.
  forward. forward.
  assert (BS: Forall byte_ok bs) by auto.
  assert (Lbs': len <= Zlength bs <= len) by lia. clear Lbs.
  forward_while (EX hs: list answer, EX byte: Z, EX cursor: Z,
    PROP (run x (begin_sdt x g m) hs =
            Some (if byte <? len then Go (Copying g (CChunk len bs cursor byte nil)) m2
                  else sdt_copied x g len cursor m2);
          0 <= byte <= len; u64_ok cursor)
    LOCAL (temp _byte_offset (Vlong (Int64.repr byte)); temp _next_copy_offset (Vlong (Int64.repr cursor));
           temp _length (Vint (Int.repr len));
           gvars gv; temp _physical_address (Vlong (Int64.repr (address_of x g)));
           temp _destination (dest_ptr pl (dest_of g)); temp _copied cp)
    SEP (data_at sh (tarray tuchar (capacity_of x g)) (bytes_val (region m2 (dest_of g) (capacity_of x g)))
           (dest_ptr pl (dest_of g));
         Ora gv ctx pl x (h ++ hs); data_at sh (tarray tuchar HEADER_BYTES) (bytes_val (m_header m2)) (p_header pl);
         func_ptr' (copy_spec Ora) copy; data_at csh t_sdt cold cp))%assert.
  { Exists hs2 0 (cursor_of g). rewrite (proj2 (Z.ltb_lt 0 len)) by lia. entailer!. unfold u64_ok; rep_lia. }
  { entailer!. }
  { (* one chunk *)
    match goal with H: run _ (begin_sdt _ _ _) hs = _ |- _ => rename H into HR end.
    rewrite (proj2 (Z.ltb_lt byte len) HRE) in HR.
    assert (Nr: 1 <= chunk_bytes len byte <= 8) by (apply chunk_bytes_range; lia).
    assert (Nle: byte + chunk_bytes len byte <= len) by (unfold chunk_bytes; lia).
    forward.
    rewrite Int64.unsigned_repr, sub_repr by rep_lia.
    forward_if (temp _t'5 (Vint (Int.repr (chunk_bytes len byte)))).
    { forward. entailer!. unfold chunk_bytes. f_equal. f_equal. lia. }
    { forward. entailer!. unfold chunk_bytes. f_equal. f_equal. lia. }
    forward. forward.
    set (n := chunk_bytes len byte) in *.
    assert (FCd2: field_compatible (tarray tuchar (capacity_of x g)) [] (dest_ptr pl (dest_of g))) by auto.
    forward_for_simple_bound n (EX k: Z,
      PROP ()
      LOCAL (temp _physical_chunk (Vlong (Int64.repr (little (sublist byte (byte + k) bs))));
             temp _chunk_bytes (Vint (Int.repr n));
             temp _byte_offset (Vlong (Int64.repr byte)); temp _next_copy_offset (Vlong (Int64.repr cursor));
             temp _length (Vint (Int.repr len)); gvars gv;
             temp _physical_address (Vlong (Int64.repr (address_of x g)));
             temp _destination (dest_ptr pl (dest_of g)); temp _copied cp)
      SEP (data_at sh (tarray tuchar (capacity_of x g)) (bytes_val (region m2 (dest_of g) (capacity_of x g)))
             (dest_ptr pl (dest_of g));
           Ora gv ctx pl x (h ++ hs); data_at sh (tarray tuchar HEADER_BYTES) (bytes_val (m_header m2)) (p_header pl);
           func_ptr' (copy_spec Ora) copy; data_at csh t_sdt cold cp))%assert.
    { entailer!. rewrite sublist_nil, little_nil. reflexivity. }
    { forward.
      { entailer!. rewrite Znth_bytes_val by lia. apply tc_byte, byte_at; auto; lia. }
      rewrite Znth_bytes_val, RBz by lia.
      forward.
      { entailer!. change (Int.unsigned Int64.iwordsize') with 64. lia. }
      rewrite compose64_at by (auto; lia).
      entailer!. }
    set (chunk := little (sublist byte (byte + n) bs)).
    assert (CU: u64_ok chunk) by (apply little_u64; [ apply Forall_sublist; auto | rewrite Zlength_sublist by lia; lia ]).
    forward.
    rewrite terminal_word2 by (try reflexivity; lia).
    forward_call (gv, ctx, pl, x, h ++ hs, cursor, address_of x g, byte, address_of x g, len, byte, chunk,
                  terminal len byte, 1).
    { rewrite (next_call_at _ _ _ _ _ _ Hrun0' HR). reflexivity. }
    Intros v1. rewrite <- app_assoc.
    assert (S1: run x (begin_sdt x g m) (hs ++ [(Stream cursor (address_of x g) byte (address_of x g) len byte chunk
                    (terminal len byte) 1, Word v1)]) =
                  Some (Go (Copying g (CChunk len bs cursor byte [v1])) m2))
      by (apply stream_more with (cur := []); auto; reflexivity).
    clear HR. gen_hist S1 hq1.
    forward_call (gv, ctx, pl, x, h ++ hq1, cursor, address_of x g, byte, address_of x g, len, byte, chunk,
                  terminal len byte, 2).
    { rewrite (next_call_at _ _ _ _ _ _ Hrun0' S1). reflexivity. }
    Intros v2. rewrite <- app_assoc.
    assert (S2: run x (begin_sdt x g m) (hq1 ++ [(Stream cursor (address_of x g) byte (address_of x g) len byte chunk
                    (terminal len byte) 2, Word v2)]) =
                  Some (Go (Copying g (CChunk len bs cursor byte [v1; v2])) m2))
      by (apply stream_more with (cur := [v1]); auto; reflexivity).
    clear S1. gen_hist S2 hq2.
    forward_call (gv, ctx, pl, x, h ++ hq2, cursor, address_of x g, byte, address_of x g, len, byte, chunk,
                  terminal len byte, 4).
    { rewrite (next_call_at _ _ _ _ _ _ Hrun0' S2). reflexivity. }
    Intros v3. rewrite <- app_assoc.
    assert (S3: run x (begin_sdt x g m) (hq2 ++ [(Stream cursor (address_of x g) byte (address_of x g) len byte chunk
                    (terminal len byte) 4, Word v3)]) =
                  Some (Go (Copying g (CChunk len bs cursor byte [v1; v2; v3])) m2))
      by (apply stream_more with (cur := [v1; v2]); auto; reflexivity).
    clear S2. gen_hist S3 hq3.
    forward_call (gv, ctx, pl, x, h ++ hq3, cursor, address_of x g, byte, address_of x g, len, byte, chunk,
                  terminal len byte, 5).
    { rewrite (next_call_at _ _ _ _ _ _ Hrun0' S3). reflexivity. }
    Intros v4. rewrite <- app_assoc.
    assert (S4: run x (begin_sdt x g m) (hq3 ++ [(Stream cursor (address_of x g) byte (address_of x g) len byte chunk
                    (terminal len byte) 5, Word v4)]) =
                  Some (Go (Copying g (CChunk len bs cursor byte [v1; v2; v3; v4])) m2))
      by (apply stream_more with (cur := [v1; v2; v3]); auto; reflexivity).
    clear S3. gen_hist S4 hq4.
    forward_call (gv, ctx, pl, x, h ++ hq4, cursor, address_of x g, byte, address_of x g, len, byte, chunk,
                  terminal len byte, 6).
    { rewrite (next_call_at _ _ _ _ _ _ Hrun0' S4). reflexivity. }
    Intros v5. rewrite <- app_assoc.
    assert (S5: run x (begin_sdt x g m) (hq4 ++ [(Stream cursor (address_of x g) byte (address_of x g) len byte chunk
                    (terminal len byte) 6, Word v5)]) =
                  Some (step x (Copying g (CChunk len bs cursor byte [v1; v2; v3; v4])) m2 (Word v5)))
      by (apply stream_last; auto; reflexivity).
    clear S4. gen_hist S5 hq5. rewrite step_chunk_last in S5. fold n in S5. fold chunk in S5.
    assert (S5': run x (begin_sdt x g m) hq5 =
      Some (if negb (transition [v1; v2; v3; v4; v5] chunk cursor byte n (terminal len byte) =? S_OK)
            then Return (transition [v1; v2; v3; v4; v5] chunk cursor byte n (terminal len byte)) None m2
            else if v3 <? len then Go (Copying g (CChunk len bs (if terminal len byte =? 0 then cursor else v4) v3 [])) m2
            else sdt_copied x g len (if terminal len byte =? 0 then cursor else v4) m2)) by (rewrite S5; reflexivity).
    clear S5. unfold vl.
    pose proof (terminal_01 len byte) as T01.
    forward_if.
    { w64.
      tfail S_BUDGET.
      forward.
      Exists hq5 S_BUDGET m2 0 0. fix_status S_BUDGET. entailer!; try discriminate. }
    w64.
    forward_if.
    { w64.
      tfail S_LENGTH.
      forward.
      Exists hq5 S_LENGTH m2 0 0. fix_status S_LENGTH. entailer!; try discriminate. }
    w64.
    forward_if.
    { w64.
      tfail S_ADDRESS.
      forward.
      Exists hq5 S_ADDRESS m2 0 0. fix_status S_ADDRESS. entailer!; try discriminate. }
    w64.
    forward_if.
    { w64.
      tfail S_OFFSET.
      forward.
      Exists hq5 S_OFFSET m2 0 0. fix_status S_OFFSET. entailer!; try discriminate. }
    w64.
    forward_if.
    { w64.
      tfail S_TERMINAL.
      forward.
      Exists hq5 S_TERMINAL m2 0 0. fix_status S_TERMINAL. entailer!; try discriminate. }
    w64.
    forward_if.
    { w64.
      tfail S_ERROR.
      forward.
      Exists hq5 S_ERROR m2 0 0. fix_status S_ERROR. entailer!; try discriminate. }
    w64.
    forward_if.
    { w64.
      tfail S_STATUS.
      forward.
      Exists hq5 S_STATUS m2 0 0. fix_status S_STATUS. entailer!; try discriminate. }
    w64.
    forward_if.
    { match goal with H: context [Int64.add (Int64.repr byte) _] |- _ => rewrite Int.unsigned_repr, add64_repr in H by rep_lia end. w64.
      tfail S_NEXT_BYTE.
      forward.
      Exists hq5 S_NEXT_BYTE m2 0 0. fix_status S_NEXT_BYTE. entailer!; try discriminate. }
    match goal with H: context [Int64.add (Int64.repr byte) _] |- _ => rewrite Int.unsigned_repr, add64_repr in H by rep_lia end. w64.
    forward_if.
    { w64.
      tfail S_EXPOSED.
      forward.
      Exists hq5 S_EXPOSED m2 0 0. fix_status S_EXPOSED. entailer!; try discriminate. }
    w64.
    assert (TB: 0 <= terminal len byte <= 1) by (destruct T01; lia).
    forward_if (temp _t'11 (Vint (bint ((terminal len byte =? 0) && negb (v4 =? cursor))))).
    { w64. forward. entailer!. rewrite cmpu_ne64 by auto. rewrite bool2val_bint.
      match goal with H: terminal len byte = 0 |- _ => rewrite H end. reflexivity. }
    { w64. forward. entailer!. rewrite (proj2 (Z.eqb_neq (terminal len byte) 0)) by auto. reflexivity. }
    forward_if.
    { bfix. match goal with H: (_ && _) = true |- _ => apply andb_prop in H as [Ta Tb] end.
      apply Z.eqb_eq in Ta. apply negb_true_iff, Z.eqb_neq in Tb.
      tfail S_PARTIAL_CURSOR.
      forward.
      Exists hq5 S_PARTIAL_CURSOR m2 0 0. fix_status S_PARTIAL_CURSOR. entailer!; try discriminate. }
    bfix. match goal with H: (_ && _) = false |- _ => rename H into PC end.
    forward_if (temp _t'12 (Vint (bint (negb (terminal len byte =? 0) && (v4 <=? cursor))))).
    { w64. forward. entailer!. rewrite cmpu_le64 by auto. rewrite bool2val_bint.
      rewrite (proj2 (Z.eqb_neq (terminal len byte) 0)) by auto. reflexivity. }
    { w64. forward. entailer!. match goal with H: terminal len byte = 0 |- _ => rewrite H end. reflexivity. }
    forward_if.
    { bfix. match goal with H: (_ && _) = true |- _ => apply andb_prop in H as [Ta Tb] end.
      apply negb_true_iff, Z.eqb_neq in Ta. apply Z.leb_le in Tb.
      assert (Ta': terminal len byte = 1) by lia.
      tfail S_FINAL_CURSOR.
      forward.
      Exists hq5 S_FINAL_CURSOR m2 0 0. fix_status S_FINAL_CURSOR. entailer!; try discriminate. }
    bfix. match goal with H: (_ && _) = false |- _ => rename H into FC end.
    assert (TOK: transition [v1; v2; v3; v4; v5] chunk cursor byte n (terminal len byte) = S_OK).
    { destruct T01 as [T0 | T1].
      - rewrite T0 in PC. cbn [Z.eqb andb] in PC. apply negb_false_iff, Z.eqb_eq in PC. tsolve.
      - rewrite T1 in FC. cbn [Z.eqb andb negb] in FC. apply Z.leb_gt in FC. tsolve. }
    set (cursor' := if terminal len byte =? 0 then cursor else v4).
    assert (S7: run x (begin_sdt x g m) hq5 =
              Some (if v3 <? len then Go (Copying g (CChunk len bs cursor' v3 [])) m2 else sdt_copied x g len cursor' m2))
      by (rewrite S5', TOK; reflexivity).
    clear S5'.
    assert (Lsub: Zlength (sublist byte (byte + n) bs) = n) by (rewrite Zlength_sublist by lia; lia).
    assert (Fsub: Forall byte_ok (sublist byte (byte + n) bs)) by (apply Forall_sublist; auto).
    forward_for_simple_bound n (EX k: Z,
      PROP ()
      LOCAL (temp _exposed (Vlong (Int64.repr v5)); temp _emitted_copy_offset (Vlong (Int64.repr v4));
             temp _next_byte (Vlong (Int64.repr v3)); temp _terminal (Vlong (Int64.repr (terminal len byte)));
             temp _chunk_bytes (Vint (Int.repr n));
             temp _byte_offset (Vlong (Int64.repr byte)); temp _next_copy_offset (Vlong (Int64.repr cursor));
             temp _length (Vint (Int.repr len)); gvars gv;
             temp _physical_address (Vlong (Int64.repr (address_of x g)));
             temp _destination (dest_ptr pl (dest_of g)); temp _copied cp)
      SEP (Ora gv ctx pl x (h ++ hq5);
           data_at sh (tarray tuchar (capacity_of x g)) (bytes_val (region m2 (dest_of g) (capacity_of x g)))
             (dest_ptr pl (dest_of g));
           data_at sh (tarray tuchar HEADER_BYTES) (bytes_val (m_header m2)) (p_header pl);
           func_ptr' (copy_spec Ora) copy; data_at csh t_sdt cold cp))%assert.
    { entailer!. }
    { forward.
      { entailer!. change (Int.unsigned Int64.iwordsize') with 64. lia. }
      { entailer!.
        match goal with |- context [Int64.Z_mod_modulus (Z.shiftr (Int64.Z_mod_modulus ?c) _)] =>
          replace c with (little (sublist byte (byte + chunk_bytes len byte) bs)) by reflexivity end.
        rewrite (wb_byte (sublist byte (byte + chunk_bytes len byte) bs) i Fsub) by (rewrite Lsub; lia).
        rewrite upd_Znth_same by (rewrite ?Zlength_bytes_val; try lia;
          rewrite Znth_bytes_val, RBz, Znth_sublist by lia; do 3 f_equal; lia).
        apply derives_refl. } }
    forward.
    forward_if (temp _next_copy_offset (Vlong (Int64.repr cursor'))).
    { w64. forward. entailer!. unfold cursor'. rewrite (proj2 (Z.eqb_neq _ _)) by auto. reflexivity. }
    { w64. forward. entailer!. unfold cursor'. match goal with H: terminal len byte = 0 |- _ => rewrite H end.
      reflexivity. }
    assert (CU': u64_ok cursor') by (unfold cursor'; destruct (_ =? _); auto).
    Exists (hq5, v3, cursor'). entailer!; try lia; try apply derives_refl. }
  (* the stream ended: the record *)
  match goal with H: run _ (begin_sdt _ _ _) hs = _ |- _ => rename H into HR end.
  rewrite (proj2 (Z.ltb_ge byte len)) in HR by lia.
  assert (IP: isptr (dest_ptr pl (dest_of g))) by (eapply field_compatible_isptr; eauto).
  forward. forward. forward. forward.
  forward.
  Exists hs S_OK m2 len cursor.
  assert (SO: status_ok S_OK) by reflexivity.
  rewrite Z.eqb_refl. cbv iota.
  unfold sdt_val. cbn [s_address s_offset s_length s_next]. rewrite dest_base by auto.
  unfold vi. rewrite repr_mod32.
  entailer!.
  rewrite Int64.Z_mod_modulus_eq, Z.mod_small by (unfold u64_ok in *; rep_lia). apply derives_refl.
Qed.
