(* Law image_exact: what the parts of the proof of read_image share: struct law_image as its fields, the model's
   decode stage by stage (each check of the law's read_image against the clause of decode), and the context and
   join assertion of read_image's body. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import LeanosDeviceProgramImage.harness.image_exact.code.
Require Import LeanosDeviceProgramImage.proof.Defs.
Require Import LeanosDeviceProgramImage.proof.LawProg LeanosDeviceProgramImage.proof.LawSpecs
  LeanosDeviceProgramImage.proof.LawLib LeanosDeviceProgramImage.proof.LawSplit
  LeanosDeviceProgramImage.proof.LawFacts.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

(* struct law_image as its fields. *)
Definition li_fields (sh: share) (r: val) (st hl: val) (tv: target_t) (pv: policy_t) (nv blv sst: val) : mpred :=
  (field_at sh t_law_image (DOT _status) st r * field_at sh t_law_image (DOT _header_len) hl r *
   field_at sh t_law_image (DOT _t) tv r * field_at sh t_law_image (DOT _pol) pv r *
   field_at sh t_law_image (DOT _n) nv r * field_at sh t_law_image (DOT _blob_len) blv r *
   field_at sh t_law_image (DOT _start_status) sst r * spacer sh 380 384 r)%logic.

Lemma li_split: forall sh r st hl tv pv nv blv sst,
  data_at sh t_law_image (law_image_val st hl tv pv nv blv sst) r = li_fields sh r st hl tv pv nv blv sst.
Proof.
  intros. unfold law_image_val, li_fields. unfold_data_at (data_at _ _ _ r). rewrite !sepcon_assoc. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* decode, stage by stage.                                                *)
(* ---------------------------------------------------------------------- *)

Section Decode.
Variable bs: list Z.

Definition hd_ok : Prop := 16 <= Zlength bs /\ le32 bs 0 = MAGIC.

Lemma dec_bad_head: Zlength bs < 16 \/ le32 bs 0 <> MAGIC -> decode bs = None.
Proof.
  intros H. unfold decode; cbv zeta. destruct H as [H|H].
  - rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity.
  - rewrite (proj2 (Z.eqb_neq _ _) H). destruct (Zlength bs <? 16); reflexivity.
Qed.

Lemma dec_head: hd_ok -> ((Zlength bs <? 16) || negb (le32 bs 0 =? MAGIC))%bool = false.
Proof. intros [A B]. rewrite (proj2 (Z.ltb_ge _ _) A), B, Z.eqb_refl. reflexivity. Qed.

Lemma dec_v1: hd_ok -> le32 bs 4 = 1 -> decode bs = Some (bcm_target, no_policy, 16).
Proof. intros H V. unfold decode; cbv zeta. rewrite dec_head by auto. rewrite V. reflexivity. Qed.

Lemma dec_bad_version: hd_ok -> le32 bs 4 <> 1 -> le32 bs 4 <> 2 -> le32 bs 4 <> 3 -> decode bs = None.
Proof.
  intros H V1 V2 V3. unfold decode; cbv zeta. rewrite dec_head by auto.
  rewrite (proj2 (Z.eqb_neq _ _) V1), (proj2 (Z.eqb_neq _ _) V2), (proj2 (Z.eqb_neq _ _) V3). reflexivity.
Qed.

Lemma dec_short23: hd_ok -> (le32 bs 4 = 2 \/ le32 bs 4 = 3) ->
  Zlength bs < (if le32 bs 4 =? 2 then 32 else 68) -> decode bs = None.
Proof.
  intros H [V|V] L; unfold decode; cbv zeta; rewrite dec_head by auto; rewrite V in *; simpl in L |- *;
    rewrite (proj2 (Z.ltb_lt _ _) L); reflexivity.
Qed.

Definition v23_ok : Prop :=
  hd_ok /\ (le32 bs 4 = 2 \/ le32 bs 4 = 3) /\ (if le32 bs 4 =? 2 then 32 else 68) <= Zlength bs.

Lemma dec_v23_pre: v23_ok -> forall (k: option (target * policy * Z)),
  (if (Zlength bs <? 16) || negb (le32 bs 0 =? MAGIC) then None else
   if le32 bs 4 =? 1 then Some (bcm_target, no_policy, 16) else
   if negb ((le32 bs 4 =? 2) || (le32 bs 4 =? 3)) then None else
   if Zlength bs <? (if le32 bs 4 =? 3 then 68 else 32) then None else k)%bool = k.
Proof.
  intros (H & [V|V] & L) k; rewrite dec_head by auto; rewrite V in *; simpl in L |- *;
    rewrite (proj2 (Z.ltb_ge _ _) L); reflexivity.
Qed.

Lemma dec_bad_target: v23_ok -> target_ok bs = false -> decode bs = None.
Proof. intros H T. unfold decode; cbv zeta. rewrite dec_v23_pre by auto. rewrite T. reflexivity. Qed.

Lemma dec_v2: v23_ok -> target_ok bs = true -> le32 bs 4 = 2 -> decode bs = Some (target_of bs, no_policy, 32).
Proof. intros H T V. unfold decode; cbv zeta. rewrite dec_v23_pre by auto. rewrite T, V. reflexivity. Qed.

Definition v3_ok : Prop := v23_ok /\ target_ok bs = true /\ le32 bs 4 = 3.

Lemma dec_v3_pre: v3_ok -> forall k,
  (if (Zlength bs <? 16) || negb (le32 bs 0 =? MAGIC) then None else
   if le32 bs 4 =? 1 then Some (bcm_target, no_policy, 16) else
   if negb ((le32 bs 4 =? 2) || (le32 bs 4 =? 3)) then None else
   if Zlength bs <? (if le32 bs 4 =? 3 then 68 else 32) then None else
   if negb (target_ok bs) then None else
   if le32 bs 4 =? 2 then Some (target_of bs, no_policy, 32) else k)%bool = k.
Proof. intros (H & T & V) k. rewrite dec_v23_pre by auto. rewrite T, V. reflexivity. Qed.

Lemma dec_v3_bad: v3_ok ->
  (3 < le32 bs 32 \/ le32 bs 36 < le32 bs 24 \/ 8 < le32 bs 64 \/ Zlength bs < 68 + 4 * le32 bs 64) ->
  decode bs = None.
Proof.
  intros H C. unfold decode; cbv zeta. rewrite dec_v3_pre by auto. unfold MAX_SINKS. simpl tg_window.
  destruct C as [C|[C|[C|C]]]; apply Z.ltb_lt in C; rewrite C; rewrite ?orb_true_r; reflexivity.
Qed.

Definition v3s_ok : Prop :=
  v3_ok /\ le32 bs 32 <= 3 /\ le32 bs 24 <= le32 bs 36 /\ le32 bs 64 <= 8 /\ 68 + 4 * le32 bs 64 <= Zlength bs.

Lemma dec_v3s_pre: v3s_ok -> forall k,
  (if (Zlength bs <? 16) || negb (le32 bs 0 =? MAGIC) then None else
   if le32 bs 4 =? 1 then Some (bcm_target, no_policy, 16) else
   if negb ((le32 bs 4 =? 2) || (le32 bs 4 =? 3)) then None else
   if Zlength bs <? (if le32 bs 4 =? 3 then 68 else 32) then None else
   if negb (target_ok bs) then None else
   if le32 bs 4 =? 2 then Some (target_of bs, no_policy, 32) else
   if (3 <? le32 bs 32) || (le32 bs 36 <? tg_window (target_of bs)) || (MAX_SINKS <? le32 bs 64) ||
      (Zlength bs <? 68 + 4 * le32 bs 64) then None else k)%bool = k.
Proof.
  intros (H & C1 & C2 & C3 & C4) k. rewrite dec_v3_pre by auto. unfold MAX_SINKS. simpl tg_window.
  rewrite (proj2 (Z.ltb_ge _ _) C1), (proj2 (Z.ltb_ge _ _) C2), (proj2 (Z.ltb_ge _ _) C3),
    (proj2 (Z.ltb_ge _ _) C4). reflexivity.
Qed.

Lemma dec_v3_nodesc: v3s_ok -> Z.land (le32 bs 32) 2 = 0 ->
  decode bs = Some (target_of bs, v3_policy bs (le32 bs 64) 0 nil, 68 + 4 * le32 bs 64).
Proof. intros H F. unfold decode; cbv zeta. rewrite dec_v3s_pre by auto. rewrite F. reflexivity. Qed.

Lemma dec_v3_shortA: v3s_ok -> Z.land (le32 bs 32) 2 <> 0 -> Zlength bs < 68 + 4 * le32 bs 64 + 4 ->
  decode bs = None.
Proof.
  intros H F L. unfold decode; cbv zeta. rewrite dec_v3s_pre by auto.
  rewrite (proj2 (Z.eqb_neq _ _) F), (proj2 (Z.ltb_lt _ _) L). reflexivity.
Qed.

Lemma dec_v3_badD: v3s_ok -> Z.land (le32 bs 32) 2 <> 0 -> 68 + 4 * le32 bs 64 + 4 <= Zlength bs ->
  (16 < le32 bs (68 + 4 * le32 bs 64) \/
   Zlength bs < 68 + 4 * le32 bs 64 + 4 + 16 * le32 bs (68 + 4 * le32 bs 64)) ->
  decode bs = None.
Proof.
  intros H F L C. unfold decode; cbv zeta. rewrite dec_v3s_pre by auto.
  rewrite (proj2 (Z.eqb_neq _ _) F), (proj2 (Z.ltb_ge _ _) L). unfold MAX_DESCS.
  destruct C as [C|C]; apply Z.ltb_lt in C; rewrite C; rewrite ?orb_true_r; reflexivity.
Qed.

Lemma dec_v3_descs: v3s_ok -> Z.land (le32 bs 32) 2 <> 0 -> 68 + 4 * le32 bs 64 + 4 <= Zlength bs ->
  le32 bs (68 + 4 * le32 bs 64) <= 16 ->
  68 + 4 * le32 bs 64 + 4 + 16 * le32 bs (68 + 4 * le32 bs 64) <= Zlength bs ->
  decode bs =
  if forallb desc_ok (descs_at bs (68 + 4 * le32 bs 64) (le32 bs (68 + 4 * le32 bs 64))) then
    Some (target_of bs,
          v3_policy bs (le32 bs 64) (le32 bs (68 + 4 * le32 bs 64))
            (descs_at bs (68 + 4 * le32 bs 64) (le32 bs (68 + 4 * le32 bs 64))),
          68 + 4 * le32 bs 64 + 4 + 16 * le32 bs (68 + 4 * le32 bs 64))
  else None.
Proof.
  intros H F L C1 C2. unfold decode; cbv zeta. rewrite dec_v3s_pre by auto.
  rewrite (proj2 (Z.eqb_neq _ _) F), (proj2 (Z.ltb_ge _ _) L). unfold MAX_DESCS.
  rewrite (proj2 (Z.ltb_ge _ _) C1), (proj2 (Z.ltb_ge _ _) C2). simpl orb.
  destruct (forallb desc_ok _); reflexivity.
Qed.

End Decode.

(* ---------------------------------------------------------------------- *)
(* The law's forms of the target checks.                                  *)
(* ---------------------------------------------------------------------- *)

Lemma bar_law: forall b, ((b <? 16) || (36 <? b) || negb (b mod 4 =? 0))%bool = negb (bar_ok b).
Proof.
  intros. unfold bar_ok. destruct (Z.ltb_spec b 16), (Z.leb_spec 16 b), (Z.ltb_spec 36 b), (Z.leb_spec b 36);
    simpl; try lia; reflexivity.
Qed.

Lemma window_law: forall w, ((w =? 0) || (65536 <? w) || negb (w mod 512 =? 0))%bool = negb (window_ok w).
Proof.
  intros. unfold window_ok. destruct (w =? 0), (Z.ltb_spec 65536 w), (Z.leb_spec w 65536); simpl; try lia; reflexivity.
Qed.

Lemma target_ok_eq: forall bs,
  target_ok bs = (bdf_ok (le32 bs 16) && bar_ok (bar_of (le32 bs 28)) && window_ok (le32 bs 24))%bool.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* The law's struct law_image during read_image: its policy at r + 32 as  *)
(* the policy's fields.                                                   *)
(* ---------------------------------------------------------------------- *)

Definition ri_rep (sh: share) (r: val) (st hl: val) (tv: target_t) (a1 a2 a3 a4 a5 a6 a7 a8: val) (ss: list val)
    (dc: val) (ds: list desc_t) (nv blv sst: val) : mpred :=
  (field_at sh t_law_image (DOT _status) st r * field_at sh t_law_image (DOT _header_len) hl r *
   field_at sh t_law_image (DOT _t) tv r * pol_fields sh (offset_val 32 r) a1 a2 a3 a4 a5 a6 a7 a8 ss dc ds *
   field_at sh t_law_image (DOT _n) nv r * field_at sh t_law_image (DOT _blob_len) blv r *
   field_at sh t_law_image (DOT _start_status) sst r * spacer sh 380 384 r)%logic.

Lemma pol_addr: forall r, field_compatible t_law_image nil r -> field_address t_law_image (DOT _pol) r = offset_val 32 r.
Proof.
  intros r FC. unfold field_address. rewrite if_true; [ reflexivity | ].
  apply field_compatible_cons; split; [ | exact FC ]. simpl. unfold in_members; simpl. auto 20.
Qed.

Lemma ri_rep_eq: forall sh r st hl tv a1 a2 a3 a4 a5 a6 a7 a8 ss dc ds nv blv sst,
  field_compatible t_law_image nil r ->
  data_at sh t_law_image (law_image_val st hl tv (pol_vals a1 a2 a3 a4 a5 a6 a7 a8 ss dc ds) nv blv sst) r =
  ri_rep sh r st hl tv a1 a2 a3 a4 a5 a6 a7 a8 ss dc ds nv blv sst.
Proof.
  intros. rewrite li_split. unfold li_fields, ri_rep.
  rewrite (field_at_data_at sh t_law_image (DOT _pol)), pol_addr by auto.
  change (nested_field_type t_law_image (DOT _pol)) with t_policy. rewrite pol_split. reflexivity.
Qed.

Definition li_default : law_image_t :=
  law_image_val Vundef Vundef (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, Vundef)))))
    (pol_vals Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef (Zrepeat Vundef 8) Vundef (Zrepeat udesc 16))
    Vundef Vundef Vundef.

Lemma li_default_eq: default_val t_law_image = li_default.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* read_image's context, its return assertion and its join point.         *)
(* ---------------------------------------------------------------------- *)

Definition ri_delta : tycontext := func_tycontext f_read_image Vlaw Glaw nil.

Definition ri_post (sh: share) (b: val) (bs: list Z) (wsh: share) (r: val) : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tvoid
      (EX (st hl : val) (tv : target_t) (pv : policy_t) (nv blv sst : val),
       PROP (reading_ok bs st hl tv pv nv blv sst)
       RETURN ( ) SEP (data_at sh (tarray tuchar (Zlength bs)) (bytes_val bs) b;
                       data_at wsh t_law_image (law_image_val st hl tv pv nv blv sst) r))%argsassert)
    (stackframe_of f_read_image).

(* After the target and policy are read: the decoded target, the decoded policy's scalars and entries, the header
   length in at. *)
Definition ri_join (sh: share) (b: val) (bs: list Z) (wsh: share) (r: val) : environ -> mpred :=
  (EX T: target, EX P: policy, EX H: Z, EX ss: list val, EX ds: list desc_t,
   PROP (decode bs = Some (T, P, H))
   LOCAL (temp _at (Vint (Int.repr H)); temp _b b; temp _len (Vint (Int.repr (Zlength bs))); temp _r r)
   SEP (data_at sh (tarray tuchar (Zlength bs)) (bytes_val bs) b;
        ri_rep wsh r (Vint (Int.repr 2)) Vundef (target_val T)
          (Vint (Int.repr (pl_present P))) (Vint (Int.repr (pl_dma P))) (Vint (Int.repr (pl_window P)))
          (Vlong (Int64.repr (pl_cfg_read P))) (Vlong (Int64.repr (pl_cfg_write P)))
          (Vint (Int.repr (pl_cmd_clear P))) (Vint (Int.repr (pl_cmd_set P))) (Vint (Int.repr (pl_sink_count P)))
          (words_val (pl_sinks P) ++ ss) (Vint (Int.repr (pl_desc_count P))) (map desc_val (pl_descs P) ++ ds)
          Vundef Vundef (Vint (Int.repr 2))))%assert.

(* The parts of read_image's body. *)
Definition ri_body : statement := ltac:(let b := eval cbv delta [f_read_image] beta iota zeta in (fn_body f_read_image)
  in exact b).

Definition s_v23 : statement := ltac:(
  let b := eval cbv delta [ri_body] in ri_body in
  match b with
  | context [Sifthenelse (Ebinop Oeq (Etempvar _version tuint) (Econst_int (Int.repr 1) tint) tint) _ ?e] => exact e
  end).

Definition s_v3 : statement := ltac:(
  let b := eval cbv delta [s_v23] in s_v23 in
  match b with
  | context [Sifthenelse (Ebinop Oeq (Etempvar _version tuint) (Econst_int (Int.repr 3) tint) tint) ?e Sskip] =>
      exact e
  end).

Definition s_desc : statement := ltac:(
  let b := eval cbv delta [s_v3] in s_v3 in
  match b with
  | context [Sifthenelse (Ebinop Oand (Etempvar _flags tuint) (Econst_int (Int.repr 2) tuint) tuint) ?e Sskip] =>
      exact e
  end).

Definition s_tail : statement := ltac:(
  let b := eval cbv delta [ri_body] in ri_body in
  match b with
  | context [Ssequence (Sifthenelse (Ebinop Oeq (Etempvar _version tuint) (Econst_int (Int.repr 1) tint) tint) _ _)
               ?t] => exact t
  end).

(* Enter a part: VST's canonical form of the goal, as start_function leaves it. *)
Ltac start_part :=
  unfold ri_delta, ri_post, s_v23, s_v3, s_desc, s_tail;
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

(* A return of read_image with the law's state as it is. *)
Ltac ri_exists :=
  let st := lazymatch goal with |- context [field_at _ t_law_image (DOT _status) ?v _] => v end in
  let hl := lazymatch goal with |- context [field_at _ t_law_image (DOT _header_len) ?v _] => v end in
  let tv := lazymatch goal with |- context [field_at _ t_law_image (DOT _t) ?v _] => v end in
  let nv := lazymatch goal with |- context [field_at _ t_law_image (DOT _n) ?v _] => v end in
  let blv := lazymatch goal with |- context [field_at _ t_law_image (DOT _blob_len) ?v _] => v end in
  let sst := lazymatch goal with |- context [field_at _ t_law_image (DOT _start_status) ?v _] => v end in
  let a1 := lazymatch goal with |- context [field_at _ t_policy (DOT _present) ?v _] => v end in
  let a2 := lazymatch goal with |- context [field_at _ t_policy (DOT _dma) ?v _] => v end in
  let a3 := lazymatch goal with |- context [field_at _ t_policy (DOT _window) ?v _] => v end in
  let a4 := lazymatch goal with |- context [field_at _ t_policy (DOT _cfg_read) ?v _] => v end in
  let a5 := lazymatch goal with |- context [field_at _ t_policy (DOT _cfg_write) ?v _] => v end in
  let a6 := lazymatch goal with |- context [field_at _ t_policy (DOT _cmd_clear) ?v _] => v end in
  let a7 := lazymatch goal with |- context [field_at _ t_policy (DOT _cmd_set) ?v _] => v end in
  let a8 := lazymatch goal with |- context [field_at _ t_policy (DOT _sink_count) ?v _] => v end in
  let ss := lazymatch goal with |- context [field_at _ t_policy (DOT _sinks) ?v _] => v end in
  let dc := lazymatch goal with |- context [field_at _ t_policy (DOT _desc_count) ?v _] => v end in
  let ds := lazymatch goal with |- context [field_at _ t_policy (DOT _descs) ?v _] => v end in
  Exists st hl tv (pol_vals a1 a2 a3 a4 a5 a6 a7 a8 ss dc ds) nv blv sst.

Ltac ri_ret FCr :=
  forward; ri_exists; rewrite ri_rep_eq by exact FCr; unfold ri_rep, pol_fields; entailer!.

Definition z32 : val := Vint (Int.repr 0).
Definition z64 : val := Vlong (Int64.repr 0).
Definition tg_undef : target_t := (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, Vundef))))).

(* The state at the branch on the version (not 1): status and start status BAD, the policy's scalars 0, at 16. *)
Definition ri_pre23 (sh: share) (b: val) (bs: list Z) (wsh: share) (r: val) : environ -> mpred :=
  (PROP (hd_ok bs; le32 bs 4 <> 1)
   LOCAL (temp _at (Vint (Int.repr 16)); temp _version (Vint (Int.repr (le32 bs 4))); temp _p (offset_val 32 r);
          temp _b b; temp _len (Vint (Int.repr (Zlength bs))); temp _r r)
   SEP (data_at sh (tarray tuchar (Zlength bs)) (bytes_val bs) b;
        ri_rep wsh r (Vint (Int.repr 2)) Vundef tg_undef z32 z32 z32 z64 z64 z32 z32 z32 (Zrepeat Vundef 8) z32
          (Zrepeat udesc 16) Vundef Vundef (Vint (Int.repr 2))))%assert.

(* Split boolean facts of comparisons into facts of Z. *)
Ltac bsplit :=
  repeat match goal with
  | H: (_ || _)%bool = false |- _ => apply orb_false_iff in H as [? ?]
  | H: (_ && _)%bool = true |- _ => apply andb_true_iff in H as [? ?]
  | H: negb _ = true |- _ => apply negb_true_iff in H
  | H: negb _ = false |- _ => apply negb_false_iff in H
  | H: (_ <? _) = false |- _ => apply Z.ltb_ge in H
  | H: (_ <? _) = true |- _ => apply Z.ltb_lt in H
  | H: (_ <=? _) = false |- _ => apply Z.leb_gt in H
  | H: (_ <=? _) = true |- _ => apply Z.leb_le in H
  | H: (_ =? _) = false |- _ => apply Z.eqb_neq in H
  | H: (_ =? _) = true |- _ => apply Z.eqb_eq in H
  end.
