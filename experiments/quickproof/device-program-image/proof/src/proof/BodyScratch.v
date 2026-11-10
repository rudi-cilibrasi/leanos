(* The end of wifi_start: S = wifi_scratch, the loop zeroing its 262144 bytes, return 0.  SCRATCH stays folded
   in the loop invariant (Zrepeat over a sublist split), and Zrepeat is opaque here, so that nothing computes a
   list of 262144 values. *)
Require Import VST.floyd.proofauto.
Require Import LeanosDeviceProgramImage.device_program.code.
Require Import LeanosDeviceProgramImage.proof.Specs.
#[local] Existing Instance Specs.CS.
Local Open Scope Z_scope.

Definition Delta_st : tycontext := func_tycontext f_wifi_start Vprog Gprog nil.

Definition Post_st gv sh image bs wsh vmp V0 ssh sc : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tint
       (EX (vv : vm_t) (sc' : list val),
        PROP (start_post image bs V0 sc vv sc')
        RETURN (Vint (Int.repr (start_status bs)))
        SEP (data_at sh (tarray tuchar (Zlength bs)) (bytes_val bs) image;
             data_at wsh t_vm vv vmp;
             data_at ssh t_scratch sc' (gv _wifi_scratch)))%argsassert)
    (stackframe_of f_wifi_start).

Definition st_body : statement :=
  ltac:(let b := eval cbv delta [f_wifi_start] beta iota zeta in (fn_body f_wifi_start) in exact b).

Definition s_scratch : statement := ltac:(
  let b := eval cbv delta [st_body] in st_body in
  match b with context [Ssequence (Sset _S ?x) ?rest] => exact (Ssequence (Sset _S x) rest) end).

Lemma zero_step: forall (z: val) (l: list val) i n, 0 <= i < n -> Zlength l = n ->
  upd_Znth i (Zrepeat z i ++ sublist i n l) z = Zrepeat z (i + 1) ++ sublist (i + 1) n l.
Proof.
  intros z l i n I L.
  rewrite upd_Znth_app2 by (rewrite Zlength_Zrepeat, Zlength_sublist; lia).
  rewrite Zlength_Zrepeat by lia. rewrite Z.sub_diag.
  rewrite (sublist_split i (i + 1) n l) by lia. rewrite (sublist_one i (i + 1) l) by lia.
  cbn [app]. rewrite upd_Znth0.
  rewrite <- Zrepeat_app by lia. rewrite <- app_assoc. reflexivity.
Qed.

Lemma zero_ext_0: Int.zero_ext 8 (Int.repr 0) = Int.repr 0.
Proof. apply Int.same_if_eq. reflexivity. Qed.

#[local] Opaque Zrepeat SCRATCH.

Lemma st_scratch {Espec: OracleKind} gv sh image bs wsh vmp V0 ssh sc vh T P H N B:
  readable_share sh -> writable_share wsh -> writable_share ssh -> Zlength sc = SCRATCH ->
  start bs = Some (T, P, H, N, B) ->
  forall Delta R c, Delta = Delta_st -> R = Post_st gv sh image bs wsh vmp V0 ssh sc -> c = s_scratch ->
  semax Delta
    (PROP ()
     LOCAL (lvar _hdr tuint vh; gvars gv)
     SEP (data_at sh (tarray tuchar (Zlength bs)) (bytes_val bs) image;
          data_at wsh t_vm (vm_val (started image V0 T P H N B)) vmp;
          data_at ssh t_scratch sc (gv _wifi_scratch);
          data_at Tsh tuint (Vint (Int.repr H)) vh))
    c R.
Proof.
  intros SH WSH SSH LS ST Delta R c -> -> ->.
  unfold s_scratch, Post_st, Delta_st.
  simplify_func_tycontext. abbreviate_semax.
  assert (SC: SCRATCH = 262144) by reflexivity.
  forward.
  forward_for_simple_bound 262144 (EX i: Z,
    PROP ()
    LOCAL (temp _S (gv _wifi_scratch); lvar _hdr tuint vh; gvars gv)
    SEP (data_at sh (tarray tuchar (Zlength bs)) (bytes_val bs) image;
         data_at wsh t_vm (vm_val (started image V0 T P H N B)) vmp;
         data_at ssh t_scratch (Zrepeat (Vint (Int.repr 0)) i ++ sublist i SCRATCH sc) (gv _wifi_scratch);
         data_at Tsh tuint (Vint (Int.repr H)) vh))%assert.
  { rewrite Zrepeat_0, app_nil_l, (sublist_same 0 SCRATCH sc) by lia. entailer!. }
  { unfold t_scratch. forward. rewrite zero_ext_0. rewrite zero_step by lia. entailer!. }
  rewrite <- SC. rewrite sublist_nil, app_nil_r.
  forward.
  Exists (vm_val (started image V0 T P H N B)) (Zrepeat (Vint (Int.repr 0)) SCRATCH).
  entailer!.
  unfold start_post, start_status. rewrite ST. split; [ split; reflexivity | reflexivity ].
Qed.
