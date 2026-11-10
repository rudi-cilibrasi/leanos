(* Law image_exact: the specifications of the harness's own functions (harness/image_exact.c), under the compspecs
   of the law's whole program (LawProg.LCS), and the context Glaw of every body proof of the harness.

   The law's reading of an image (read_image, into law.want) is stated with the model of Defs.v: its status and
   start status are header_status and start_status, and on a good image its target, header length, N, B and
   policy are the decoded ones (the policy's entries past its counts are whatever the object held).  Each helper
   that performs checks (check_policy, header_case, start_case, admission_case) has a precondition that makes
   all its qp_asserts true and a postcondition that returns its objects; main passes the law's state and the
   image to them. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import LeanosDeviceProgramImage.harness.image_exact.code.
Require Import LeanosDeviceProgramImage.proof.Defs.
Require LeanosDeviceProgramImage.device_program.code.
Require LeanosDeviceProgramImage.proof.Specs.
Require Import LeanosDeviceProgramImage.proof.LawProg.
Module S := LeanosDeviceProgramImage.proof.Specs.
Local Open Scope Z_scope.

#[export] Existing Instance LawProg.LCS.

(* ---------------------------------------------------------------------- *)
(* The law's state.                                                       *)
(* ---------------------------------------------------------------------- *)

Definition t_law := Tstruct _law__1 noattr.
Definition t_law_image := Tstruct _law_image noattr.
Definition t_target := Tstruct _wifi_target noattr.
Definition t_desc := Tstruct _wifi_desc noattr.
Definition t_policy := Tstruct _wifi_policy noattr.
Definition t_vm := Tstruct _wifi_vm noattr.

Definition _wifi_scratch : ident := LeanosDeviceProgramImage.device_program.code._wifi_scratch.

(* struct law_image: status, header_len, t, pol, n, blob_len, start_status; struct law: call, length, copy, want. *)
Definition law_image_t : Type := (val * (val * (target_t * (policy_t * (val * (val * val))))))%type.
Definition law_t : Type := (val * (val * (val * law_image_t)))%type.

Definition law_image_val (st hl: val) (tv: target_t) (pv: policy_t) (nv blv sst: val) : law_image_t :=
  (st, (hl, (tv, (pv, (nv, (blv, sst)))))).

(* The policy object pv holds P's scalars and P's declared entries first; its entries past the counts are any. *)
Definition pol_declares (P: policy) (pv: policy_t) : Prop :=
  exists (ss: list val) (ds: list desc_t),
    pv = policy_rep (pl_present P) (pl_dma P) (pl_window P) (pl_cfg_read P) (pl_cfg_write P)
           (pl_cmd_clear P) (pl_cmd_set P) (pl_sink_count P) (words_val (pl_sinks P) ++ ss)
           (pl_desc_count P) (map desc_val (pl_descs P) ++ ds).

(* The law's reading of the image bs (struct law_image, field by field). *)
Definition reading_ok (bs: list Z) (st hl: val) (tv: target_t) (pv: policy_t) (nv blv sst: val) : Prop :=
  st = Vint (Int.repr (header_status bs)) /\ sst = Vint (Int.repr (start_status bs)) /\
  match decode bs with
  | Some (T, P, H) =>
      hl = Vint (Int.repr H) /\ tv = target_val T /\ pol_declares P pv /\
      nv = Vint (Int.repr (le32 bs 8)) /\ blv = Vint (Int.repr (le32 bs 12))
  | None => True
  end.

(* The law's state as header_case and start_case read it: the image's length and the law's reading of it. *)
Definition law_reads (bs: list Z) (lv: law_t) : Prop :=
  match lv with
  | (_, (len, (_, (st, (hl, (tv, (pv, (nv, (blv, sst))))))))) =>
      len = Vint (Int.repr (Zlength bs)) /\ reading_ok bs st hl tv pv nv blv sst
  end.

(* ---------------------------------------------------------------------- *)
(* The law's reading of an image.                                         *)
(* ---------------------------------------------------------------------- *)

Definition word_at_spec :=
  DECLARE _word_at
  WITH sh: share, b: val, bs: list Z, k: Z
  PRE [ tptr tuchar, tuint ]
    PROP (readable_share sh; 0 <= k; k + 4 <= Zlength bs; image_ok bs)
    PARAMS (b; Vint (Int.repr k))
    SEP (data_at sh (tarray tuchar (Zlength bs)) (bytes_val bs) b)
  POST [ tuint ]
    PROP ()
    RETURN (Vint (Int.repr (le32 bs k)))
    SEP (data_at sh (tarray tuchar (Zlength bs)) (bytes_val bs) b).

Definition read_image_spec :=
  DECLARE _read_image
  WITH sh: share, b: val, bs: list Z, wsh: share, r: val
  PRE [ tptr tuchar, tuint, tptr t_law_image ]
    PROP (readable_share sh; writable_share wsh; image_ok bs)
    PARAMS (b; Vint (Int.repr (Zlength bs)); r)
    SEP (data_at sh (tarray tuchar (Zlength bs)) (bytes_val bs) b; data_at_ wsh t_law_image r)
  POST [ tvoid ]
    EX st: val, EX hl: val, EX tv: target_t, EX pv: policy_t, EX nv: val, EX blv: val, EX sst: val,
    PROP (reading_ok bs st hl tv pv nv blv sst)
    RETURN ()
    SEP (data_at sh (tarray tuchar (Zlength bs)) (bytes_val bs) b;
         data_at wsh t_law_image (law_image_val st hl tv pv nv blv sst) r).

(* ---------------------------------------------------------------------- *)
(* Choices and copies.                                                    *)
(* ---------------------------------------------------------------------- *)

Definition any_target_spec :=
  DECLARE _any_target
  WITH sh: share, t: val
  PRE [ tptr t_target ]
    PROP (writable_share sh) PARAMS (t) SEP (data_at_ sh t_target t)
  POST [ tvoid ]
    EX T: target, PROP (target_wf T) RETURN () SEP (data_at sh t_target (target_val T) t).

Definition any_u64_spec :=
  DECLARE _any_u64
  WITH u: unit
  PRE [ ] PROP () PARAMS () SEP ()
  POST [ tulong ] EX x: Z, PROP (u64_ok x) RETURN (Vlong (Int64.repr x)) SEP ().

(* any_policy(p, bounded): any policy; with bounded (1), at most 8 sinks and 16 descriptors. *)
Definition any_policy_spec :=
  DECLARE _any_policy
  WITH sh: share, p: val, bounded: bool
  PRE [ tptr t_policy, tint ]
    PROP (writable_share sh) PARAMS (p; Vint (Int.repr (Z.b2z bounded))) SEP (data_at_ sh t_policy p)
  POST [ tvoid ]
    EX P: policy,
    PROP (policy_wf P; if bounded then policy_bounded P else True)
    RETURN ()
    SEP (data_at sh t_policy (policy_val P) p).

Definition copy_policy_spec :=
  DECLARE _copy_policy
  WITH dsh: share, d: val, ssh: share, s: val, P: policy
  PRE [ tptr t_policy, tptr t_policy ]
    PROP (writable_share dsh; readable_share ssh; policy_wf P)
    PARAMS (d; s)
    SEP (data_at_ dsh t_policy d; data_at ssh t_policy (policy_val P) s)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at dsh t_policy (policy_val P) d; data_at ssh t_policy (policy_val P) s).

(* ---------------------------------------------------------------------- *)
(* Comparisons.                                                           *)
(* ---------------------------------------------------------------------- *)

Definition same_target_spec :=
  DECLARE _same_target
  WITH ash: share, a: val, A: target, bsh: share, b: val, B: target
  PRE [ tptr t_target, tptr t_target ]
    PROP (readable_share ash; readable_share bsh; target_wf A; target_wf B)
    PARAMS (a; b)
    SEP (data_at ash t_target (target_val A) a; data_at bsh t_target (target_val B) b)
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (Z.b2z (target_eqb A B))))
    SEP (data_at ash t_target (target_val A) a; data_at bsh t_target (target_val B) b).

Definition same_desc_spec :=
  DECLARE _same_desc
  WITH ash: share, a: val, A: desc, bsh: share, b: val, B: desc
  PRE [ tptr t_desc, tptr t_desc ]
    PROP (readable_share ash; readable_share bsh; desc_wf A; desc_wf B)
    PARAMS (a; b)
    SEP (data_at ash t_desc (desc_val A) a; data_at bsh t_desc (desc_val B) b)
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (Z.b2z (desc_eqb A B))))
    SEP (data_at ash t_desc (desc_val A) a; data_at bsh t_desc (desc_val B) b).

(* check_policy(got, want, prior) for a parsed policy: got is the decoded policy P laid over the prior object Q,
   want the law's reading of P, prior Q.  Every check of check_policy holds. *)
Definition check_policy_spec :=
  DECLARE _check_policy
  WITH gsh: share, g: val, wsh: share, w: val, wv: policy_t, qsh: share, q: val, P: policy, Q: policy
  PRE [ tptr t_policy, tptr t_policy, tptr t_policy ]
    PROP (readable_share gsh; readable_share wsh; readable_share qsh; decoded_wf P; policy_wf Q;
          pol_declares P wv)
    PARAMS (g; w; q)
    SEP (data_at gsh t_policy (policy_val (store P Q)) g; data_at wsh t_policy wv w;
         data_at qsh t_policy (policy_val Q) q)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at gsh t_policy (policy_val (store P Q)) g; data_at wsh t_policy wv w;
         data_at qsh t_policy (policy_val Q) q).

Definition declares_sink_spec :=
  DECLARE _declares_sink
  WITH psh: share, pp: val, P: policy, off: Z
  PRE [ tptr t_policy, tuint ]
    PROP (readable_share psh; policy_wf P; pl_sink_count P <= MAX_SINKS; u32_ok off)
    PARAMS (pp; Vint (Int.repr off))
    SEP (data_at psh t_policy (policy_val P) pp)
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (Z.b2z (is_sink P off))))
    SEP (data_at psh t_policy (policy_val P) pp).

Definition declares_desc_spec :=
  DECLARE _declares_desc
  WITH psh: share, pp: val, P: policy, dsh: share, dp: val, d: desc
  PRE [ tptr t_policy, tptr t_desc ]
    PROP (readable_share psh; readable_share dsh; policy_wf P; pl_desc_count P <= MAX_DESCS; desc_wf d)
    PARAMS (pp; dp)
    SEP (data_at psh t_policy (policy_val P) pp; data_at dsh t_desc (desc_val d) dp)
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (Z.b2z (has_desc P d))))
    SEP (data_at psh t_policy (policy_val P) pp; data_at dsh t_desc (desc_val d) dp).

(* The law's within: the same Within(p, max) as the C's. *)
Definition law_within_spec :=
  DECLARE _within
  WITH psh: share, pp: val, P: policy, msh: share, mp: val, M: policy
  PRE [ tptr t_policy, tptr t_policy ]
    PROP (readable_share psh; readable_share msh; policy_bounded P; policy_bounded M)
    PARAMS (pp; mp)
    SEP (data_at psh t_policy (policy_val P) pp; data_at msh t_policy (policy_val M) mp)
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (Z.b2z (within P M))))
    SEP (data_at psh t_policy (policy_val P) pp; data_at msh t_policy (policy_val M) mp).

(* ---------------------------------------------------------------------- *)
(* The cases.                                                             *)
(* ---------------------------------------------------------------------- *)

(* header_case(m, image): the law holds the image's length and its reading; every check holds. *)
Definition header_case_spec :=
  DECLARE _header_case
  WITH msh: share, m: val, lv: law_t, ish: share, image: val, bs: list Z
  PRE [ tptr t_law, tptr tuchar ]
    PROP (readable_share msh; readable_share ish; image_ok bs; law_reads bs lv)
    PARAMS (m; image)
    SEP (data_at msh t_law lv m; data_at ish (tarray tuchar (Zlength bs)) (bytes_val bs) image)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at msh t_law lv m; data_at ish (tarray tuchar (Zlength bs)) (bytes_val bs) image).

(* start_case(m, image): as header_case, with the scratch (any contents) and the allocator; it allocates three
   objects it never frees (TT). *)
Definition start_case_spec :=
  DECLARE _start_case
  WITH gv: globals, msh: share, m: val, lv: law_t, ish: share, image: val, bs: list Z
  PRE [ tptr t_law, tptr tuchar ]
    PROP (readable_share msh; readable_share ish; image_ok bs; law_reads bs lv)
    PARAMS (m; image)
    GLOBALS (gv)
    SEP (mem_mgr gv; data_at msh t_law lv m; data_at ish (tarray tuchar (Zlength bs)) (bytes_val bs) image;
         data_at_ Ews (tarray tuchar SCRATCH) (gv _wifi_scratch))
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (mem_mgr gv; data_at msh t_law lv m; data_at ish (tarray tuchar (Zlength bs)) (bytes_val bs) image;
         TT).

(* admission_case(m): the law's call is 2, 3 or 4; every check holds. *)
Definition admission_case_spec :=
  DECLARE _admission_case
  WITH msh: share, m: val, lv: law_t, c: Z
  PRE [ tptr t_law ]
    PROP (readable_share msh; 2 <= c <= 4; fst lv = Vint (Int.repr c))
    PARAMS (m)
    SEP (data_at msh t_law lv m)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at msh t_law lv m).

(* ---------------------------------------------------------------------- *)
(* The contexts.                                                          *)
(* ---------------------------------------------------------------------- *)

(* The program's global variables: the law's state and the unit's scratch. *)
Definition Vlaw : varspecs := [(_wifi_scratch, tarray tuchar SCRATCH); (_law, t_law)].

(* The context of every body proof of the harness, main included: the harness's functions, the wrappers it calls
   and the environment functions it calls. *)
Definition Glaw : funspecs :=
  [word_at_spec; read_image_spec; any_target_spec; any_u64_spec; any_policy_spec; copy_policy_spec;
   same_target_spec; same_desc_spec; check_policy_spec; declares_sink_spec; declares_desc_spec;
   law_within_spec; header_case_spec; start_case_spec; admission_case_spec;
   S.dp_header_spec; S.dp_start_spec; S.dp_within_spec; S.dp_service_spec; S.dp_source_spec;
   S.dp_scratch_spec;
   nondet_u8_spec; nondet_u32_spec; nondet_bytes_spec; gp_assert_spec; (_quickproof_malloc, malloc_spec')].
