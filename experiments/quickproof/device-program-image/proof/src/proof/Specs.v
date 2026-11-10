(* VST specifications of every function of the unit patch/device_program_unit.c (hardware/wifi/wifi-exec.h and its
   six wrappers), under the unit's compspecs.  Each wrapper has the specification of the function it forwards to
   (one funspec, two names); dp_scratch returns the address of the static wifi_scratch.

   The specifications are stated against the model of Defs.v and are what the law's checks need (src/proof/NOTES.md
   maps each to the law comment):
   - the image is an array of exactly its length, read with any readable share and returned unchanged;
   - wifi_image_header: the status, and on 0 exactly the decoded target, header length and policy (the policy's
     entries past its counts keep the prior object's values); on BAD any values;
   - wifi_start: on 0 the whole executor state (code and blob as pointers into the image object), the stack
     unchanged and the scratch zero; on BAD every field but target and policy, and the scratch, unchanged;
   - the admission functions: the model's boolean as 0 or 1, for policies of at most 8 sinks and 16 descriptors.
   Every output object takes its own writable share (wifi_start passes the target and policy of its executor
   state together with its own local header length). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require LeanosDeviceProgramImage.units.DeviceProgram.
Require Import LeanosDeviceProgramImage.device_program.code.
Require Export LeanosDeviceProgramImage.proof.Defs.
Local Open Scope Z_scope.

#[export] Instance CS : compspecs := LeanosDeviceProgramImage.units.DeviceProgram.CS.
Definition Vprog : varspecs. mk_varspecs LeanosDeviceProgramImage.device_program.code.prog. Defined.

(* ---------------------------------------------------------------------- *)
(* Types.                                                                 *)
(* ---------------------------------------------------------------------- *)

Definition t_target := Tstruct _wifi_target noattr.
Definition t_desc := Tstruct _wifi_desc noattr.
Definition t_policy := Tstruct _wifi_policy noattr.
Definition t_vm := Tstruct _wifi_vm noattr.
Definition t_scratch := tarray tuchar SCRATCH.

(* The memory values of the structs are in Defs.v (target_val, policy_val, vm_val, ...). *)

(* ---------------------------------------------------------------------- *)
(* The outcomes of the header and of wifi_start.                          *)
(* ---------------------------------------------------------------------- *)

(* wifi_image_header's outputs (target tv, policy pv, header length hv) from the prior policy object P0: on 0
   exactly the decoded ones, on BAD anything. *)
Definition header_post (bs: list Z) (P0: policy) (tv: target_t) (pv: policy_t) (hv: val) : Prop :=
  match decode bs with
  | Some (T, P, H) => tv = target_val T /\ pv = policy_val (store P P0) /\ hv = Vint (Int.repr H)
  | None => True
  end.

(* wifi_start's executor state vv and scratch sc' from the prior state V0 and scratch sc: on 0 the started state
   and a zero scratch; on BAD the prior state but any target and policy, and the prior scratch. *)
Definition start_post (image: val) (bs: list Z) (V0: vmstate) (sc: list val) (vv: vm_t) (sc': list val) : Prop :=
  match start bs with
  | Some (T, P, H, N, B) =>
      vv = vm_val (started image V0 T P H N B) /\ sc' = Zrepeat (Vint (Int.repr 0)) SCRATCH
  | None =>
      (exists (pv: policy_t) (tv: target_t),
         vv = vm_rep (vm_code V0) (vm_blob V0) (vm_n V0) (vm_blob_len V0) (vm_window V0) pv tv
                (words_val (vm_r V0)) (words_val (vm_stack V0)) (vm_sp V0) (vm_pc V0) (vm_steps V0)) /\
      sc' = sc
  end.

(* ---------------------------------------------------------------------- *)
(* The helpers.                                                           *)
(* ---------------------------------------------------------------------- *)

(* wifi_le32(b + k): word@k of the image object at b. *)
Definition le32_spec :=
  DECLARE _wifi_le32
  WITH sh: share, b: val, bs: list Z, k: Z
  PRE [ tptr tuchar ]
    PROP (readable_share sh; 0 <= k; k + 4 <= Zlength bs; Forall u8_ok bs)
    PARAMS (offset_val k b)
    SEP (data_at sh (tarray tuchar (Zlength bs)) (bytes_val bs) b)
  POST [ tuint ]
    PROP ()
    RETURN (Vint (Int.repr (le32 bs k)))
    SEP (data_at sh (tarray tuchar (Zlength bs)) (bytes_val bs) b).

(* wifi_desc_limit(d), called after count >= 1 was checked. *)
Definition desc_limit_spec :=
  DECLARE _wifi_desc_limit
  WITH sh: share, p: val, d: desc
  PRE [ tptr t_desc ]
    PROP (readable_share sh; desc_wf d; 1 <= ds_count d)
    PARAMS (p)
    SEP (data_at sh t_desc (desc_val d) p)
  POST [ tulong ]
    PROP ()
    RETURN (Vlong (Int64.repr (desc_limit d)))
    SEP (data_at sh t_desc (desc_val d) p).

Definition has_desc_spec :=
  DECLARE _wifi_has_desc
  WITH psh: share, pp: val, P: policy, dsh: share, dp: val, d: desc
  PRE [ tptr t_policy, tptr t_desc ]
    PROP (readable_share psh; readable_share dsh; policy_wf P; pl_desc_count P <= MAX_DESCS; desc_wf d)
    PARAMS (pp; dp)
    SEP (data_at psh t_policy (policy_val P) pp; data_at dsh t_desc (desc_val d) dp)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (Z.b2z (has_desc P d))))
    SEP (data_at psh t_policy (policy_val P) pp; data_at dsh t_desc (desc_val d) dp).

Definition is_sink_spec :=
  DECLARE _wifi_is_sink
  WITH psh: share, pp: val, P: policy, off: Z
  PRE [ tptr t_policy, tuint ]
    PROP (readable_share psh; policy_wf P; pl_sink_count P <= MAX_SINKS; u32_ok off)
    PARAMS (pp; Vint (Int.repr off))
    SEP (data_at psh t_policy (policy_val P) pp)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (Z.b2z (is_sink P off))))
    SEP (data_at psh t_policy (policy_val P) pp).

(* ---------------------------------------------------------------------- *)
(* The admission (wifi_policy_within, wifi_service_admitted,              *)
(* wifi_source_admitted and their wrappers).                              *)
(* ---------------------------------------------------------------------- *)

Definition within_fspec : funspec :=
  WITH psh: share, pp: val, P: policy, msh: share, mp: val, M: policy
  PRE [ tptr t_policy, tptr t_policy ]
    PROP (readable_share psh; readable_share msh; policy_bounded P; policy_bounded M)
    PARAMS (pp; mp)
    SEP (data_at psh t_policy (policy_val P) pp; data_at msh t_policy (policy_val M) mp)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (Z.b2z (within P M))))
    SEP (data_at psh t_policy (policy_val P) pp; data_at msh t_policy (policy_val M) mp).

Definition service_fspec : funspec :=
  WITH tsh: share, tp: val, T: target, psh: share, pp: val, P: policy,
       wsh: share, wp: val, W: target, msh: share, mp: val, M: policy
  PRE [ tptr t_target, tptr t_policy, tptr t_target, tptr t_policy ]
    PROP (readable_share tsh; readable_share psh; readable_share wsh; readable_share msh;
          target_wf T; policy_bounded P; target_wf W; policy_bounded M)
    PARAMS (tp; pp; wp; mp)
    SEP (data_at tsh t_target (target_val T) tp; data_at psh t_policy (policy_val P) pp;
         data_at wsh t_target (target_val W) wp; data_at msh t_policy (policy_val M) mp)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (Z.b2z (service T P W M))))
    SEP (data_at tsh t_target (target_val T) tp; data_at psh t_policy (policy_val P) pp;
         data_at wsh t_target (target_val W) wp; data_at msh t_policy (policy_val M) mp).

Definition source_fspec : funspec :=
  WITH tsh: share, tp: val, T: target, psh: share, pp: val, P: policy, msh: share, mp: val, M: policy
  PRE [ tptr t_target, tptr t_policy, tptr t_policy ]
    PROP (readable_share tsh; readable_share psh; readable_share msh;
          target_wf T; policy_bounded P; policy_bounded M)
    PARAMS (tp; pp; mp)
    SEP (data_at tsh t_target (target_val T) tp; data_at psh t_policy (policy_val P) pp;
         data_at msh t_policy (policy_val M) mp)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (Z.b2z (source T P M))))
    SEP (data_at tsh t_target (target_val T) tp; data_at psh t_policy (policy_val P) pp;
         data_at msh t_policy (policy_val M) mp).

Definition policy_within_spec := DECLARE _wifi_policy_within within_fspec.
Definition service_admitted_spec := DECLARE _wifi_service_admitted service_fspec.
Definition source_admitted_spec := DECLARE _wifi_source_admitted source_fspec.
Definition dp_within_spec := DECLARE _dp_within within_fspec.
Definition dp_service_spec := DECLARE _dp_service service_fspec.
Definition dp_source_spec := DECLARE _dp_source source_fspec.

(* ---------------------------------------------------------------------- *)
(* The parser (wifi_image_header, wifi_start and their wrappers).         *)
(* ---------------------------------------------------------------------- *)

(* The image (sh, image, bs) is an object of exactly Zlength bs bytes.  The target and the header length may hold
   anything before; the policy object P0 any values (its entries past the decoded counts survive). *)
Definition header_fspec : funspec :=
  WITH sh: share, image: val, bs: list Z, tsh: share, tp: val, psh: share, pp: val, P0: policy,
       hsh: share, hp: val
  PRE [ tptr tuchar, tuint, tptr t_target, tptr t_policy, tptr tuint ]
    PROP (readable_share sh; writable_share tsh; writable_share psh; writable_share hsh;
          image_ok bs; policy_wf P0)
    PARAMS (image; Vint (Int.repr (Zlength bs)); tp; pp; hp)
    SEP (data_at sh (tarray tuchar (Zlength bs)) (bytes_val bs) image;
         data_at_ tsh t_target tp; data_at psh t_policy (policy_val P0) pp; data_at_ hsh tuint hp)
  POST [ tint ]
    EX tv: target_t, EX pv: policy_t, EX hv: val,
    PROP (header_post bs P0 tv pv hv)
    RETURN (Vint (Int.repr (header_status bs)))
    SEP (data_at sh (tarray tuchar (Zlength bs)) (bytes_val bs) image;
         data_at tsh t_target tv tp; data_at psh t_policy pv pp; data_at hsh tuint hv hp).

(* The executor state V0 and the scratch sc before; the scratch is the static wifi_scratch. *)
Definition start_fspec : funspec :=
  WITH gv: globals, sh: share, image: val, bs: list Z, wsh: share, vmp: val, V0: vmstate,
       ssh: share, sc: list val
  PRE [ tptr t_vm, tptr tuchar, tuint ]
    PROP (readable_share sh; writable_share wsh; writable_share ssh; image_ok bs; vm_wf V0;
          Zlength sc = SCRATCH)
    PARAMS (vmp; image; Vint (Int.repr (Zlength bs)))
    GLOBALS (gv)
    SEP (data_at sh (tarray tuchar (Zlength bs)) (bytes_val bs) image;
         data_at wsh t_vm (vm_val V0) vmp;
         data_at ssh t_scratch sc (gv _wifi_scratch))
  POST [ tint ]
    EX vv: vm_t, EX sc': list val,
    PROP (start_post image bs V0 sc vv sc')
    RETURN (Vint (Int.repr (start_status bs)))
    SEP (data_at sh (tarray tuchar (Zlength bs)) (bytes_val bs) image;
         data_at wsh t_vm vv vmp;
         data_at ssh t_scratch sc' (gv _wifi_scratch)).

Definition image_header_spec := DECLARE _wifi_image_header header_fspec.
Definition wifi_start_spec := DECLARE _wifi_start start_fspec.
Definition dp_header_spec := DECLARE _dp_header header_fspec.
Definition dp_start_spec := DECLARE _dp_start start_fspec.

(* dp_scratch(): the address of wifi_scratch. *)
Definition dp_scratch_spec :=
  DECLARE _dp_scratch
  WITH gv: globals
  PRE [ ]
    PROP () PARAMS () GLOBALS (gv) SEP ()
  POST [ tptr tuchar ]
    PROP () RETURN (gv _wifi_scratch) SEP ().

(* The context of every body proof of the unit: all its functions. *)
Definition Gprog : funspecs :=
  [le32_spec; desc_limit_spec; has_desc_spec; is_sink_spec;
   policy_within_spec; service_admitted_spec; source_admitted_spec;
   image_header_spec; wifi_start_spec;
   dp_header_spec; dp_start_spec; dp_within_spec; dp_service_spec; dp_source_spec; dp_scratch_spec].
