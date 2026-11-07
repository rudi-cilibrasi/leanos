(* Specifications of the four functions of include/madt_generated_admission.h (static inline, kept as separate
   functions by clightgen), and Gprog, the specifications the body proofs are stated against.  A starting point
   for the body proofs, which may revise them; the interface the law depends on (the oracle, the exports and
   the four wrappers) is MgaSpecs.v.

   Each function is specified as one phase of main's run of Defs: from the progress the phase starts at, after
   the answers h, to the progress its returned status leads to, after the answers h ++ hs:
   - madt_generated_envelope: from envelope_from x 0 initial_envelope to envelope_end x st;
   - madt_generated_entries: from begin_entries x to entries_end x st id (id written on OK);
   - madt_topology_admission_result: from the result with arguments args to result_end st id (id written on
     OK);
   - madt_generated_admission: as madt_admission (MgaSpecs.admission_pre_post).
   The APIC ID record may hold any value before (rold).  The envelope and the entries also bound their status
   (0 .. 7 and 0 .. 17, the enum's values up to their last): the admission tests it against MADT_GENERATED_OK
   as a C int, which says st = 0 only for a st in range. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import LeanosMadtAdmission.madt_admission.code.
Require Import LeanosMadtAdmission.proof.Defs.
Require Import LeanosMadtAdmission.proof.MgaSpecs.
#[local] Existing Instance MgaSpecs.CS.

(* madt_generated_envelope(bytes, length). *)
Definition generated_envelope_spec (Ora: ORA) :=
  DECLARE _madt_generated_envelope
  WITH gv: globals, x: inputs, h: list answer, bp: val, sh: share
  PRE [ tptr tuchar, tuint ]
    PROP (inputs_ok x; readable_share sh; run x (start x) h = Some (envelope_from x 0 initial_envelope))
    PARAMS (bp; vi (i_length x))
    GLOBALS (gv)
    SEP (Ora gv x h; data_at sh (tarray tuchar (i_length x)) (bytes_val (i_bytes x)) bp)
  POST [ tint ]
    EX hs: list answer, EX st: Z,
    PROP (run x (start x) (h ++ hs) = Some (envelope_end x st); 0 <= st <= 7)
    RETURN (vi st)
    SEP (Ora gv x (h ++ hs); data_at sh (tarray tuchar (i_length x)) (bytes_val (i_bytes x)) bp).

(* madt_generated_entries(bytes, length, executing_apic_id, admitted_apic_id). *)
Definition generated_entries_spec (Ora: ORA) :=
  DECLARE _madt_generated_entries
  WITH gv: globals, x: inputs, h: list answer, bp: val, sh: share, rp: val, rsh: share, rold: val
  PRE [ tptr tuchar, tuint, tuint, tptr tuint ]
    PROP (inputs_ok x; readable_share sh; writable_share rsh; run x (start x) h = Some (begin_entries x))
    PARAMS (bp; vi (i_length x); vi (i_executing x); rp)
    GLOBALS (gv)
    SEP (Ora gv x h; data_at sh (tarray tuchar (i_length x)) (bytes_val (i_bytes x)) bp;
         data_at rsh tuint rold rp)
  POST [ tint ]
    EX hs: list answer, EX st: Z, EX id: Z,
    PROP (run x (start x) (h ++ hs) = Some (entries_end x st id); u32_ok id; 0 <= st <= 17)
    RETURN (vi st)
    SEP (Ora gv x (h ++ hs); data_at sh (tarray tuchar (i_length x)) (bytes_val (i_bytes x)) bp;
         data_at rsh tuint (if st =? S_OK then vi id else rold) rp).

(* madt_topology_admission_result(args[0..9], published_apic_id). *)
Definition topology_result_spec (Ora: ORA) :=
  DECLARE _madt_topology_admission_result
  WITH gv: globals, x: inputs, h: list answer, args: list Z, rp: val, rsh: share, rold: val
  PRE [ tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tptr tuint ]
    PROP (writable_share rsh; Zlength args = 10; Forall u64_ok args;
          run x (start x) h = Some (Go (ExpectResult args nil)))
    PARAMS (vl (Znth 0 args); vl (Znth 1 args); vl (Znth 2 args); vl (Znth 3 args); vl (Znth 4 args);
            vl (Znth 5 args); vl (Znth 6 args); vl (Znth 7 args); vl (Znth 8 args); vl (Znth 9 args); rp)
    GLOBALS (gv)
    SEP (Ora gv x h; data_at rsh tuint rold rp)
  POST [ tint ]
    EX hs: list answer, EX st: Z, EX id: Z,
    PROP (run x (start x) (h ++ hs) = Some (result_end st id); u32_ok id)
    RETURN (vi st)
    SEP (Ora gv x (h ++ hs); data_at rsh tuint (if st =? S_OK then vi id else rold) rp).

(* madt_generated_admission: the specification of its wrapper madt_admission. *)
Definition generated_admission_spec Ora := admission_pre_post Ora _madt_generated_admission.

Definition Gprog (Ora: ORA) : funspecs :=
  [envelope_step_spec Ora; entry_step_spec Ora; result_query_spec Ora;
   generated_envelope_spec Ora; generated_entries_spec Ora; topology_result_spec Ora;
   generated_admission_spec Ora;
   envelope_spec Ora; entries_spec Ora; result_spec Ora; admission_spec Ora].
