# Checking the captured Qotom processor inventory

This topology-only candidate binds the complete observation to BSP 0 and ordered enabled processor IDs 0, 2, 4, 6. It grants no runtime authority and makes no AP-dormancy or interrupt-routing safety claim. The first five results are general witness laws; the remaining results check concrete inputs, including explicitly synthetic root-table fixtures.

- `check_preserves_observation` — Every successful check retains the exact input snapshot in its witness.
- `witness_has_complete_baseline` — Every witness carries the complete fixed processor baseline together.
- `witness_binds_executing_bsp` — Every witness binds both the executing and recorded BSP identity to 0.
- `witness_enumerates_four_enabled_processors` — Every witness contains exactly the four specified enabled processors with no online-capable flag.
- `witness_still_rejected_by_single_core` — The existing single-core policy rejects every candidate witness as multiple enabled processors.
- `baseline_candidate_accepted` — The exact baseline passes the topology-only check.
- `wrong_source_rejected` — A CPUID-sourced snapshot is rejected.
- `wrong_version_rejected` — Snapshot version 2 is rejected.
- `wrong_executing_bsp_rejected` — Executing processor 2 is rejected.
- `wrong_recorded_bsp_rejected` — Recorded BSP 2 is rejected.
- `duplicate_processor_rejected` — Repeating the processor list is rejected as duplicate identities.
- `missing_processors_rejected` — An empty processor list is rejected as having no enabled processor.
- `missing_one_processor_rejected` — Removing the last captured processor fails exact inventory matching.
- `changed_processor_order_rejected` — Reversing the captured processor order fails exact inventory matching.
- `disabled_ap_rejected` — Disabling processor 2 fails exact inventory matching.
- `online_capable_ap_rejected` — Marking processor 2 online-capable fails exact inventory matching.
- `exceeded_bound_rejected_before_duplicates` — An oversized duplicate list receives the bounds rejection first.
- `q35_cannot_supply_qotom_topology` — The single-core q35 inventory cannot satisfy the Qotom candidate.
- `authoritative_synthetic_four_cpu_candidate_accepted` — A synthetic root-selected four-processor table passes the candidate check.
- `missing_root_cannot_reach_candidate` — Missing ACPI root tags fail before candidate matching.
- `wrong_root_address_cannot_reach_candidate` — A copied root at the wrong address fails before candidate matching.
- `missing_translation_cannot_reach_candidate` — A missing translation for a root entry fails before candidate matching.
- `duplicate_translation_cannot_reach_candidate` — Duplicate translations fail before candidate matching.
- `damaged_madt_cannot_reach_candidate` — A damaged selected MADT checksum fails before candidate matching.
- `authoritative_wrong_executing_bsp_rejected` — The authoritative synthetic path rejects executing processor 2.
- `authoritative_q35_cannot_supply_candidate` — The authoritative q35 table path cannot satisfy the Qotom inventory.
