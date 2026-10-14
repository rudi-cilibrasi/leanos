# Oracle rows for interrupts, entry, and faults

The oracle block for interrupt and fault handling: interrupt entry, extended processor state, privileged-entry controls, fault dispatch, direct hardware ports, non-maskable interrupts, boot phases, stale translations, and page faults. The block starts at corpus row 86, so position `i` here is corpus row 86 + `i`. The theorems fix each sub-block's size and names and prove the exported adapters agree with the richer models on every row.

- `interrupt_entry_scenario_agrees` — The six legitimate interrupt-entry rows are accepted and all thirteen corrupted entry rows are rejected.
- `general_protection_entry_scenario_agrees` — The general-protection-fault row really is an interrupt-entry row, and it is accepted.
- `extended_state_dispatch_scenario_agrees` — In the extended processor-state block, the two peer dispatch rows produce the identical exact dispatch word, the idle row is a bare acceptance, and the policy-mismatch, kernel-origin, invariant-violation, and stale-binding rows are all refused.
- `privilege_entry_control_scenario_agrees` — In the privileged-entry-control block, only the correctly configured setup row is accepted, all eighteen mutated or degraded configurations are refused, and the return path, the user trap rows, the later event rows, and the post-fatal row each land on their exact expected code or code band.
- `privilege_entry_control_corpus_shape` — Bookkeeping: the entry-control block is exactly the 32 rows at position 26 of the interrupt family's block (corpus row 112), immediately before the fault-dispatch block.
- `privilege_entry_control_adapter_agrees_with_model` — On all 32 entry-control rows, the exported adapter agrees with the independently evaluated rich control model.
- `direct_port_io_corpus_shape` — Bookkeeping: the direct hardware-port block is exactly 28 rows, covering accepted controls, every named control mutation, stale live state, all direction and width classes, right and wrong kernel purposes, malformed words, and post-validation relaxation.
- `direct_port_io_adapter_agrees_with_model` — On all 28 port rows, the exported adapter agrees with the model.
- `nmi_corpus_shape` — Bookkeeping: the non-maskable-interrupt block is exactly 17 rows, laid out as three accepted interrupted modes plus one row for every rejection reachable through this boundary.
- `nmi_corpus_id_inventory` — Bookkeeping: the 17 non-maskable-interrupt rows carry exactly the expected names, in order.
- `nmi_adapter_agrees_with_model` — On all 17 non-maskable-interrupt rows, the exported adapter agrees with the model.
- `nmi_accepted_modes_agree` — The three accepted rows — interrupted while running user code, while handling in the kernel, and the already-halted snapshot — produce their exact expected words.
- `nmi_noncanonical_context_codes_rejected` — Context words carrying an impossible bounds code or an impossible mode code are rejected, each with its own distinct error code.
- `nmi_rejection_codes_agree` — The fourteen rejection rows produce, in order, exactly the published inventory of rejection codes.
- `user_fault_class_corpus_shape` — Bookkeeping: the contained user-fault block for divide-error and breakpoint faults is exactly 23 rows.
- `user_fault_class_entry_scenario_agrees` — The two accepted user-fault entry rows are accepted and all six entry corruptions are rejected.
- `user_fault_class_dispatch_scenario_agrees` — Accepted divide-error and breakpoint dispatches carry their exact typed reason code in the fixed bits of the result word, the kernel-origin, malformed, and wrong-restart forms produce terminal words, and the swapped-shape and stale-binding rows produce nothing.
- `boot_phase_corpus_shape` — Bookkeeping: the boot-phase block is exactly 18 rows, covering every orderly publication step, every wrong or premature publication, boot-time interrupts and faults in both bootstrap phases, the inherited window, runtime delegation, repeated terminal events, post-latch attempts, and a malformed phase code.
- `boot_phase_corpus_id_inventory` — Bookkeeping: those 18 rows carry exactly the expected names, in order.
- `boot_phase_adapter_agrees_with_model` — On all 18 boot-phase rows, the exported adapter agrees with the rich finite phase model.
- `boot_phase_expected_classes_agree` — Only the three orderly publications are accepted, both boot-time non-maskable-interrupt rows latch the absorbing terminal record, and the delegation and post-latch rows return the caller's opaque business token unchanged.
- `stale_translation_corpus_shape` — Bookkeeping: the stale-translation block is exactly the 15-row tail covering accepted unmap and protect, wrong-owner rejections, release, destroy, and switch effects, unmapped-page and post-reuse rejections, permission amplification, and a malformed encoding.
- `stale_translation_adapter_agrees_with_model` — On all 15 stale-translation rows, the exported adapter agrees with the independently evaluated authoritative transition.
- `stale_translation_scenario_agrees` — Accepted transitions carry their exact effect words — which cache invalidation is required, for which address space and page — while wrong-owner and post-reuse requests demand no invalidation at all and the malformed row changes nothing.
- `page_fault_corpus_shape` — Bookkeeping: the page-fault block is exactly 36 rows.
- `page_fault_adapter_agrees_with_model` — On all 36 page-fault rows, the exported adapter agrees with the model.
- `page_fault_subject_mutation_attested` — Changing only the faulting program's identity changes the accepted page-fault answer, proving the adapter genuinely consumes that input rather than discarding it.
- `page_fault_space_mutation_attested` — Changing only the address-space identity likewise changes the accepted answer.
- `page_fault_cr3_mutation_attested` — Changing only the page-table root likewise changes the accepted answer.
- `page_fault_wp_mutation_attested` — Changing only the write-protect control bit likewise changes the accepted answer.
- `page_fault_nxe_mutation_attested` — Changing only the no-execute control bit likewise changes the accepted answer.
- `page_fault_smep_mutation_attested` — Changing only the control that stops the kernel executing user memory likewise changes the accepted answer.
- `page_fault_smap_mutation_attested` — Changing only the control that stops the kernel reading user memory likewise changes the accepted answer.
- `page_fault_authority_mutations_attested` — All seven facts combined: no authority-bearing input to the page-fault adapter can be dropped without visibly changing the accepted answer.
