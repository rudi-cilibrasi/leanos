# Validated copy-alias operands

The operand model turns validated locations into reserved alias pages and physical byte offsets. It assumes a successful, stable plan; it does not install roots, execute transfer instructions, or account for cached translations.

- `frame_index_lookup` — Looking up the index of a frame present in the list retrieves that same frame.
- `location_frame_in_plan` — Every validated byte location names a frame included in its accepted alias plan.
- `operand_in_slots` — Every validated operand uses one of the two reserved virtual alias pages.
- `operand_leaf_exact` — The selected alias page maps exactly the validated physical frame with the request's alias permissions.
- `operands_length` — There is exactly one operand per requested byte, including none for a zero-length request.
- `validated_location_authorized` — Each validated location comes from an authorized original byte address inside the requested range.
- `validated_offset_bound` — Every validated physical-byte offset lies inside its 4 KiB page.
- `operand_offset_exact` — An alias operand retains its validated physical-byte offset and the page bound.
- `operands_at` — Selecting any operand index preserves the corresponding validated location and its order.
- `operands_prefix` — A completed operand prefix corresponds to the same location prefix as the partial-copy model.
