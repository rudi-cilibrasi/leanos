# Scalar native PCI inventory fields

The twelve-field representation includes BDF, identity, multifunction, layout and bridge routing/control. It carries no DMA or CPL3 authority. Scalar matching is a component for a complete immutable-snapshot check, not proof of physical enumeration completeness.

- `entryWords_injective` — Equal encoded rows imply equal typed entries.
- `entries_eq_of_words` — Equality of encoded lists preserves the complete ordered inventory.
- `native_inventory_of_words` — Complete encoded equality supplies the native witness's inventory property.
- `observed_entry_words` — Selected reference observation fields encode the accepted header's typed inventory projection exactly.
- `expected_row` — Every admitted scalar table index equals the corresponding complete typed baseline row.
- `matches_row` — Successful scalar comparison binds all supplied fields to the baseline slot.
- `matches_entry` — Matching fields that encode a typed entry establish that entry at the specified index.
- `checkHeader_binds_raw` — Successful direct scalar validation decodes the supplied raw header and binds its projection to the exact native slot.
- `exported_check_iff` — The stable UInt64 export returns one exactly when the proved raw-header checker succeeds; zero rejects.
