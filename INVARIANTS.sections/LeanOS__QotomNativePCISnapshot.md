# Complete native PCI snapshot binding

The proof model has fixed sixteen-word input records. Its loop contract requires exactly sixteen immutable entries, checked at indices zero through fifteen by the generated scalar checker. This establishes an inventory witness, not device quiescence or hardware enumeration completeness.

- `Input.check_binds` — A successful scalar check of an input record decodes that record's actual raw words and binds its projection to the baseline position.
- `complete_snapshot` — A complete sixteen-entry loop produces a native inventory witness preserving the entire supplied raw-header list in order. The finite index bound also rules out UInt64 index wrapping.
