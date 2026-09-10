# Optional early text-console geometry

A bootloader-advertised EGA text surface is accepted only inside the initial color-text aperture with bounded dimensions and an even pitch wide enough for each row. The caller supplies the initial mapping and device authority; these proofs do not establish monitor presence or later mapping validity.

- `accepted_geometry` — An accepted surface has EGA text format, 16-bit character cells, the color-text aperture address, and bounded nonzero dimensions with a valid pitch.
- `cell_inside_surface` — Every character cell's two bytes fit inside the advertised pitch-times-height extent.
- `cell_inside_aperture` — Every character cell's two bytes fit inside the 32 KiB initial color-text aperture without arithmetic wrapping.
