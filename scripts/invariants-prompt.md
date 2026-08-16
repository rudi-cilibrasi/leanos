# INVARIANTS.md generation prompt

This file is the prompt that `scripts/generate-invariants.py generate` sends to
the language model (everything before the split marker is the system prompt;
everything after it is the per-chunk user prompt, with `{{FILE}}`,
`{{PART_NOTE}}`, `{{NAMES}}`, and `{{SNIPPETS}}` substituted). The same
instructions apply to any model or agent asked to write or update a section of
`INVARIANTS.md` by hand.

You are writing one section of `INVARIANTS.md` for the LeanOS project: a
complete plain-English index of every theorem proved by the repository's Lean
sources. The audience is an intelligent adult with **no programming or formal
methods background** who wants to know what the kernel provably guarantees.

Rules:

1. You will be given the exact ordered list of theorem names for one Lean
   source file, plus the Lean text of each theorem. Output exactly one bullet
   per name, in the given order, formatted precisely as:
   `` - `name` — sentence ``
   (hyphen, space, backticked name exactly as given, space, em dash, space,
   explanation). Never add, drop, rename, or reorder theorems: the list of
   names is extracted deterministically from the code and is checked
   mechanically after you answer.
2. Each explanation is one plain-English sentence (a second is allowed only
   when one would be misleading). Present tense. Name the actors — the kernel,
   a program, a device, a message, a region of memory — instead of Lean
   identifiers where possible. Avoid jargon: no "Prop", "simp", "structure",
   "monad", "hypothesis"; say "whenever/never/exactly" instead of quantifier
   symbols.
3. Be faithful. Do not overclaim: if a theorem only restates a definition or
   bridges two formulations, say that honestly (for example, "Restated
   bookkeeping: …" or "A stepping-stone fact used by the theorems below: …").
   Do not add global caveats about models or hardware in individual bullets —
   the document's introduction states the proved-versus-trusted boundary once
   for everything.
4. {{PART_NOTE}} placeholder in the user prompt controls whether you also
   write the section header: when asked for it, the header is a line
   `# <Title>` (a short human topic title for the file, such as "Message
   passing between programs"), followed by a blank line and a 2–4 sentence
   introduction paragraph summarizing, for the same non-technical reader,
   what this file's theorems collectively guarantee. No other headings, no
   code fences, no numbered lists.
5. Output raw Markdown only — no surrounding commentary, no code fences.

<!-- prompt:split -->

File: `{{FILE}}`

{{PART_NOTE}}

The theorem names, in order (one bullet each, names verbatim):

{{NAMES}}

The Lean text of each theorem (name, then its declaration; docstrings between
`/--` and `-/` are the authors' own summaries — trust them):

{{SNIPPETS}}
