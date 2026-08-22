#!/usr/bin/env python3
"""Generate and verify INVARIANTS.md, the plain-English index of Lean theorems.

INVARIANTS.md explains, for a non-technical reader, every theorem that the
default Lean build proves (all of them, and only them).  This script keeps that
promise machine-checked:

  extract   Parse LeanOS.lean and LeanOS/*.lean and list every `theorem`
            declaration (JSON on stdout or --json PATH).
  generate  Call a language model (OpenAI or Anthropic API) with the prompt in
            scripts/invariants-prompt.md to write one per-file section at a
            time into --sections-dir, then assemble INVARIANTS.md.
  assemble  Build INVARIANTS.md from already-written per-file section files,
            validating that each section explains exactly the extracted
            theorems in source order.
  verify    Re-extract the theorems and check that INVARIANTS.md lists all of
            them and only them, with matching totals.  Offline, deterministic,
            no API key needed; used by scripts/check-invariants.sh.

The theorem inventory is whatever the extractor finds; the language model only
ever writes explanation sentences and section introductions.  It never chooses
which theorems appear.
"""

import argparse
import bisect
import datetime
import json
import os
import re
import sys
import urllib.error
import urllib.request
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
PROMPT_PATH = REPO_ROOT / "scripts" / "invariants-prompt.md"
DEFAULT_DOC = REPO_ROOT / "INVARIANTS.md"

MODIFIERS = r"(?:(?:private|protected|scoped|noncomputable)[ \t]+)*"
ATTRIBUTES = r"(?:@\[[^\]]*\][ \t]*)*"
NAME = r"([A-Za-z_«][A-Za-z0-9_'«».!?]*)"
THEOREM_RE = re.compile(
    r"(?m)^[ \t]*" + ATTRIBUTES + MODIFIERS + r"theorem[ \t\r\n]+" + NAME
)
EXAMPLE_RE = re.compile(r"(?m)^[ \t]*example\b")
NAMESPACE_RE = re.compile(r"^[ \t]*namespace[ \t]+([A-Za-z0-9_.«»]+)")
SECTION_RE = re.compile(r"^[ \t]*section\b(?:[ \t]+([A-Za-z0-9_.«»]+))?[ \t]*$")
MUTUAL_RE = re.compile(r"^[ \t]*mutual\b[ \t]*$")
END_RE = re.compile(r"^[ \t]*end\b(?:[ \t]+([A-Za-z0-9_.«»]+))?[ \t]*$")

BULLET_RE = re.compile(r"^- `([^`]+)` — (.+)$")
HEADING_RE = re.compile(r"^## .*`([^`]+\.lean)`.*$")
TOTALS_RE = re.compile(
    r"<!-- invariants:totals theorems=(\d+) files=(\d+) examples=(\d+) -->"
)
PROSE_TOTALS_RE = re.compile(
    r"The Lean sources currently prove \*\*(\d+) named theorems\*\* across "
    r"\*\*(\d+) files\*\*"
)
SNIPPET_LINES = 30


def source_files():
    files = [REPO_ROOT / "LeanOS.lean"]
    files.extend(sorted((REPO_ROOT / "LeanOS").glob("*.lean")))
    return files


def blank_comments_and_strings(text):
    """Replace comments and string/char literals with spaces, keep newlines.

    Also returns the list of (end_offset, body) for `/-- ... -/` docstrings so
    extraction can attach each docstring to the declaration that follows it.
    """
    out = list(text)
    docstrings = []
    i, n = 0, len(text)

    def blank(a, b):
        for k in range(a, b):
            if out[k] != "\n":
                out[k] = " "

    while i < n:
        two = text[i : i + 2]
        if two == "--":
            j = text.find("\n", i)
            j = n if j == -1 else j
            blank(i, j)
            i = j
        elif two == "/-":
            is_doc = text[i : i + 3] == "/--" and text[i : i + 4] != "/---"
            depth, j = 1, i + 2
            while j < n and depth > 0:
                if text[j : j + 2] == "/-":
                    depth += 1
                    j += 2
                elif text[j : j + 2] == "-/":
                    depth -= 1
                    j += 2
                else:
                    j += 1
            if is_doc:
                docstrings.append((j, text[i + 3 : j - 2].strip()))
            blank(i, j)
            i = j
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            j = min(j + 1, n)
            blank(i + 1, j - 1)
            i = j
        else:
            i += 1
    return "".join(out), docstrings


def extract_file(path):
    text = path.read_text(encoding="utf-8")
    clean, docstrings = blank_comments_and_strings(text)
    lines = clean.split("\n")

    # Namespace stack per line: walk statements in order.
    stack = []  # entries: ("namespace", [components]) / ("section"|"mutual", None)
    stack_at_offset = []  # (offset, namespace components) checkpoints
    offset = 0
    for line in lines:
        m = NAMESPACE_RE.match(line)
        if m:
            stack.append(("namespace", m.group(1).split(".")))
        elif SECTION_RE.match(line):
            stack.append(("section", None))
        elif MUTUAL_RE.match(line):
            stack.append(("mutual", None))
        elif END_RE.match(line):
            if stack:
                stack.pop()
        ns = [c for kind, comps in stack if kind == "namespace" for c in comps]
        offset += len(line) + 1
        stack_at_offset.append((offset, ns))

    boundaries = [b for b, _ in stack_at_offset]

    def namespace_at(pos):
        index = bisect.bisect_right(boundaries, pos)
        return stack_at_offset[index - 1][1] if index else []

    newline_offsets = [i for i, ch in enumerate(clean) if ch == "\n"]
    docstring_ends = [end for end, _ in docstrings]
    text_lines = text.split("\n")

    theorems = []
    for m in THEOREM_RE.finditer(clean):
        name_start = m.start(1)
        ns = namespace_at(m.start())
        declared = m.group(1).rstrip(".")
        line_no = bisect.bisect_right(newline_offsets, name_start) + 1
        doc = ""
        index = bisect.bisect_right(docstring_ends, m.start()) - 1
        if index >= 0:
            end, body = docstrings[index]
            between = clean[end : m.start()]
            if all(
                not part.strip()
                or part.lstrip().startswith(("set_option", "open ", "@["))
                for part in between.split("\n")
            ):
                doc = body
        decl_line = bisect.bisect_right(newline_offsets, m.start())
        snippet = "\n".join(text_lines[decl_line : decl_line + SNIPPET_LINES])
        theorems.append(
            {
                "file": str(path.relative_to(REPO_ROOT)),
                "line": line_no,
                "namespace": ".".join(ns),
                "declared": declared,
                "qualified": ".".join(ns + [declared]) if ns else declared,
                "docstring": doc,
                "snippet": snippet,
            }
        )

    # Display name: qualified name minus the namespace components shared by
    # every theorem in the file (component-aligned), so single-namespace files
    # read as the bare declared name.
    if theorems:
        stacks = [t["namespace"].split(".") if t["namespace"] else [] for t in theorems]
        common = stacks[0]
        for s in stacks[1:]:
            k = 0
            while k < min(len(common), len(s)) and common[k] == s[k]:
                k += 1
            common = common[:k]
        for t, s in zip(theorems, stacks):
            extra = s[len(common) :]
            t["display"] = ".".join(extra + [t["declared"]])
        seen = {}
        for t in theorems:
            if t["display"] in seen:
                seen[t["display"]] += 1
                t["display"] = t["qualified"]
            else:
                seen[t["display"]] = 1
    examples = len(EXAMPLE_RE.findall(clean))
    return theorems, examples


def extract_all():
    per_file = {}
    total_examples = 0
    for path in source_files():
        theorems, examples = extract_file(path)
        total_examples += examples
        if theorems:
            per_file[str(path.relative_to(REPO_ROOT))] = theorems
    return per_file, total_examples


def section_key(rel_path):
    return rel_path.replace("/", "__").replace(".lean", "") + ".md"


def parse_section(text, rel_path, expected):
    """Validate a per-file section: '# Title', intro prose, then one bullet
    per expected theorem in order.  Returns (title, intro_lines, bullets)."""
    lines = [line.rstrip() for line in text.strip().split("\n")]
    if not lines or not lines[0].startswith("# "):
        raise ValueError(f"{rel_path}: section must start with '# <title>'")
    title = lines[0][2:].strip()
    intro, bullets = [], []
    for line in lines[1:]:
        m = BULLET_RE.match(line)
        if m:
            bullets.append((m.group(1), m.group(2)))
        elif bullets:
            if line.strip():
                raise ValueError(
                    f"{rel_path}: prose after bullets began: {line!r}"
                )
        else:
            intro.append(line)
    got = [name for name, _ in bullets]
    want = [t["display"] for t in expected]
    if got != want:
        missing = [n for n in want if n not in got]
        extra = [n for n in got if n not in want]
        raise ValueError(
            f"{rel_path}: bullets do not match extracted theorems in order; "
            f"missing={missing[:5]} extra={extra[:5]} "
            f"(got {len(got)}, want {len(want)})"
        )
    while intro and not intro[0].strip():
        intro.pop(0)
    while intro and not intro[-1].strip():
        intro.pop()
    if not intro:
        raise ValueError(f"{rel_path}: section has no introduction paragraph")
    return title, intro, bullets


def build_document(per_file, total_examples, sections, generator, date):
    total = sum(len(v) for v in per_file.values())
    out = []
    out.append("# LeanOS invariants, in plain English")
    out.append("")
    out.append(
        f"<!-- invariants:totals theorems={total} files={len(per_file)} "
        f"examples={total_examples} -->"
    )
    out.append(
        "<!-- Generated by scripts/generate-invariants.py; do not edit the "
        "bullet lists by hand without re-running "
        "`python3 scripts/generate-invariants.py verify`. -->"
    )
    out.append("")
    out.append(
        "LeanOS is an experimental operating-system kernel whose safety and "
        "security rules are written and proved in the Lean theorem prover. "
        "This page explains, in ordinary language, every guarantee the Lean "
        "code currently proves — all of them, and only them. Each bullet "
        "below is one Lean theorem: a statement that the Lean proof checker "
        "has verified is true of the kernel's formal model, every time the "
        "project builds."
    )
    out.append("")
    out.append(
        f"The Lean sources currently prove **{total} named theorems** across "
        f"**{len(per_file)} files**, listed completely below. The code also "
        f"contains {total_examples} anonymous `example` proofs — inline "
        "sanity checks with no names — which are verified by the same build "
        "but cannot be listed individually because they are unnamed. The "
        "deliberately broken claims under `tests/negative/` are *not* proofs "
        "and are excluded; the build gate exists to reject them."
    )
    out.append("")
    out.append("## What these guarantees do and do not cover")
    out.append("")
    out.append(
        "Every theorem here is proved about the kernel's *formal model*: a "
        "precise mathematical description of the kernel written in Lean. The "
        "connection between that model and the machine code that actually "
        "boots is a separate engineering chain — generated C code, compilers, "
        "the QEMU emulator, and hardware — that is tested by the repository's "
        "evidence scripts rather than proved. For the precise statement of "
        "what is proved versus what is trusted, see "
        "[docs/security-claims.md](docs/security-claims.md) and "
        "[docs/model-oracle.md](docs/model-oracle.md). In short: if a bullet "
        "below says \"the kernel refuses X,\" the Lean model of the kernel "
        "provably refuses X, and the project's test evidence — not a proof — "
        "links that model to the running binary."
    )
    out.append("")
    out.append(
        f"Generated by model `{generator}` on {date} with "
        "`scripts/generate-invariants.py` (prompt: "
        "`scripts/invariants-prompt.md`). The explanations are "
        "machine-written; the theorem list itself is extracted "
        "deterministically from the Lean sources, and "
        "`scripts/check-invariants.sh` fails the build if this page ever "
        "lists more or fewer theorems than the code proves."
    )
    for rel_path in sorted(per_file):
        title, intro, bullets = sections[rel_path]
        out.append("")
        out.append(f"## {title} (`{rel_path}`)")
        out.append("")
        out.extend(intro)
        out.append("")
        for name, sentence in bullets:
            out.append(f"- `{name}` — {sentence}")
    out.append("")
    return "\n".join(out)


def cmd_extract(args):
    per_file, total_examples = extract_all()
    payload = {
        "total_theorems": sum(len(v) for v in per_file.values()),
        "total_files": len(per_file),
        "total_examples": total_examples,
        "files": per_file,
    }
    text = json.dumps(payload, indent=2)
    if args.json:
        Path(args.json).write_text(text + "\n", encoding="utf-8")
        print(
            f"extracted {payload['total_theorems']} theorems from "
            f"{payload['total_files']} files -> {args.json}"
        )
    else:
        print(text)
    return 0


def load_sections(per_file, sections_dir):
    sections = {}
    for rel_path, theorems in per_file.items():
        section_path = Path(sections_dir) / section_key(rel_path)
        if not section_path.is_file():
            raise ValueError(f"missing section file: {section_path}")
        sections[rel_path] = parse_section(
            section_path.read_text(encoding="utf-8"), rel_path, theorems
        )
    return sections


def cmd_assemble(args):
    per_file, total_examples = extract_all()
    try:
        sections = load_sections(per_file, args.sections_dir)
    except ValueError as err:
        print(f"assemble error: {err}", file=sys.stderr)
        return 1
    doc = build_document(
        per_file, total_examples, sections, args.generator, args.date
    )
    Path(args.output).write_text(doc, encoding="utf-8")
    print(f"wrote {args.output}")
    return 0


def call_model(args, system_prompt, user_prompt):
    if args.provider == "openai":
        key = os.environ.get("OPENAI_API_KEY")
        if not key:
            raise ValueError("OPENAI_API_KEY is not set")
        base = os.environ.get("OPENAI_BASE_URL", "https://api.openai.com/v1")
        url = f"{base.rstrip('/')}/chat/completions"
        body = {
            "model": args.model,
            "messages": [
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": user_prompt},
            ],
        }
        headers = {"Authorization": f"Bearer {key}"}
    else:
        key = os.environ.get("ANTHROPIC_API_KEY")
        if not key:
            raise ValueError("ANTHROPIC_API_KEY is not set")
        base = os.environ.get("ANTHROPIC_BASE_URL", "https://api.anthropic.com")
        url = f"{base.rstrip('/')}/v1/messages"
        body = {
            "model": args.model,
            "max_tokens": args.max_output_tokens,
            "system": system_prompt,
            "messages": [{"role": "user", "content": user_prompt}],
        }
        headers = {"x-api-key": key, "anthropic-version": "2023-06-01"}
    headers["Content-Type"] = "application/json"
    request = urllib.request.Request(
        url, data=json.dumps(body).encode("utf-8"), headers=headers
    )
    try:
        with urllib.request.urlopen(request, timeout=600) as response:
            reply = json.loads(response.read().decode("utf-8"))
    except urllib.error.HTTPError as err:
        detail = err.read().decode("utf-8", "replace")[:500]
        raise ValueError(f"model API error {err.code}: {detail}") from err
    if args.provider == "openai":
        return reply["choices"][0]["message"]["content"]
    return "".join(
        block["text"] for block in reply["content"] if block["type"] == "text"
    )


def chunk(theorems, size):
    return [theorems[i : i + size] for i in range(0, len(theorems), size)]


def cmd_generate(args):
    prompt_template = PROMPT_PATH.read_text(encoding="utf-8")
    marker = "<!-- prompt:split -->"
    if marker not in prompt_template:
        print(f"generate error: {PROMPT_PATH} lacks {marker}", file=sys.stderr)
        return 1
    system_prompt, user_template = prompt_template.split(marker, 1)
    per_file, total_examples = extract_all()
    sections_dir = Path(args.sections_dir)
    sections_dir.mkdir(parents=True, exist_ok=True)
    for rel_path in sorted(per_file):
        theorems = per_file[rel_path]
        section_path = sections_dir / section_key(rel_path)
        if section_path.is_file() and not args.force:
            print(f"keeping existing {section_path}")
            continue
        parts = []
        for index, group in enumerate(chunk(theorems, args.chunk_size)):
            names = "\n".join(t["display"] for t in group)
            snippets = "\n\n".join(
                f"-- {t['display']} (line {t['line']})\n"
                + (f"/-- {t['docstring']} -/\n" if t["docstring"] else "")
                + t["snippet"]
                for t in group
            )
            part_note = (
                "Write the `# Title` line and the introduction paragraph, "
                "then the bullets."
                if index == 0
                else "This is a continuation chunk of the same file: write "
                "ONLY the bullets, with no title and no introduction."
            )
            user_prompt = (
                user_template.replace("{{FILE}}", rel_path)
                .replace("{{PART_NOTE}}", part_note)
                .replace("{{NAMES}}", names)
                .replace("{{SNIPPETS}}", snippets)
            )
            print(
                f"generating {rel_path} chunk {index + 1} "
                f"({len(group)} theorems) via {args.provider}:{args.model}"
            )
            parts.append(call_model(args, system_prompt, user_prompt).strip())
        text = "\n\n".join(parts) + "\n"
        try:
            parse_section(text, rel_path, theorems)
        except ValueError as err:
            draft = section_path.with_suffix(".rejected.md")
            draft.write_text(text, encoding="utf-8")
            print(
                f"generate error: {err}\n(model output kept at {draft})",
                file=sys.stderr,
            )
            return 1
        section_path.write_text(text, encoding="utf-8")
    return cmd_assemble(args)


def cmd_verify(args):
    per_file, total_examples = extract_all()
    doc_path = Path(args.document)
    if not doc_path.is_file():
        print(f"verify error: missing {doc_path}", file=sys.stderr)
        return 1
    doc = doc_path.read_text(encoding="utf-8")

    errors = []
    m = TOTALS_RE.search(doc)
    total = sum(len(v) for v in per_file.values())
    if not m:
        errors.append("missing invariants:totals marker")
    else:
        got = tuple(int(g) for g in m.groups())
        want = (total, len(per_file), total_examples)
        if got != want:
            errors.append(
                f"totals marker says theorems={got[0]} files={got[1]} "
                f"examples={got[2]} but sources have theorems={want[0]} "
                f"files={want[1]} examples={want[2]}"
            )
    prose = PROSE_TOTALS_RE.search(doc)
    if not prose:
        errors.append("missing named-theorem prose totals")
    else:
        got = tuple(int(group) for group in prose.groups())
        want = (total, len(per_file))
        if got != want:
            errors.append(
                f"prose says theorems={got[0]} files={got[1]} but sources "
                f"have theorems={want[0]} files={want[1]}"
            )
    if "Generated by model `" not in doc:
        errors.append("missing 'Generated by model' provenance line")

    doc_sections = {}
    current = None
    for line_no, line in enumerate(doc.split("\n"), start=1):
        heading = HEADING_RE.match(line)
        if heading:
            current = heading.group(1)
            if current in doc_sections:
                errors.append(f"duplicate section for {current}")
            doc_sections[current] = []
            continue
        bullet = BULLET_RE.match(line)
        if bullet:
            if current is None:
                errors.append(f"line {line_no}: bullet before any file section")
            else:
                doc_sections[current].append(bullet.group(1))

    for rel_path in sorted(per_file):
        want = [t["display"] for t in per_file[rel_path]]
        got = doc_sections.get(rel_path)
        if got is None:
            errors.append(f"missing section for {rel_path} ({len(want)} theorems)")
            continue
        if got != want:
            missing = [n for n in want if n not in got]
            extra = [n for n in got if n not in want]
            errors.append(
                f"{rel_path}: listed theorems diverge from sources; "
                f"missing={missing[:5]} extra={extra[:5]} "
                f"(listed {len(got)}, proved {len(want)})"
            )
    for rel_path in doc_sections:
        if rel_path not in per_file:
            errors.append(f"section for {rel_path} which has no theorems in sources")

    if errors:
        print("INVARIANTS.md is out of date with the Lean sources:", file=sys.stderr)
        for err in errors:
            print(f"  - {err}", file=sys.stderr)
        print(
            "Regenerate with scripts/generate-invariants.py generate "
            "(or hand-edit the affected bullets to match) and re-run "
            "scripts/check-invariants.sh.",
            file=sys.stderr,
        )
        return 1
    print(
        f"INVARIANTS.md is current: {total} theorems across "
        f"{len(per_file)} files, {total_examples} anonymous examples."
    )
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)

    p = sub.add_parser("extract", help="list every theorem as JSON")
    p.add_argument("--json", help="write JSON to this path instead of stdout")
    p.set_defaults(func=cmd_extract)

    def add_assemble_args(p):
        p.add_argument("--sections-dir", required=True)
        p.add_argument("--output", default=str(DEFAULT_DOC))
        p.add_argument("--generator", required=True, help="model id for provenance")
        p.add_argument(
            "--date", default=datetime.date.today().isoformat(),
            help="provenance date (YYYY-MM-DD)",
        )

    p = sub.add_parser("assemble", help="build INVARIANTS.md from section files")
    add_assemble_args(p)
    p.set_defaults(func=cmd_assemble)

    p = sub.add_parser("generate", help="write sections with a model, then assemble")
    add_assemble_args(p)
    p.add_argument("--provider", choices=["openai", "anthropic"], default="openai")
    p.add_argument(
        "--model", default=None,
        help="model id (default: gpt-5.6-sol for openai, claude-fable-5 for anthropic)",
    )
    p.add_argument("--chunk-size", type=int, default=40)
    p.add_argument("--max-output-tokens", type=int, default=16000)
    p.add_argument("--force", action="store_true", help="regenerate existing sections")
    p.set_defaults(func=cmd_generate)

    p = sub.add_parser("verify", help="check INVARIANTS.md against the sources")
    p.add_argument("--document", default=str(DEFAULT_DOC))
    p.set_defaults(func=cmd_verify)

    args = parser.parse_args()
    if args.command == "generate" and args.model is None:
        args.model = "gpt-5.6-sol" if args.provider == "openai" else "claude-fable-5"
    try:
        return args.func(args)
    except ValueError as err:
        print(f"{args.command} error: {err}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
