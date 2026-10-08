#!/usr/bin/env python3
"""Extract one generated scalar C export as a LeanOS C-subset AST (issue #470).

The pinned Lean toolchain emits each `@[export]` scalar function into the
module's generated `.c`. This tool parses exactly the C subset that
`LeanOS/Refinement/CSubset.lean` gives meaning to and prints the function as a
Lean `Func` term. It rejects every other construct, so the proof about the
checked-in AST covers the emitted function only while the two agree.

usage: extract-generated-c.py GENERATED.c EXPORT_NAME
       extract-generated-c.py --check GENERATED.c EXPORT_NAME LEAN_FILE
  --check compares the rendering with the text between the
  `-- BEGIN GENERATED AST` and `-- END GENERATED AST` markers of LEAN_FILE.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

TOKEN = re.compile(r"\s*(?:(?P<id>[A-Za-z_][A-Za-z0-9_]*)|(?P<num>[0-9]+(?:ULL)?)|"
                   r"(?P<op>==|[{}();:=,]))")


class Reject(Exception):
    pass


def tokens(text: str) -> list[str]:
    out, i = [], 0
    while i < len(text):
        if text[i:].strip() == "":
            break
        match = TOKEN.match(text, i)
        if not match:
            raise Reject(f"unsupported C near: {text[i:i + 40]!r}")
        out.append(match.group(match.lastgroup))
        i = match.end()
    return out


class Parser:
    def __init__(self, toks: list[str]):
        self.toks, self.i = toks, 0

    def peek(self, k: int = 0) -> str | None:
        return self.toks[self.i + k] if self.i + k < len(self.toks) else None

    def take(self, expected: str | None = None) -> str:
        tok = self.peek()
        if tok is None or (expected is not None and tok != expected):
            raise Reject(f"expected {expected!r}, found {tok!r}")
        self.i += 1
        return tok

    def expr(self) -> str:
        tok = self.take()
        if tok == "lean_uint64_dec_eq":
            self.take("(")
            left = self.expr()
            self.take(",")
            right = self.expr()
            self.take(")")
            return f"(.decEq {left} {right})"
        if re.fullmatch(r"[0-9]+ULL", tok):
            return f"(.lit {tok[:-3]})"
        if re.fullmatch(r"v_[A-Za-z0-9_]*", tok):
            return f'(.var "{tok}")'
        raise Reject(f"unsupported expression {tok!r}")

    def stmts(self) -> list[str]:
        out = []
        while self.peek() not in (None, "}"):
            out.extend(self.stmt())
        return out

    def braced(self) -> list[str]:
        self.take("{")
        body = self.stmts()
        self.take("}")
        return body

    def stmt(self) -> list[str]:
        tok = self.peek()
        if tok in ("uint64_t", "uint8_t"):
            ty = ".u64" if self.take() == "uint64_t" else ".u8"
            names = [self.take()]
            self.take(";")
            return [f'(.decl {ty} "{name}")' for name in names]
        if tok == "if":
            self.take("if")
            self.take("(")
            name = self.take()
            self.take("==")
            if self.take() != "0":
                raise Reject("only `if (x == 0)` is supported")
            self.take(")")
            then_ = self.braced()
            self.take("else")
            else_ = self.braced()
            return [f'(.ifZero "{name}" {lean_list(then_)} {lean_list(else_)})']
        if tok == "goto":
            self.take("goto")
            label = self.take()
            self.take(";")
            return [f'(.goto "{label}")']
        if tok == "return":
            self.take("return")
            value = self.expr()
            self.take(";")
            return [f"(.ret {value})"]
        if tok is not None and self.peek(1) == ":":
            label = self.take()
            self.take(":")
            return [f'(.block "{label}" {lean_list(self.braced())})']
        if tok is not None and self.peek(1) == "=":
            name = self.take()
            self.take("=")
            value = self.expr()
            self.take(";")
            return [f'(.assign "{name}" {value})']
        raise Reject(f"unsupported statement starting {tok!r}")


def lean_list(items: list[str]) -> str:
    return "[" + ", ".join(items) + "]" if items else "[]"


def extract(source: str, export: str) -> str:
    header = re.search(
        rf"LEAN_EXPORT uint64_t {re.escape(export)}\(uint64_t (v_[A-Za-z0-9_]+), "
        rf"uint64_t (v_[A-Za-z0-9_]+)\)\{{\n_start:\n", source)
    if not header:
        raise Reject(f"no two-argument uint64_t definition of {export}")
    # The body is the brace-balanced block after `_start:`.
    start = header.end()
    if source[start] != "{":
        raise Reject("expected the body block after _start:")
    depth, end = 0, start
    for end in range(start, len(source)):
        depth += {"{": 1, "}": -1}.get(source[end], 0)
        if depth == 0:
            break
    if source[end + 1:end + 3] != "\n}":
        raise Reject("function does not end after its body block")
    parser = Parser(tokens(source[start + 1:end]))
    body = parser.stmts()
    if parser.peek() is not None:
        raise Reject("trailing tokens in body")
    params = f'["{header.group(1)}", "{header.group(2)}"]'
    lines = ",\n    ".join(body)
    return ("{ params := " + params + "\n  body := [\n    " + lines + "] }\n")


def main(argv: list[str]) -> int:
    try:
        if argv[:1] == ["--check"]:
            _, c_file, export, lean_file = argv
            rendered = extract(Path(c_file).read_text(), export)
            text = Path(lean_file).read_text()
            match = re.search(r"-- BEGIN GENERATED AST\n(.*?)-- END GENERATED AST",
                              text, re.S)
            if not match:
                raise Reject(f"{lean_file} has no generated AST markers")
            checked_in = match.group(1)
            ast = checked_in.split(":=", 1)[1].lstrip("\n") if ":=" in checked_in else ""
            if " ".join(ast.split()) != " ".join(rendered.split()):
                print(f"error: emitted C for {export} drifted from the AST in "
                      f"{lean_file}; regenerate it and re-check the proof", file=sys.stderr)
                return 1
            print(f"generated C for {export} matches the proved AST")
            return 0
        c_file, export = argv
        sys.stdout.write(extract(Path(c_file).read_text(), export))
        return 0
    except (Reject, ValueError, OSError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
