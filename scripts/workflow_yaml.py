#!/usr/bin/env python3
"""Small, dependency-free YAML loader for the GitHub workflow subset.

The loader deliberately implements YAML 1.2 core scalars so keys such as
``on`` remain strings.  It rejects anchors, aliases, tags, duplicate mapping
keys, tabs used for indentation, and constructs outside the repository's
workflow subset instead of guessing at their meaning.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import re
from typing import Any


class WorkflowYamlError(ValueError):
    """Raised when a workflow is outside the supported structural subset."""


@dataclass(frozen=True)
class _Line:
    number: int
    indent: int
    text: str


_INTEGER = re.compile(r"-?(?:0|[1-9][0-9]*)$")


def _split_mapping(text: str, number: int) -> tuple[str, str]:
    quote: str | None = None
    for index, char in enumerate(text):
        if char in "'\"":
            if quote is None:
                quote = char
            elif quote == char:
                quote = None
        elif char == ":" and quote is None:
            key = text[:index].strip()
            if not key:
                raise WorkflowYamlError(f"line {number}: empty mapping key")
            return key, text[index + 1 :].strip()
    raise WorkflowYamlError(f"line {number}: expected a mapping entry")


def _flow_sequence(value: str, number: int) -> list[Any]:
    body = value[1:-1].strip()
    if not body:
        return []
    items: list[str] = []
    start = 0
    quote: str | None = None
    for index, char in enumerate(body):
        if char in "'\"":
            if quote is None:
                quote = char
            elif quote == char:
                quote = None
        elif char == "," and quote is None:
            items.append(body[start:index].strip())
            start = index + 1
    if quote is not None:
        raise WorkflowYamlError(f"line {number}: unterminated quoted scalar")
    items.append(body[start:].strip())
    if any(not item for item in items):
        raise WorkflowYamlError(f"line {number}: empty flow-sequence item")
    return [_scalar(item, number) for item in items]


def _scalar(value: str, number: int) -> Any:
    if value.startswith(("&", "*", "!")):
        raise WorkflowYamlError(
            f"line {number}: anchors, aliases, and tags are unsupported"
        )
    if value.startswith("["):
        if not value.endswith("]"):
            raise WorkflowYamlError(f"line {number}: unterminated flow sequence")
        return _flow_sequence(value, number)
    if len(value) >= 2 and value[0] == value[-1] and value[0] in "'\"":
        if value[0] == "'":
            return value[1:-1].replace("''", "'")
        return bytes(value[1:-1], "utf-8").decode("unicode_escape")
    if value in ("true", "false"):
        return value == "true"
    if value in ("null", "~"):
        return None
    if _INTEGER.fullmatch(value):
        return int(value)
    return value


class _Parser:
    def __init__(self, source: str):
        self.raw = source.splitlines()
        self.lines: list[_Line] = []
        for number, raw in enumerate(self.raw, 1):
            if "\t" in raw[: len(raw) - len(raw.lstrip())]:
                raise WorkflowYamlError(f"line {number}: tab indentation is forbidden")
            stripped = raw.lstrip(" ")
            if not stripped or stripped.startswith("#") or stripped == "---":
                continue
            self.lines.append(_Line(number, len(raw) - len(stripped), stripped))

    def parse(self) -> dict[str, Any]:
        if not self.lines:
            raise WorkflowYamlError("workflow is empty")
        value, index = self._node(0, self.lines[0].indent)
        if index != len(self.lines) or not isinstance(value, dict):
            raise WorkflowYamlError("workflow root must be a mapping")
        return value

    def _node(self, index: int, indent: int) -> tuple[Any, int]:
        if self.lines[index].indent != indent:
            raise WorkflowYamlError(
                f"line {self.lines[index].number}: inconsistent indentation"
            )
        if self.lines[index].text.startswith("- "):
            return self._sequence(index, indent)
        return self._mapping(index, indent)

    def _mapping(self, index: int, indent: int) -> tuple[dict[str, Any], int]:
        result: dict[str, Any] = {}
        while index < len(self.lines):
            line = self.lines[index]
            if line.indent < indent:
                break
            if line.indent != indent or line.text.startswith("- "):
                raise WorkflowYamlError(f"line {line.number}: inconsistent mapping indentation")
            key, raw_value = _split_mapping(line.text, line.number)
            key_value = _scalar(key, line.number)
            if not isinstance(key_value, str):
                raise WorkflowYamlError(f"line {line.number}: mapping key must be a string")
            if key_value in result:
                raise WorkflowYamlError(f"line {line.number}: duplicate key {key_value!r}")
            index += 1
            if raw_value in ("|", "|-", "|+", ">", ">-", ">+"):
                value, index = self._block(index, line.indent, raw_value.startswith(">"))
            elif raw_value:
                value = _scalar(raw_value, line.number)
            elif index < len(self.lines) and self.lines[index].indent > indent:
                value, index = self._node(index, self.lines[index].indent)
            else:
                value = None
            result[key_value] = value
        return result, index

    def _sequence(self, index: int, indent: int) -> tuple[list[Any], int]:
        result: list[Any] = []
        while index < len(self.lines):
            line = self.lines[index]
            if line.indent < indent:
                break
            if line.indent != indent or not line.text.startswith("- "):
                break
            item = line.text[2:].strip()
            index += 1
            if not item:
                if index >= len(self.lines) or self.lines[index].indent <= indent:
                    raise WorkflowYamlError(f"line {line.number}: empty sequence item")
                value, index = self._node(index, self.lines[index].indent)
            elif ":" in item:
                key, raw_value = _split_mapping(item, line.number)
                key_value = _scalar(key, line.number)
                if not isinstance(key_value, str):
                    raise WorkflowYamlError(f"line {line.number}: mapping key must be a string")
                if raw_value in ("|", "|-", "|+", ">", ">-", ">+"):
                    item_value, index = self._block(
                        index, line.indent, raw_value.startswith(">")
                    )
                else:
                    item_value = _scalar(raw_value, line.number) if raw_value else None
                value = {key_value: item_value}
                if index < len(self.lines) and self.lines[index].indent > indent:
                    continuation, index = self._mapping(index, self.lines[index].indent)
                    overlap = value.keys() & continuation.keys()
                    if overlap:
                        duplicate = next(iter(overlap))
                        raise WorkflowYamlError(f"line {line.number}: duplicate key {duplicate!r}")
                    value.update(continuation)
            else:
                value = _scalar(item, line.number)
            result.append(value)
        return result, index

    def _block(self, index: int, parent_indent: int, folded: bool) -> tuple[str, int]:
        start = index
        while index < len(self.lines) and self.lines[index].indent > parent_indent:
            index += 1
        if start == index:
            return "", index
        block_indent = min(line.indent for line in self.lines[start:index])
        pieces = [line.text if line.indent == block_indent else " " * (line.indent - block_indent) + line.text for line in self.lines[start:index]]
        return ((" " if folded else "\n").join(pieces) + "\n"), index


def load_workflow(path: Path) -> dict[str, Any]:
    """Load one repository workflow using the fail-closed YAML subset."""

    try:
        return _Parser(path.read_text(encoding="utf-8")).parse()
    except OSError as error:
        raise WorkflowYamlError(f"cannot read {path}: {error}") from error
