#!/usr/bin/env python3
"""Check that every C device-program profile equals the Lean policy it names (issue #642).

The kernel and the Qotom lab kernel admit a device program's declared policy
against C copies of the policies in `LeanOS/DeviceProgramConfinement.lean`:

* `static const struct wifi_policy NAME = { ... };` in `boot/kernel.c`;
* the entries of `lab_dev_profiles[]` in `hardware/lab/qotom-wifi.c.inc`.

Each profile's comment names its Lean policy in backticks (for example
"Mirrors `qotomAhciPolicy`"). This script evaluates every such initializer
and requires each field to equal that policy's, as printed by
`leanos-device-policies`: the window, both configuration bitmaps, both
command masks, DMA, the address sinks and the descriptor map. The profile
must be present, its sink and descriptor counts within the executor's limits,
and any array entries past the counts zero. A profile that names no policy,
or more than one, fails.

usage: check-device-policies.py POLICIES_FILE [C_SOURCE...]
  POLICIES_FILE is the output of `.lake/build/bin/leanos-device-policies`;
  the C sources default to boot/kernel.c and hardware/lab/qotom-wifi.c.inc.
"""
import ast
import re
import sys
from pathlib import Path

MAX_SINKS = 8      # WIFI_MAX_SINKS (hardware/wifi/wifi-exec.h)
MAX_DESCS = 16     # WIFI_MAX_DESCS
DEFAULT_SOURCES = ['boot/kernel.c', 'hardware/lab/qotom-wifi.c.inc']


class CheckError(Exception):
    pass


def parse_policies(text):
    """NAME -> dict of the Lean policy's fields."""
    out = {}
    for line in text.splitlines():
        if not line.strip():
            continue
        name, *fields = line.split()
        kv = dict(f.split('=', 1) for f in fields)
        num = lambda k: int(kv[k], 16)
        sinks = [] if kv['sinks'] == '-' else [int(x, 16) for x in kv['sinks'].split(',')]
        descs = [] if kv['descs'] == '-' else [
            tuple(int(p, 16) for p in d.split(':')) for d in kv['descs'].split(',')]
        out[name] = {
            'window': num('window'), 'cfg_read': num('cfgRead'), 'cfg_write': num('cfgWrite'),
            'cmd_clear': num('cmdClear'), 'cmd_set': num('cmdSet'), 'dma': num('dma'),
            'sinks': sinks, 'descs': descs,
        }
    if not out:
        raise CheckError('no Lean policies in the policies file')
    return out


# ---------------------------------------------------------------- C side

_TOKEN = re.compile(r'\s*(?:(0[xX][0-9a-fA-F]+|\d+)[uUlL]*|(UINT(?:32|64)_C)\s*\(|(<<|>>|[|&^+*/()-]))')


def c_value(expr):
    """Evaluate a constant C integer expression of the forms the profiles use."""
    pos, py = 0, []
    expr = expr.strip()
    while pos < len(expr):
        m = _TOKEN.match(expr, pos)
        if not m or m.end() == pos:
            raise CheckError(f'cannot evaluate C expression {expr!r}')
        num, wrap, op = m.groups()
        if num is not None:
            py.append(str(int(num, 0)))
        elif wrap is not None:
            py.append('(')
        else:
            py.append('//' if op == '/' else op)
        pos = m.end()
    tree = ast.parse(' '.join(py), mode='eval')
    allowed = (ast.Expression, ast.BinOp, ast.Constant, ast.BitOr, ast.BitAnd, ast.BitXor,
               ast.LShift, ast.RShift, ast.Add, ast.Sub, ast.Mult, ast.FloorDiv,
               ast.UnaryOp, ast.USub)
    for node in ast.walk(tree):
        if not isinstance(node, allowed):
            raise CheckError(f'unsupported construct in C expression {expr!r}')
    return eval(compile(tree, '<c>', 'eval'), {'__builtins__': {}})


def strip_comments(text):
    return re.sub(r'/\*.*?\*/', ' ', text, flags=re.S)


def split_top(body):
    """Split a brace body at its top-level commas (braces nest)."""
    parts, depth, cur = [], 0, ''
    for ch in body:
        if ch == '{':
            depth += 1
        elif ch == '}':
            depth -= 1
        if ch == ',' and depth == 0:
            parts.append(cur.strip())
            cur = ''
        else:
            cur += ch
    if cur.strip():
        parts.append(cur.strip())
    return parts


def unbrace(s):
    s = s.strip()
    if not (s.startswith('{') and s.endswith('}')):
        raise CheckError(f'expected a braced initializer, got {s[:60]!r}')
    return s[1:-1]


def matching(text, i):
    """Index of the brace matching the '{' at text[i], skipping comments."""
    depth, j = 0, i
    while j < len(text):
        if text.startswith('/*', j):
            j = text.index('*/', j) + 2
            continue
        if text[j] == '{':
            depth += 1
        elif text[j] == '}':
            depth -= 1
            if depth == 0:
                return j
        j += 1
    raise CheckError('unbalanced braces')


def policy_fields(init):
    """The fields of a `struct wifi_policy` initializer (wifi-exec.h order)."""
    items = split_top(unbrace(strip_comments(init)))
    if len(items) != 11:
        raise CheckError(f'a struct wifi_policy initializer has {len(items)} fields, expected 11')
    (present, dma, window, cfg_read, cfg_write, cmd_clear, cmd_set,
     sink_count, sinks, desc_count, descs) = items
    sink_vals = [c_value(x) for x in split_top(unbrace(sinks))]
    desc_vals = [tuple(c_value(y) for y in split_top(unbrace(d))) for d in split_top(unbrace(descs))]
    for d in desc_vals:
        if len(d) != 4:
            raise CheckError(f'a descriptor initializer has {len(d)} fields, expected 4')
    return {
        'present': c_value(present), 'dma': c_value(dma), 'window': c_value(window),
        'cfg_read': c_value(cfg_read), 'cfg_write': c_value(cfg_write),
        'cmd_clear': c_value(cmd_clear), 'cmd_set': c_value(cmd_set),
        'sink_count': c_value(sink_count), 'sink_init': sink_vals,
        'desc_count': c_value(desc_count), 'desc_init': desc_vals,
    }


def named_policy(comment, known, where):
    names = sorted({n for n in re.findall(r'`([A-Za-z0-9_]+)`', comment) if n in known})
    if len(names) != 1:
        raise CheckError(f'{where}: its comment must name exactly one Lean policy in backticks, '
                         f'found {names or "none"}')
    return names[0]


def last_comment(text):
    found = re.findall(r'/\*.*?\*/', text, flags=re.S)
    return found[-1] if found else ''


def profiles(path, text, known):
    """(where, Lean policy name, C fields) for every profile in one source."""
    out = []
    for m in re.finditer(r'static\s+const\s+struct\s+wifi_policy\s+(\w+)\s*=\s*\{', text):
        start = m.end() - 1
        init = text[start:matching(text, start) + 1]
        line = text.count('\n', 0, m.start()) + 1
        where = f'{path}:{line} ({m.group(1)})'
        # The comment just before the definition (only whitespace between).
        before = text[:m.start()].rstrip()
        comment = last_comment(before) if before.endswith('*/') else ''
        out.append((where, named_policy(comment, known, where), policy_fields(init)))
    for m in re.finditer(r'static\s+const\s+struct\s+lab_dev_profile\s+(\w+)\s*\[\s*\]\s*=\s*\{', text):
        start = m.end() - 1
        end = matching(text, start)
        j = start + 1
        comment = ''
        while j < end:
            if text.startswith('/*', j):
                k = text.index('*/', j) + 2
                comment = text[j:k]
                j = k
            elif text[j] == '{':
                k = matching(text, j)
                entry = split_top(unbrace(strip_comments(text[j:k + 1])))
                line = text.count('\n', 0, j) + 1
                where = f'{path}:{line} ({m.group(1)} entry)'
                if len(entry) != 5:
                    raise CheckError(f'{where}: a lab profile has {len(entry)} fields, expected 5')
                out.append((where, named_policy(comment, known, where), policy_fields(entry[4])))
                comment = ''
                j = k + 1
            else:
                j += 1
    return out


def compare(where, name, c, lean):
    errors = []
    if c['present'] != 1:
        errors.append(f'present is {c["present"]}, expected 1')
    for field in ('dma', 'window', 'cfg_read', 'cfg_write', 'cmd_clear', 'cmd_set'):
        if c[field] != lean[field]:
            errors.append(f'{field} is {c[field]:#x}, {name} has {lean[field]:#x}')
    n, init = c['sink_count'], c['sink_init']
    if n > MAX_SINKS or len(init) > MAX_SINKS:
        errors.append(f'{n} sinks ({len(init)} initialized), the executor allows {MAX_SINKS}')
    elif init[:n] + [0] * (n - len(init)) != lean['sinks'] or any(init[n:]):
        errors.append(f'sinks are {[hex(x) for x in init[:n]]} (count {n}), '
                      f'{name} has {[hex(x) for x in lean["sinks"]]}')
    n, init = c['desc_count'], c['desc_init']
    if n > MAX_DESCS or len(init) > MAX_DESCS:
        errors.append(f'{n} descriptors ({len(init)} initialized), the executor allows {MAX_DESCS}')
    elif init[:n] != lean['descs'] or any(any(d) for d in init[n:]):
        errors.append(f'descriptors are {init[:n]} (count {n}), {name} has {lean["descs"]}')
    return [f'{where}: mirrors {name}, but {e}' for e in errors]


def check(policies_text, sources):
    known = parse_policies(policies_text)
    errors, count = [], 0
    for path in sources:
        text = Path(path).read_text()
        found = profiles(path, text, known)
        if not found:
            raise CheckError(f'{path}: no device-program profiles found')
        for where, name, fields in found:
            count += 1
            errors += compare(where, name, fields, known[name])
    return count, errors


def main(argv):
    if len(argv) < 2:
        print(__doc__, file=sys.stderr)
        return 2
    sources = argv[2:] or DEFAULT_SOURCES
    try:
        count, errors = check(Path(argv[1]).read_text(), sources)
    except CheckError as e:
        print(f'error: {e}', file=sys.stderr)
        return 1
    for e in errors:
        print(f'error: {e}', file=sys.stderr)
    if errors:
        return 1
    print(f'device-program profiles: {count} C profiles equal the Lean policies they name')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
