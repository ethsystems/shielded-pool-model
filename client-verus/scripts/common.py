"""Shared helpers for the client-verus scripts: the manifest, the controls, mirror extents."""
import json
import re
from pathlib import Path

PKG = Path(__file__).resolve().parent.parent
PROOF_ERRORS = ('postcondition not satisfied', 'assertion failed', 'precondition not satisfied',
                'invariant not satisfied')
RLIMIT = 'Resource limit (rlimit) exceeded'
UNSUPPORTED = 'Verus does not yet support Opaque types in trait def'


def pins():
    out, blobs = {}, []
    for line in (PKG / 'PINS.txt').read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        k, v = line.split(' ', 1)
        if k == 'blob':
            blobs.append(tuple(v.split(' ', 1)))
        else:
            out[k] = v
    out['blobs'] = blobs
    return out


def manifest():
    return json.loads((PKG / 'source' / 'manifest.json').read_text())


def controls():
    return json.loads((PKG / 'controls' / 'controls.json').read_text())


def mirror_text(name):
    return (PKG / 'mirrors' / name).read_text()


FN = re.compile(r'^\s*(pub(\([a-z]+\))?\s+)?(async\s+)?fn\s')


def fn_extent(text, marker):
    """Line range [a, b) of the mirrored function that `marker` (unique) names. The marker is
    either the function's first line(s), possibly after an `impl` line, or a `// STRENGTH`
    comment inside its spec clauses. The function ends where its braces balance."""
    assert text.count(marker) == 1, ('marker not unique', marker)
    lines = text.splitlines(True)
    pos = text.index(marker)
    first = text[:pos].count('\n')
    last = first + marker.rstrip('\n').count('\n')
    hits = [i for i in range(first, last + 1) if FN.match(lines[i])]
    if hits:
        a = hits[0]
    else:
        a = max(i for i in range(0, first + 1) if FN.match(lines[i]))
    # The body starts at the first line that begins with `{` or ends with an open `{`; spec
    # clauses may hold balanced braces (`if c {A} else {B}`) and do not start it.
    s = next(i for i in range(a, len(lines))
             if lines[i].lstrip().startswith('{') or lines[i].rstrip().endswith('{'))
    depth = 0
    for b in range(s, len(lines)):
        depth += lines[b].count('{') - lines[b].count('}')
        if depth == 0:
            assert lines[b].rstrip().endswith('}'), ('function does not end with a brace', marker)
            return a, b + 1
    raise ValueError(marker)


def fn_text(text, marker):
    a, b = fn_extent(text, marker)
    return ''.join(text.splitlines(True)[a:b])


def strength_body(text, name):
    """Character range of the body of the function whose spec holds `// STRENGTH name`."""
    marker = '// STRENGTH ' + name + '\n'
    start = text.index('{', text.index(marker) + len(marker))
    depth, i = 1, start + 1
    while depth:
        depth += {'{': 1, '}': -1}.get(text[i], 0)
        i += 1
    return start, i


def apply_control(c):
    """The mirror text with the control's one replacement made."""
    text = mirror_text(c['mirror'])
    if c.get('within') == 'function':
        a, b = strength_body(text, c['function'])
        body = text[a:b]
        assert body.count(c['old']) == 1, (c['id'], body.count(c['old']))
        return text[:a] + body.replace(c['old'], c['new'], 1) + text[b:]
    assert text.count(c['old']) == 1, (c['id'], text.count(c['old']))
    return text.replace(c['old'], c['new'], 1)


def control_offset(c):
    """Character offset in the mirror where the control changes the text."""
    text = mirror_text(c['mirror'])
    if c.get('within') == 'function':
        a, b = strength_body(text, c['function'])
        return a + text[a:b].index(c['old'])
    return text.index(c['old'])
