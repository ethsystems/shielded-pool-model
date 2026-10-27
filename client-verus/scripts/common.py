"""Shared helpers for the client-verus scripts: the manifest, the controls, mirror extents."""
import json
import re
from pathlib import Path

PKG = Path(__file__).resolve().parent.parent
PROOF_ERRORS = ('postcondition not satisfied', 'assertion failed', 'precondition not satisfied',
                'invariant not satisfied')
RLIMIT = 'Resource limit (rlimit) exceeded'
UNSUPPORTED = 'Verus does not yet support Opaque types in trait def'
# The messages of verification errors; any other error of a control run is a compiler error.
VERIFY_ERRORS = PROOF_ERRORS + ('unable to prove post-condition of closure', 'possible arithmetic underflow/overflow', RLIMIT)


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


ANY_FN = re.compile(r'^\s*(?:pub(?:\([a-z]+\))?\s+)?(?:(?:open|closed)\s+)?(?:(?:spec|proof|exec)\s+)?'
                    r'(?:async\s+)?fn\s+(\w+)')


def fn_spans(text):
    """Every function with a body, of any mode: (first line, last line, name), 1-based and
    inclusive. A declaration that ends with `;` before any `{` has no body and no span."""
    lines = text.splitlines(True)
    out = []
    for a, line in enumerate(lines):
        m = ANY_FN.match(line)
        if not m:
            continue
        s = None
        for i in range(a, len(lines)):
            t = lines[i].rstrip()
            if lines[i].lstrip().startswith('{') or t.endswith('{'):
                s = i
                break
            if t.endswith(';'):
                break
        if s is None:
            continue
        depth = 0
        for b in range(s, len(lines)):
            depth += lines[b].count('{') - lines[b].count('}')
            if depth == 0:
                break
        out.append((a + 1, b + 1, m[1]))
    return out


def control_target(c, mutated):
    """The function of the mutated file in which the control's diagnostic must lie:
    (first line, last line, name). It is the function whose first line holds the control's
    `target` text, if it names one (a control that weakens a contract fails in its caller);
    else the function of its `// STRENGTH` marker; else the innermost function that holds the
    change."""
    spans = fn_spans(mutated)
    lines = mutated.splitlines(True)
    if 'target' in c:
        hit = [s for s in spans if c['target'] in lines[s[0] - 1]]
    elif 'function' in c:
        marker = '// STRENGTH ' + c['function'] + '\n'
        assert mutated.count(marker) == 1, (c['id'], 'marker')
        line = mutated[:mutated.index(marker)].count('\n') + 1
        hit = sorted((s for s in spans if s[0] <= line <= s[1]), key=lambda s: s[1] - s[0])[:1]
    else:
        line = mutated[:control_offset(c)].count('\n') + 1
        hit = sorted((s for s in spans if s[0] <= line <= s[1]), key=lambda s: s[1] - s[0])[:1]
    assert len(hit) == 1, (c['id'], 'target', hit)
    return hit[0]
