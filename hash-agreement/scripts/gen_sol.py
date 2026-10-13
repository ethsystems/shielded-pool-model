"""Translate inputs/PoseidonT3.sol (poseidon-solidity 0.0.5) into a Lean term over ZMod F.

Accepted constructs only (anything else raises):
  header: pragma/license/library/comment lines, `uint constant Mij = <hex>;`,
          `function hash(uint[2] memory) public pure returns (uint) {`, `assembly {`
  `let F := <literal>`              checked equal to F, then dropped
  `let x := e` / `x := e`           -> Lean `let x := e`
  `mstore(0x0, e)`                  -> the result
  `return(0, 0x20)`                 must directly follow the mstore
  closing braces
Expressions: mulmod(a,b,F) -> (a * b); add(a,b) -> (a + b); mod(e,F) -> e;
mload(0x80) -> a; mload(0xa0) -> b; decimal/hex literals; Mij names.
The field reading of `add` assumes no uint256 wrap. The hash-differential record bounds
every `add` statically below 3.998 p (inputs/PROVENANCE.md); nothing here proves it.

The second half cuts the same statement list into 65 segments at the 64 mix blocks
(`segment`, `lean_seg_block`). No statement changes; only the cut points and the
input/output variable names are added.
"""

import re
import sys

import common as c

TOK = re.compile(r"\s*(mulmod|add|mod|mload|0x[0-9a-fA-F]+|\d+|[A-Za-z_][A-Za-z0-9_]*|\(|\)|,)")


def tokenize(s):
    out, pos = [], 0
    s = s.rstrip()
    while pos < len(s):
        m = TOK.match(s, pos)
        if not m:
            raise SystemExit(f"cannot tokenize at: {s[pos:]!r}")
        out.append(m.group(1))
        pos = m.end()
    return out


class Expr:
    def __init__(self, toks, consts, vars_):
        self.t, self.i, self.consts, self.vars = toks, 0, consts, vars_

    def eat(self, x=None):
        tok = self.t[self.i]
        if x is not None and tok != x:
            raise SystemExit(f"expected {x!r}, got {tok!r}")
        self.i += 1
        return tok

    def parse(self):
        tok = self.eat()
        if tok in ("mulmod", "add", "mod"):
            self.eat("(")
            a = self.parse()
            self.eat(",")
            b = self.parse()
            if tok == "mulmod":
                self.eat(",")
                if self.eat() != "F":
                    raise SystemExit("mulmod modulus is not F")
            self.eat(")")
            if tok == "mulmod":
                return f"({a} * {b})"
            if tok == "add":
                return f"({a} + {b})"
            if b != "F":
                raise SystemExit("mod by something other than F")
            return a
        if tok == "mload":
            self.eat("(")
            addr = self.eat()
            self.eat(")")
            return {"0x80": "a", "0xa0": "b"}[addr]
        if tok == "F":
            return "F"
        if re.fullmatch(r"0x[0-9a-fA-F]+|\d+", tok):
            v = int(tok, 0)
            if not v < 2 ** 256:
                raise SystemExit("literal out of range")
            return f"({v} : K)"
        if tok in self.consts:
            return tok
        if tok in self.vars:
            return tok
        raise SystemExit(f"unknown name {tok!r}")

    def done(self):
        if self.i != len(self.t):
            raise SystemExit(f"trailing tokens {self.t[self.i:]}")


def translate(path):
    lines = open(path).read().splitlines()
    consts, vars_, body, result = {}, set(), [], None
    in_asm = False
    pending_return = False
    for n, raw in enumerate(lines, 1):
        s = raw.strip()
        if not s or s.startswith("//") or s.startswith("///"):
            continue
        if pending_return:
            if s != "return(0, 0x20)":
                raise SystemExit(f"line {n}: expected return(0, 0x20)")
            pending_return = False
            continue
        if not in_asm:
            m = re.fullmatch(r"uint constant (M[0-2][0-2]) = (0x[0-9a-fA-F]+);", s)
            if m:
                consts[m.group(1)] = int(m.group(2), 16)
                continue
            if s in ("pragma solidity >=0.7.0;", "library PoseidonT3 {",
                     "function hash(uint[2] memory) public pure returns (uint) {"):
                continue
            if s == "assembly {":
                in_asm = True
                continue
            raise SystemExit(f"line {n}: unexpected header {s!r}")
        if s == "}":
            continue
        m = re.fullmatch(r"let F := (\d+)", s)
        if m:
            if int(m.group(1)) != c.F:
                raise SystemExit("F literal differs")
            continue
        m = re.fullmatch(r"(let )?([A-Za-z_][A-Za-z0-9_]*) := (.*)", s)
        if m:
            name, rhs = m.group(2), m.group(3)
            # multi-line expressions: join following lines until parentheses balance
            k = n
            while rhs.count("(") != rhs.count(")"):
                rhs += lines[k].strip()
                lines[k] = ""
                k += 1
            m2 = re.fullmatch(r"(0x[0-9a-fA-F]+|\d+)", rhs.strip())
            if m.group(1) and m2 and re.fullmatch(r"M[0-2][0-2]", name):
                consts[name] = int(m2.group(1), 0)
                continue
            e = Expr(tokenize(rhs), consts, vars_)
            lean = e.parse()
            e.done()
            if not m.group(1) and name not in vars_:
                raise SystemExit(f"line {n}: assignment to undeclared {name}")
            vars_.add(name)
            body.append(f"  let {name} := {lean}")
            continue
        m = re.fullmatch(r"mstore\(0x0, (.*)\)", s)
        if m:
            e = Expr(tokenize(m.group(1)), consts, vars_)
            result = e.parse()
            e.done()
            pending_return = True
            continue
        raise SystemExit(f"line {n}: unexpected statement {s!r}")
    if result is None or pending_return:
        raise SystemExit("no mstore/return at the end")
    assert sorted(consts) == [f"M{i}{j}" for i in range(3) for j in range(3)]
    return consts, body, result


def lean_block(consts, body, result):
    out = ["-- SOL: generated by gen_sol.py from inputs/PoseidonT3.sol (sha256 %s)" % c.SOL_SHA]
    for k in sorted(consts):
        out.append(f"def Sol{k} : K := {consts[k]}")
    out.append("set_option maxRecDepth 100000 in")
    out.append("def solHash (a b : K) : K :=")
    for k in sorted(consts):
        out.append(f"  let {k} := Sol{k}")
    out += body
    out.append(f"  {result}")
    return "\n".join(out) + "\n"


if __name__ == "__main__":
    c.check_sources()
    consts, body, result = translate(c.SOL_PATH)
    sys.stdout.write(lean_block(consts, body, result))


# ---------- the same statements cut into 65 rounds at the mix blocks ----------

MIXCOL = re.compile(r"\* M[0-2]([0-2])\)")
LET = re.compile(r"  let (\w+) := (.*)")


def segment(consts, body, result):
    """Cut the let chain after each 3-line mix block. Returns (segs[0..63], last, outs).
    Each segment keeps the source statements in order; only the cut points and the
    input/output variable names are added. Checks that every read is defined."""
    mix = [i for i, l in enumerate(body) if MIXCOL.search(l)]
    blocks = [mix[i:i + 3] for i in range(0, len(mix), 3)]
    assert len(blocks) == 64 and all(b == list(range(b[0], b[0] + 3)) for b in blocks)
    outs = []
    for b in blocks:
        words = {}
        for i in b:
            name = LET.match(body[i]).group(1)
            cols = set(MIXCOL.findall(body[i]))
            assert len(cols) == 1, body[i]
            words[int(cols.pop())] = name
        outs.append([words[0], words[1], words[2]])
    cuts = [-1] + [b[-1] for b in blocks]
    segs = [body[cuts[k] + 1:cuts[k + 1] + 1] for k in range(64)]
    last = body[cuts[64] + 1:]
    names = set(consts)

    def check(stmts, inputs, tail_expr=None):
        defined = set(inputs) | names
        for l in stmts:
            m = LET.match(l)
            for v in re.findall(r"\b(state\d|scratch\d|a|b)\b", m.group(2)):
                assert v in defined, (v, l)
            defined.add(m.group(1))
        if tail_expr:
            for v in re.findall(r"\b(state\d|scratch\d)\b", tail_expr):
                assert v in defined
        return defined

    check(segs[0], ["a", "b"])
    for k in range(1, 64):
        check(segs[k], outs[k - 1])
    check(last, outs[63], result)
    return segs, last, outs


def lean_seg_block(consts, body, result):
    segs, last, outs = segment(consts, body, result)
    mlets = "".join(f"  let {k} := Sol{k}\n" for k in sorted(consts))
    out = ["-- SOLSEG: the SOL statements cut at the 64 mix blocks (no statement changed)"]
    out.append("def solR0 (a b : K) : St :=\n" + mlets + "\n".join(segs[0]) +
               f"\n  ({outs[0][0]}, {outs[0][1]}, {outs[0][2]})\n")
    for k in range(1, 64):
        i0, i1, i2 = outs[k - 1]
        o0, o1, o2 = outs[k]
        out.append(f"def solR{k} (s : St) : St :=\n" + mlets +
                   f"  let {i0} := s.1\n  let {i1} := s.2.1\n  let {i2} := s.2.2\n" +
                   "\n".join(segs[k]) + f"\n  ({o0}, {o1}, {o2})\n")
    i0, i1, i2 = outs[63]
    out.append("def solLast (s : St) : K :=\n" + mlets +
               f"  let {i0} := s.1\n  let {i1} := s.2.1\n  let {i2} := s.2.2\n" +
               "\n".join(last) + ("\n" if last else "") + f"  {result}\n")
    nest = "solR0 a b"
    for k in range(1, 64):
        nest = f"solR{k} ({nest})"
    out.append(f"def solHashSeg (a b : K) : K := solLast ({nest})\n")
    return "\n".join(out)
