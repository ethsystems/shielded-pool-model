"""Shared inputs for the hash-agreement generators.

Every input is sha256-checked on each load (inputs/PROVENANCE.md). The two upstream libraries
are not in the repo: scripts/sources.py fetches them at the pins in inputs/SOURCES.txt and
writes them to build/sources/.
- Noir tables: noir-lang/poseidon v0.3.0 `src/poseidon/bn254/consts.nr`, `x5_3_config()`,
  parsed here directly.
- Plain constants and MDS: `inputs/sol_params.json`, the hash-differential extraction from
  `PoseidonT3.sol` (trusted, reused; the Solidity round lemmas re-check every value
  against the Yul literals).
- Test vectors: `inputs/vectors/inputs.json` (300 pairs) and `sol_outputs.txt` (the EVM
  outputs of `PoseidonT3.hash` on them).
"""

import hashlib
import json
import os
import re

F = 21888242871839275222246405745257275088548364400416034343698204186575808495617

PKG = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
INPUTS = os.path.join(PKG, "inputs")
SOURCES = os.path.join(PKG, "build", "sources")
NOIR_DIR = os.path.join(SOURCES, "noir")
NOIR_SHA = {
    "mod.nr": "d0b044a17c0d7c26470137c17b7a43c172051da8ea74e56797323f3cc07a5a84",
    "bn254.nr": "4800b851b4b0e2c71cd6456efb021be865e4fde040c6e63797b6f157c042653a",
    "bn254/perm.nr": "1daf55657af0418deb717b74cd45a1a4e9ac9d59678335cf0e677ed8a682be23",
    "bn254/consts.nr": "0e1ce6ec6ed2ebbab52739ab07a2ab7a9cfb9b479cb012527f5e08447677dfd2",
}
SOL_PATH = os.path.join(SOURCES, "PoseidonT3.sol")
SOL_SHA = "08a7493be37838166954af6c77d583d797cc17d37673196498fc70cbf557831c"
PARAMS_PATH = os.path.join(INPUTS, "sol_params.json")
PARAMS_SHA = "cbca794b53c67844b9ab3cd21203f6720e291b6c8639cece18ff37b3aa01f2b8"
PLAIN_RC_SHA = "d417fc7af999d34fce76e1a216d3bbd899aca21f3f7d0c409bb2882fd9a9b218"
VECTORS_DIR = os.path.join(INPUTS, "vectors")
VECTORS_SHA = {
    "inputs.json": "ab284c7668a2ba195000a4c8eb9ca709d74dc61f27c60fa613025b1f490f0bcd",
    "sol_outputs.txt": "8acc9017447ec7f85e804858d1ccbce78723119fae4688f905a8e32fa844152f",
}

T, RF, RP = 3, 8, 57
NR = RF + RP


def sha256_file(path):
    with open(path, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()


def check_sources():
    if not os.path.isdir(SOURCES):
        raise SystemExit("build/sources/ is missing: run python3 scripts/sources.py (or ./check.sh) first")
    for rel, want in NOIR_SHA.items():
        got = sha256_file(os.path.join(NOIR_DIR, rel))
        assert got == want, f"noir/{rel}: sha256 {got} != {want}"
    got = sha256_file(SOL_PATH)
    assert got == SOL_SHA, f"PoseidonT3.sol sha256 {got} != {SOL_SHA}"
    got = sha256_file(PARAMS_PATH)
    assert got == PARAMS_SHA, f"sol_params.json sha256 {got} != {PARAMS_SHA}"
    for rel, want in VECTORS_SHA.items():
        got = sha256_file(os.path.join(VECTORS_DIR, rel))
        assert got == want, f"vectors/{rel}: sha256 {got} != {want}"


def _canon_sha(x):
    def canon(v):
        return [canon(y) for y in v] if isinstance(v, list) else str(v)
    return hashlib.sha256(json.dumps(canon(x), separators=(",", ":")).encode()).hexdigest()


def load_plain():
    """195 plain round constants (round-major, t words each) and MDS M[j][i]."""
    with open(PARAMS_PATH) as f:
        d = json.load(f)
    C = [int(x) for x in d["round_constants"]]
    M = [[int(x) for x in row] for row in d["mds"]]
    assert len(C) == T * NR and _canon_sha(C) == PLAIN_RC_SHA
    assert d["mix_convention"] == "out[i] = sum_j state[j] * M[j][i]"
    assert all(0 <= x < F for x in C) and all(0 <= x < F for r in M for x in r)
    return C, M


def _parse_nested(text):
    toks = re.findall(r"\[|\]|0x[0-9a-fA-F]+|\d+|,", text)
    stack, cur = [], []
    for t in toks:
        if t == "[":
            stack.append(cur)
            cur = []
        elif t == "]":
            done = cur
            cur = stack.pop()
            cur.append(done)
        elif t != ",":
            cur.append(int(t, 0))
    assert not stack
    return cur


def load_noir():
    """Return (rc[81], mds[3][3], presparse[3][3], sparse[285]) from x5_3_config()."""
    src = open(os.path.join(NOIR_DIR, "bn254/consts.nr")).read()
    m = re.search(r"pub fn x5_3_config\(\) -> PoseidonConfig<3, 81, 285> \{\s*config\(\s*3,\s*8,\s*57,\s*alpha\(\),(.*?)\)\s*\}", src, re.S)
    assert m, "x5_3_config not found in the expected shape"
    assert re.search(r"fn alpha\(\) -> Field \{\s*5\s*\}", src), "alpha() is not 5"
    rc, mds, pre, sparse = _parse_nested(m.group(1))
    assert len(rc) == 81 and len(sparse) == 285
    assert [len(r) for r in mds] == [3, 3, 3] and [len(r) for r in pre] == [3, 3, 3]
    for x in rc + sparse + [y for r in mds + pre for y in r]:
        assert 0 <= x < F
    return rc, mds, pre, sparse


def load_vectors():
    """300 (a, b, PoseidonT3.hash([a, b])) triples."""
    pairs = json.load(open(os.path.join(VECTORS_DIR, "inputs.json")))["pairs"]
    outs = [int(x) for x in open(os.path.join(VECTORS_DIR, "sol_outputs.txt")).read().split()]
    assert len(pairs) == len(outs) == 300
    return [(int(p["a"]), int(p["b"]), o) for p, o in zip(pairs, outs)]


# ---------- exact models (Python, for witnesses and the Python replay only) ----------

def vecmat(v, A):
    return [sum(v[j] * A[j][i] for j in range(3)) % F for i in range(3)]


def matmul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(3)) % F for j in range(3)] for i in range(3)]


def plain_round(C, M, j, s):
    s = [(x + C[3 * j + i]) % F for i, x in enumerate(s)]
    if j < RF // 2 or j >= RF // 2 + RP:
        s = [pow(x, 5, F) for x in s]
    else:
        s[0] = pow(s[0], 5, F)
    return vecmat(s, M)


def plain_perm(C, M, s):
    for j in range(NR):
        s = plain_round(C, M, j, s)
    return s


def noir_round(rc, mds, pre, sp, j, s):
    """Round j of noir `permute` (noir-lang/poseidon src/poseidon/mod.nr:49-110), cut as in README 'The round cut'."""
    sig = lambda v: [x * ((x * x) * (x * x)) % F for x in v]
    if j < 3:
        s = sig(s)
        s = [(x + rc[3 * (j + 1) + i]) % F for i, x in enumerate(s)]
        return vecmat(s, mds)
    if j == 3:
        s = sig(s)
        s = [(x + rc[12 + i]) % F for i, x in enumerate(s)]
        return vecmat(s, pre)
    if j < 61:
        r = j - 4
        s0 = (pow(s[0], 5, F) + rc[15 + r]) % F
        b = 5 * r
        new0 = (sp[b] * s0 + sp[b + 1] * s[1] + sp[b + 2] * s[2]) % F
        return [new0, (s[1] + s0 * sp[b + 3]) % F, (s[2] + s0 * sp[b + 4]) % F]
    if j < 64:
        s = sig(s)
        s = [(x + rc[72 + 3 * (j - 61) + i]) % F for i, x in enumerate(s)]
        return vecmat(s, mds)
    return vecmat(sig(s), mds)


def noir_perm(rc, mds, pre, sp, s):
    s = [(x + rc[i]) % F for i, x in enumerate(s)]
    for j in range(NR):
        s = noir_round(rc, mds, pre, sp, j, s)
    return s


# ---------- witnesses (untrusted hints; every Lean lemma re-checks them) ----------

def witnesses(C, M, rc, pre, sp):
    """Affine maps L_j x = x*Tw[j] + vw[j] for j = 4..60, plus Tw[61] = I.

    Tw[j] = A'_(j-4): backward factorization of the accumulated matrix,
    A_56 = M, A_r = A'_r * S_r, A_(r-1) = M * A'_r.
    vw is propagated forward from the Noir tables.
    """
    I = [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
    Ap = [None] * (RP + 1)
    Ap[RP] = I
    A = [row[:] for row in M]
    for r in range(RP - 1, -1, -1):
        Ap[r] = [[1, 0, 0], [0, A[1][1], A[1][2]], [0, A[2][1], A[2][2]]]
        A = matmul(M, Ap[r])
    Tw = {4 + r: Ap[r] for r in range(RP + 1)}
    assert matmul(M, Tw[4]) == pre, "P != M * A'_0"
    vw = {4: vecmat([(rc[12 + i]) for i in range(3)], pre)}
    for j in range(4, 61):
        r = j - 4
        Smat = [[sp[5 * r], sp[5 * r + 3], sp[5 * r + 4]],
                [sp[5 * r + 1], 1, 0],
                [sp[5 * r + 2], 0, 1]]
        assert matmul(Tw[j], Smat) == matmul(M, Tw[j + 1]), f"T*S != M*T' at j={j}"
        assert vw[j][0] == C[3 * j], f"v0 != c0 at j={j}"
        cT = vecmat(C[3 * j:3 * j + 3], Tw[j])
        e = [rc[15 + r], (vw[j][1] - cT[1]) % F, (vw[j][2] - cT[2]) % F]
        vw[j + 1] = vecmat(e, Smat)
    assert vw[61] == C[3 * 61:3 * 61 + 3], "v_61 != c_61"
    return Tw, vw
