"""Python replay (a test, not a proof): evaluate the gen_sol let chain, its segmentation,
and the common.py plain and Noir models on all 300 vector pairs against the EVM outputs.
Prints one line per model and a final JSON line; exits 1 on any mismatch."""
import json
import re

import common as c
import gen_sol

LIT = re.compile(r"\((\d+) : K\)")


def run(stmts, env):
    for l in stmts:
        m = gen_sol.LET.match(l)
        env[m.group(1)] = eval(LIT.sub(r"\1", m.group(2)), {}, env) % c.F
    return env


def main():
    c.check_sources()
    consts, body, result = gen_sol.translate(c.SOL_PATH)
    segs, last, outs = gen_sol.segment(consts, body, result)
    C, M = c.load_plain()
    rc, mds, pre, sp = c.load_noir()
    vectors = c.load_vectors()
    n = {"monolithic": 0, "segmented": 0, "plain": 0, "noir": 0}
    for a, b, o in vectors:
        env = run(body, dict(consts, a=a, b=b))
        n["monolithic"] += eval(LIT.sub(r"\1", result), {}, env) % c.F == o
        env = run(segs[0], dict(consts, a=a, b=b))
        st = [env[v] for v in outs[0]]
        for k in range(1, 64):
            env = run(segs[k], dict(consts, **dict(zip(outs[k - 1], st))))
            st = [env[v] for v in outs[k]]
        env = run(last, dict(consts, **dict(zip(outs[63], st))))
        n["segmented"] += eval(LIT.sub(r"\1", result), {}, env) % c.F == o
        n["plain"] += c.plain_perm(C, M, [0, a, b])[0] == o
        n["noir"] += c.noir_perm(rc, mds, pre, sp, [0, a, b])[0] == o
    for k, v in n.items():
        print(f"{k}: {v}/300 equal to the EVM outputs")
    print(json.dumps(n))
    raise SystemExit(0 if all(v == 300 for v in n.values()) else 1)


if __name__ == "__main__":
    main()
