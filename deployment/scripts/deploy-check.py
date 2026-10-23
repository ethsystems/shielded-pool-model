#!/usr/bin/env python3
"""Deployment check: on-chain contracts against a fresh a04b8b3 build.

Usage: deploy-check.py <ref-dir> <rpc> <claim.json>
<ref-dir> is the fresh export built with `forge build --offline --build-info`.
Chain bytes come only from the RPC; expected bytes come only from <ref-dir>.
Every expectation comes from the claim file or the exported source, never from the chain.
The claimed block may lie below the chain head (a public chain moves on): CHAIN requires the
claimed chain id and the claimed hash at the claimed block, and a head at or above that block.
Pool logs are read from block 0 in one query, or, when the claim names `logsFromBlock`, from that
block in windows of LOG_WINDOW blocks (env, default 10000; public RPCs cap the range); the pool
must then have no code at logsFromBlock - 1.
"""
import glob, hashlib, json, os, re, subprocess, sys, urllib.request

REF, RPC, CLAIM = sys.argv[1:4]
claim = json.load(open(CLAIM))
results = []


def report(name, status, why):
    results.append((name, status))
    print(f"CHECK {name} {status} {why}", flush=True)


def rpc(method, *params):
    req = urllib.request.Request(RPC, json.dumps({"jsonrpc": "2.0", "id": 1, "method": method, "params": list(params)}).encode(),
                                 {"content-type": "application/json", "user-agent": "deploy-check"})  # some RPCs refuse urllib's default agent
    r = json.load(urllib.request.urlopen(req, timeout=60))
    if "error" in r:
        raise RuntimeError(f"{method}: {r['error']}")
    return r["result"]


def addr(a):
    a = a.lower()
    assert re.fullmatch(r"0x[0-9a-f]{40}", a), a
    return a


BLOCK = hex(claim["block"])


def code_at(a):
    return bytes.fromhex(rpc("eth_getCode", a, BLOCK)[2:])


def code_at_block(a, n):
    return bytes.fromhex(rpc("eth_getCode", a, hex(n))[2:])


def keccak_sig(s):
    return subprocess.run(["cast", "keccak", s], capture_output=True, text=True, check=True).stdout.strip()


# ---- reference: the build-info of the fresh export ----
infos = glob.glob(os.path.join(REF, "contracts/out/build-info/*.json"))
if len(infos) != 1:
    sys.exit(f"REFUSE: expected one build-info in {REF}, found {len(infos)}")
bi = json.load(open(infos[0]))
src_in = bi["input"]["sources"]
mismatch = [p for p, s in src_in.items()
            if hashlib.sha256(s["content"].encode()).digest() != hashlib.sha256(open(os.path.join(REF, p), "rb").read()).digest()]
print(f"REF build-info={os.path.basename(infos[0])} solc={bi['solcLongVersion']} sources={len(src_in)} "
      f"optimizer={bi['input']['settings'].get('optimizer')} evm={bi['input']['settings'].get('evmVersion')}")
if mismatch:
    sys.exit(f"REFUSE: build-info sources differ from files in {REF}: {mismatch[:5]}")
st = bi["input"]["settings"]
# a04b8b3 foundry.toml sets optimizer and runs; evmVersion and viaIR are forge 1.8.3 defaults, enforced here.
if (bi["solcLongVersion"].split("+")[0] != "0.8.37" or st.get("optimizer") != {"enabled": True, "runs": 100}
        or st.get("evmVersion") != "osaka" or st.get("viaIR", False)):
    sys.exit(f"REFUSE: reference settings are not solc 0.8.37, optimizer on, runs 100, osaka, no viaIR: "
             f"{bi['solcLongVersion']} {st.get('optimizer')} {st.get('evmVersion')} {st.get('viaIR')}")
print(f"REF settings viaIR={st.get('viaIR', False)} evmVersion={st.get('evmVersion')} metadata={st.get('metadata')}")

ids = {}  # AST id -> variable name


def walk(n):
    if isinstance(n, dict):
        if n.get("nodeType") == "VariableDeclaration":
            ids[str(n["id"])] = n["name"]
        for v in n.values():
            walk(v)
    elif isinstance(n, list):
        for v in n:
            walk(v)


for s in bi["output"]["sources"].values():
    walk(s["ast"])

V = "contracts/src/verifiers/"
# claim key -> (source path, contract name)
CONTRACTS = {
    "pool": ("contracts/src/ShieldedPool.sol", "ShieldedPool"),
    "composite": ("contracts/src/CompositeVerifier.sol", "CompositeVerifier"),
    "registry": ("contracts/src/AttestationRegistry.sol", "AttestationRegistry"),
    "depositVerifier": (V + "DepositVerifier.sol", "HonkVerifier"),
    "transferVerifier": (V + "TransferVerifier.sol", "HonkVerifier"),
    "withdrawVerifier": (V + "WithdrawVerifier.sol", "HonkVerifier"),
    "depositTranscriptLib": (V + "DepositVerifier.sol", "ZKTranscriptLib"),
    "transferTranscriptLib": (V + "TransferVerifier.sol", "ZKTranscriptLib"),
    "withdrawTranscriptLib": (V + "WithdrawVerifier.sol", "ZKTranscriptLib"),
    "leanIMT": ("dependencies/zk-kit-v1/packages/lean-imt/contracts/LeanIMT.sol", "LeanIMT"),
    "poseidonT3": ("dependencies/poseidon-solidity-0.0.5/PoseidonT3.sol", "PoseidonT3"),
    "poseidonT5": ("dependencies/poseidon-solidity-0.0.5/PoseidonT5.sol", "PoseidonT5"),  # linked by the registry
}
LINKS = {(p, n): k for k, (p, n) in CONTRACTS.items() if n not in ("HonkVerifier", "ShieldedPool", "CompositeVerifier", "AttestationRegistry")}
MOCKS = {"MockVerifier": ("contracts/src/mocks/MockVerifier.sol", "MockVerifier"),
         "MockCompositeVerifier": ("contracts/src/mocks/MockCompositeVerifier.sol", "MockVerifier")}
ROLES = ("deposit", "transfer", "withdraw")


def ref_bytecode(path, name):
    return bi["output"]["contracts"][path][name]["evm"]["deployedBytecode"]


def source_constants(path):
    """Top-level and contract-level `uint256 [internal] constant X = expr;` from the exported source."""
    env = {}
    for m in re.finditer(r"uint256\s+(?:internal\s+)?constant\s+(\w+)\s*=\s*([^;]+);", open(os.path.join(REF, path)).read()):
        expr = m.group(2).split("//")[0].strip()
        if re.fullmatch(r"[\w\s+\-*()x<]+", expr):
            try:
                env[m.group(1)] = eval(expr, {"__builtins__": {}}, dict(env))
            except Exception:
                pass
    return env


MSM_LINE = "$MSMSize = NUMBER_UNSHIFTED_ZK + _logN + LIBRA_COMMITMENTS + 2;"


def immutable_values(key):
    """Expected value per immutable name; never read from the chain."""
    if key == "composite":
        return {f"{r}Verifier": int(addr(claim[f"{r}Verifier"]), 16) for r in ROLES}
    if key.endswith("Verifier"):
        path = CONTRACTS[key][0]
        if MSM_LINE not in open(os.path.join(REF, path)).read():
            raise RuntimeError(f"{path}: MSMSize constructor line changed")
        c = source_constants(path)
        return {"$N": c["N"], "$LOG_N": c["LOG_N"], "$VK_HASH": c["VK_HASH"], "$NUM_PUBLIC_INPUTS": c["NUMBER_OF_PUBLIC_INPUTS"],
                "$MSMSize": c["NUMBER_UNSHIFTED_ZK"] + c["LOG_N"] + c["LIBRA_COMMITMENTS"] + 2}
    return {}


def expected_code(key):
    path, name = CONTRACTS[key]
    d = ref_bytecode(path, name)
    h = list(d["object"])
    for lpath, libs in d["linkReferences"].items():
        for lname, refs in libs.items():
            lk = LINKS.get((lpath, lname))
            if lk is None:
                raise RuntimeError(f"unknown link {lpath}:{lname}")
            for r in refs:
                if r["length"] != 20 or not re.fullmatch(r"__\$[0-9a-f]{34}\$__", "".join(h[2 * r["start"]:2 * r["start"] + 40])):
                    raise RuntimeError(f"link {lname} at {r['start']}: width {r['length']} or placeholder not as expected")
                h[2 * r["start"]:2 * r["start"] + 40] = addr(claim[lk])[2:]
    code = bytearray(bytes.fromhex("".join(h)))
    vals = immutable_values(key)
    filled = set()
    for iid, refs in (d.get("immutableReferences") or {}).items():
        nm = ids.get(iid)
        if nm not in vals:
            raise RuntimeError(f"{key}: no expected value for immutable id {iid} ({nm})")
        for r in refs:
            span = set(range(r["start"], r["start"] + r["length"]))
            if r["length"] != 32 or code[r["start"]:r["start"] + 32] != bytes(32) or span & filled:
                raise RuntimeError(f"{key}: immutable {nm} at {r['start']}: width, placeholder or overlap not as expected")
            filled |= span
            code[r["start"]:r["start"] + 32] = vals[nm].to_bytes(32, "big")
    if code[:1] == b"\x73" and code[1:21] == bytes(20) and code[21:22] == b"\x30":
        code[1:21] = bytes.fromhex(addr(claim[key])[2:])  # library call protection: own address
    return bytes(code)


CBOR_KEYS = {"ipfs", "bzzr0", "bzzr1", "experimental", "solc"}


def cbor_tail(code):
    """Split code at the CBOR metadata tail named by its two-byte length suffix. Cut exactly L+2 bytes."""
    if len(code) < 2:
        raise ValueError("code shorter than the length suffix")
    L = int.from_bytes(code[-2:], "big")
    if L + 2 > len(code):
        raise ValueError(f"suffix length {L} exceeds code")
    cb = code[-(L + 2):-2]
    i = 0

    def item():
        nonlocal i
        b = cb[i]; i += 1
        mt, ai = b >> 5, b & 31
        if ai < 24:
            n = ai
        elif ai == 24:
            n = cb[i]; i += 1
        elif ai == 25:
            n = int.from_bytes(cb[i:i + 2], "big"); i += 2
        else:
            raise ValueError("unsupported CBOR length")
        if mt in (2, 3):
            v = cb[i:i + n]; i += n
            return v.decode() if mt == 3 else v
        if mt == 7 and ai in (20, 21):
            return ai == 21
        raise ValueError(f"unexpected CBOR major type {mt}")

    if not cb or cb[0] >> 5 != 5:
        raise ValueError("tail is not a CBOR map")
    n = cb[0] & 31; i = 1
    meta = {}
    for _ in range(n):
        k = item(); meta[k] = item()
    if i != len(cb) or not set(meta) <= CBOR_KEYS:
        raise ValueError(f"CBOR tail not a pure metadata map: keys={list(meta)} used={i}/{len(cb)}")
    return code[:-(L + 2)], meta


def first_diff(a, b):
    return next((i for i in range(min(len(a), len(b))) if a[i] != b[i]), min(len(a), len(b)))


# ---- checks ----
def chain_state():
    blk = rpc("eth_getBlockByNumber", BLOCK, False)
    return int(rpc("eth_chainId"), 16), int(rpc("eth_blockNumber"), 16), blk["hash"] if blk else None


cid, head, bh = chain_state()
ok = cid == claim["chainId"] and head >= claim["block"] and bh == claim["blockHash"]
report("CHAIN", "PASS" if ok else "FAIL", f"chainId={cid} head={head} hash={bh} claimed chainId={claim['chainId']} block={claim['block']} "
       f"hash={claim['blockHash']} (the RPC and its history are trusted)")
if not ok:
    print("VERDICT FAIL failing=[CHAIN] (other checks skipped: wrong chain or block)")
    sys.exit(1)

for key in CONTRACTS:
    a = addr(claim[key])
    try:
        exp = expected_code(key)
        got = code_at(a)
        if not got:
            report(f"CODE:{key}", "FAIL", f"no code at {a}")
            continue
        eb, em = cbor_tail(exp)
        gb, gm = cbor_tail(got)
        et, gt = exp[len(eb):], got[len(gb):]
    except (RuntimeError, ValueError, KeyError, IndexError) as e:
        report(f"CODE:{key}", "FAIL", f"{a}: {type(e).__name__}: {e}")
        continue
    if eb == gb:
        report(f"CODE:{key}", "PASS", f"{a} {len(gb)} bytes before metadata equal (links and immutables filled, nothing masked)")
    else:
        off = first_diff(eb, gb)
        report(f"CODE:{key}", "FAIL", f"{a} body differs: lengths expected={len(eb)} chain={len(gb)}, first difference at byte {off} "
               f"(expected {eb[off:off + 4].hex()} chain {gb[off:off + 4].hex()})")
    if et == gt:
        report(f"METADATA:{key}", "PASS", f"CBOR tail bytes equal ({len(gt)} bytes), solc {gm.get('solc', b'').hex()}")
    elif gm.get("solc") != em.get("solc"):
        report(f"METADATA:{key}", "FAIL", f"compiler differs: expected {em.get('solc', b'').hex()} chain {gm.get('solc', b'').hex()}")
    else:
        report(f"METADATA:{key}", "WARN", f"CBOR tail bytes differ, same solc: expected ipfs {em.get('ipfs', b'').hex()} chain {gm.get('ipfs', b'').hex()}")


def call(to, path, name, sig):
    sel = bi["output"]["contracts"][path][name]["evm"]["methodIdentifiers"][sig]
    out = rpc("eth_call", {"to": to, "data": "0x" + sel}, BLOCK)
    return "0x" + out[-40:]


comp = addr(claim["composite"])
vk = {r: source_constants(CONTRACTS[f"{r}Verifier"][0])["VK_HASH"] for r in ROLES}
vkoff = {}
for r in ROLES:
    d = ref_bytecode(*CONTRACTS[f"{r}Verifier"])
    vkoff[r] = next(refs[0]["start"] for iid, refs in d["immutableReferences"].items() if ids[iid] == "$VK_HASH")
slot_addr, bad = {}, []
for r in ROLES:
    try:
        a = call(comp, *CONTRACTS["composite"], f"{r}Verifier()")
    except RuntimeError as e:
        bad.append(f"{r}: call failed ({e})"); continue
    slot_addr[r] = a
    c = code_at(a)
    w = int.from_bytes(c[vkoff[r]:vkoff[r] + 32], "big") if len(c) >= vkoff[r] + 32 else None
    if w == vk[r] and a == addr(claim[f"{r}Verifier"]):
        continue
    found = [o for o in ROLES if w == vk[o]]
    bad.append(f"{r} slot -> {a} (claimed {addr(claim[r + 'Verifier'])}): VK_HASH word at {vkoff[r]} is "
               f"{'that of ' + found[0] if found else ('absent, code ' + str(len(c)) + ' bytes') if w is None else hex(w)}")
report("SLOTS", "FAIL" if bad else "PASS",
       "; ".join(bad) if bad else "deposit, transfer, withdraw slots hold the claimed verifiers with their own VK_HASH " +
       ", ".join(f"{r}={vk[r]:#066x}" for r in ROLES))

mock_bodies = {}
for mn, (p, n) in MOCKS.items():
    d = ref_bytecode(p, n)
    code = bytearray(bytes.fromhex(d["object"]))  # build-info objects carry no 0x prefix
    zero = [(x["start"], x["length"]) for refs in (d.get("immutableReferences") or {}).values() for x in refs]
    mock_bodies[mn] = (cbor_tail(bytes(code))[0], zero)


def is_mock(c):
    try:
        body = bytearray(cbor_tail(c)[0])
    except (ValueError, IndexError):
        return None
    for mn, (mb, zero) in mock_bodies.items():
        b = bytearray(body)
        for s, l in zero:  # detection only: zeroing can only add matches
            b[s:s + l] = bytes(l)
        if len(b) == len(mb) and bytes(b) == mb:
            return mn
    return None


pool = addr(claim["pool"])
pv = call(pool, *CONTRACTS["pool"], "verifier()")
targets = {"pool.verifier()": pv, **{f"composite.{r}Verifier()": a for r, a in slot_addr.items()}}
hits = [f"{t} {a} is {m}" for t, a in targets.items() if (m := is_mock(code_at(a)))]
report("MOCK", "FAIL" if hits else "PASS", "; ".join(hits) if hits else
       f"no mock code at pool.verifier() or any composite slot ({len(targets)} addresses compared with MockVerifier and MockCompositeVerifier)")

reg = call(pool, *CONTRACTS["pool"], "attestationRegistry()")
w = []
if pv != comp:
    w.append(f"pool.verifier()={pv} claimed composite {comp}")
if reg != addr(claim["registry"]):
    w.append(f"pool.attestationRegistry()={reg} claimed {addr(claim['registry'])}")
report("WIRING", "FAIL" if w else "PASS", "; ".join(w) if w else f"pool.verifier()={pv}, registry={reg}")

FROM = claim.get("logsFromBlock", 0)
logs, pre = [], (code_at_block(pool, FROM - 1) if FROM > 0 else b"")
if FROM == 0:
    logs = rpc("eth_getLogs", {"address": pool, "fromBlock": "0x0", "toBlock": BLOCK})
WINDOW = int(os.environ.get("LOG_WINDOW", "10000"))
for lo in range(FROM, claim["block"] + 1, WINDOW) if FROM > 0 else []:
    logs += rpc("eth_getLogs", {"address": pool, "fromBlock": hex(lo), "toBlock": hex(min(lo + WINDOW - 1, claim["block"]))})
T = {s.split("(")[0]: keccak_sig(s) for s in ["VerifierUpdated(address,address)", "OwnershipTransferred(address,address)",
                                              "TokenAdded(address)", "TokenRemoved(address)", "Deposit(bytes32,address,uint256,bytes)",
                                              "Withdraw(bytes32,address,address,uint256)", "AttestationRegistryUpdated(address,address)"]}
names = {v: k for k, v in T.items()}
counts = {}
for lg in logs:
    counts[names.get(lg["topics"][0], lg["topics"][0])] = counts.get(names.get(lg["topics"][0], lg["topics"][0]), 0) + 1
print(f"LOGS pool blocks {FROM}..{claim['block']}: {len(logs)} logs {counts}"
      + (f"; pool code at block {FROM - 1}: {len(pre)} bytes" if FROM > 0 else ""))
vu = [lg for lg in logs if lg["topics"][0] == T["VerifierUpdated"]]
report("EVENTS", "FAIL" if vu or pre else "PASS",
       f"pool has code at block {FROM - 1}, before logsFromBlock" if pre else
       f"{len(vu)} VerifierUpdated log(s), first in block {int(vu[0]['blockNumber'], 16)}" if vu else
       f"no VerifierUpdated log in blocks {FROM}..claimed block" + (" (no pool code before them)" if FROM > 0 else ""))

own = call(pool, *CONTRACTS["pool"], "owner()")
order = lambda x: (int(x["blockNumber"], 16), int(x["transactionIndex"], 16), int(x["logIndex"], 16))
ot = sorted((lg for lg in logs if lg["topics"][0] == T["OwnershipTransferred"]), key=order)
last = "0x" + ot[-1]["topics"][2][-40:] if ot else None
first_prev = "0x" + ot[0]["topics"][1][-40:] if ot else None
ok = own == addr(claim["owner"]) and last == own and first_prev == "0x" + "0" * 40
report("OWNER", "PASS" if ok else "FAIL", f"owner()={own} claimed={addr(claim['owner'])} OwnershipTransferred logs={len(ot)} last new owner={last}")

tok = set()
for lg in sorted(logs, key=order):
    t0 = lg["topics"][0]
    if t0 in (T["TokenAdded"], T["TokenRemoved"]):
        a = "0x" + lg["topics"][1][-40:]
        (tok.add if t0 == T["TokenAdded"] else tok.discard)(a)
want = {addr(t) for t in claim["supportedTokens"]}
on = {t: int(rpc("eth_call", {"to": pool, "data": "0x" + bi["output"]["contracts"][CONTRACTS["pool"][0]]["ShieldedPool"]["evm"]["methodIdentifiers"]["supportedTokens(address)"] + t[2:].rjust(64, "0")}, BLOCK), 16) for t in want}
ok = tok == want and all(on.values())
report("TOKENS", "PASS" if ok else "FAIL", f"from logs={sorted(tok)} claimed={sorted(want)} supportedTokens()={on}")

end = chain_state()
report("CHAIN-END", "PASS" if (end[0], end[2]) == (cid, bh) and end[1] >= head else "FAIL",
       f"chain state at end {end}, at start {(cid, head, bh)} (chain id and hash at block {claim['block']} unchanged, head not lower)")
failing = [n for n, s in results if s == "FAIL"]
warns = [n for n, s in results if s == "WARN"]
print(f"VERDICT {'FAIL' if failing else 'PASS'} failing={failing} warnings={warns}")
sys.exit(1 if failing else 0)
