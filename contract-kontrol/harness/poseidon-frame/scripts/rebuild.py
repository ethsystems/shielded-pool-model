#!/usr/bin/env python3
"""Rebuild the PoseidonT3 runtime and its storage-writing mutant, and check the bytes the tests etch.

Env: POSEIDON_DIR (the poseidon-solidity 0.0.5 soldeer package, checked by check.sh), SOLC (solc
0.8.37). The source is the package's PoseidonT3.sol; the compiler settings are inputs/solc-settings.json
(the settings of the pool build: optimizer 100 runs, Osaka, the libraries and remappings, which enter
the metadata). The mutant adds `sstore(0, not(sload(0)))` before the arithmetic and drops `pure` so it
compiles. Each runtime, with the library address 0xA1002 in its call-protection slot, must equal the
hex literal of its two test files byte for byte, and the real creation code must equal the literal of
test/Deployment.t.sol. Writes results/rebuild.json (runtimes and source maps) for scripts/scan.py.
"""
import json
import os
import pathlib
import re
import subprocess

root = pathlib.Path(__file__).resolve().parent.parent
(root / "results").mkdir(exist_ok=True)
source = (pathlib.Path(os.environ["POSEIDON_DIR"]) / "PoseidonT3.sol").read_text()
settings = json.loads((root / "inputs" / "solc-settings.json").read_text())
key = "dependencies/poseidon-solidity-0.0.5/PoseidonT3.sol"
out = {}
for label in ["real", "mutant"]:
    s = source
    if label == "mutant":
        s = source.replace("public pure returns", "public returns").replace("assembly {", "assembly {\n      sstore(0, not(sload(0)))", 1)
        assert s != source
    inp = {"language": "Solidity", "sources": {key: {"content": s}},
           "settings": dict(settings, outputSelection={key: {"PoseidonT3": ["evm.bytecode.object", "evm.deployedBytecode.object", "evm.deployedBytecode.sourceMap"]}})}
    res = json.loads(subprocess.check_output([os.environ.get("SOLC", "solc"), "--standard-json"], input=json.dumps(inp).encode()))
    assert not any(e["severity"] == "error" for e in res.get("errors", [])), res.get("errors")
    c = res["contracts"][key]["PoseidonT3"]["evm"]
    code = c["deployedBytecode"]["object"]
    assert code[:42] == "73" + "00" * 20
    deployed = "73" + (0xA1002).to_bytes(20, "big").hex() + code[42:]
    for suffix in [".t.sol", "Replay.t.sol"]:
        test = (root / "test" / (label.capitalize() + suffix)).read_text()
        assert 'hex"' + deployed + '"' in test, f"{label}{suffix}: etched runtime differs from the rebuild"
    if label == "real":
        dep = (root / "test" / "Deployment.t.sol").read_text()
        assert 'hex"' + c["bytecode"]["object"] + '"' in dep, "Deployment.t.sol: creation code differs from the rebuild"
    out[label] = {"runtime": code, "deployed": deployed, "sourceMap": c["deployedBytecode"]["sourceMap"]}
    print(label, "rebuilt, equal to the etched bytes:", len(code) // 2, "bytes")
(root / "results" / "rebuild.json").write_text(json.dumps(out) + "\n")
