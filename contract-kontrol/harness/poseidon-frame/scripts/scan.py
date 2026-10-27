#!/usr/bin/env python3
"""Scan executable instructions, respecting PUSH immediates and Solidity's data fence."""
import collections,hashlib,json,pathlib,subprocess
root=pathlib.Path(__file__).resolve().parent.parent
r=json.loads((root/'results'/'rebuild.json').read_text())['real']
raw=bytes.fromhex(r['runtime'])
code=bytes.fromhex(r['deployed'])
smap=r['sourceMap']
assert code[:1]==raw[:1]==b'\x73' and code[21:]==raw[21:]
assert code[1:21]==(0xa1002).to_bytes(20,'big')
lines=subprocess.check_output(['cast','disassemble',code.hex()],text=True).splitlines()
(root/'results'/'real-deployed.disasm').write_text('\n'.join(lines)+'\n')
ins=[]
for line in lines:
 if not line.strip(): continue
 pc,op=line.split(': ',1); ins.append((int(pc,16),op.split()[0],op))
# solc provides one source-map entry per executable instruction.
bound=len(smap.split(';'))
pc,op,_=ins[bound]
assert op=='INVALID'
assert all(op!='JUMPDEST' for _,op,_ in ins[bound+1:])
# No valid jump can enter the suffix, and fall-through stops at INVALID.
counts=collections.Counter(op for _,op,_ in ins[:bound])
forbidden=['SSTORE','SLOAD','TSTORE','TLOAD','CALL','STATICCALL','DELEGATECALL','CALLCODE','CREATE','CREATE2','SELFDESTRUCT','LOG0','LOG1','LOG2','LOG3','LOG4','CALLER','ORIGIN','BALANCE','SELFBALANCE','TIMESTAMP','NUMBER','PREVRANDAO','DIFFICULTY','GASLIMIT','GASPRICE','BASEFEE','BLOBBASEFEE','BLOCKHASH','BLOBHASH','CHAINID','CALLVALUE','GAS','EXTCODESIZE','EXTCODECOPY','EXTCODEHASH']
assert all(counts[x]==0 for x in forbidden)
assert counts['ADDRESS']==1 and ins[1][0:2]==(21,'ADDRESS')
assert ins[2][1]=='EQ'
assert not any(op.startswith('UNKNOWN') for _,op,_ in ins[:bound])
report={'result':'PASS','original_runtime_sha256':hashlib.sha256(raw).hexdigest(),'deployed_runtime_sha256':hashlib.sha256(code).hexdigest(),'runtime_bytes':len(raw),'exact_rebuild':True,'executable_instructions':bound,'data_fence_pc':pc,'constant_data_start':pc+1,'metadata_start':len(raw)-2-int.from_bytes(raw[-2:],'big'),'suffix_valid_jumpdests':[],'forbidden_counts':{x:counts[x] for x in forbidden},'instruction_counts':dict(sorted(counts.items())),'suffix_misleading_instructions':[{'pc':p,'opcode':o} for p,o,_ in ins[bound+1:] if o in forbidden],'address_exception':'Library entry computes embedded-address == ADDRESS. Direct/delegate equal-result checks cover both Boolean outcomes. No other environmental read.'}
(root/'results'/'opcode-scan.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ['instruction_counts','forbidden_counts']},indent=2))
