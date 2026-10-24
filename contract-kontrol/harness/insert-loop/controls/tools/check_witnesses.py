#!/usr/bin/env python3
from pathlib import Path
import subprocess, json, re, hashlib, difflib
D=Path(__file__).resolve().parents[1]
F=21888242871839275222246405745257275088548364400416034343698204186575808495617
U=2**256
cache={}
def key(a,b):
    if (a,b) not in cache:
        inp='0x'+a.to_bytes(32,'big').hex()+b.to_bytes(32,'big').hex()
        cache[a,b]=int(subprocess.check_output(['cast','keccak',inp],text=True).strip(),16)
    return cache[a,b]
def h(a,b): return key(a,b)%F
rows=[]
for depth,level,index,leaf in [(2,0,2,11),(4,1,5,13)]:
    storage={0:9,1:17,77:177,key(88,105):188,key(leaf,2):800+leaf,key(leaf,3):0}
    for i in range(5): storage[key(i,2)]=101+i;storage[key(i,3)]=701+i
    assert len(storage)==16,'unexpected storage key collision'
    for m in [1,2,3]:
        n=leaf
        branch=[]
        stock=storage.copy();mutant=storage.copy()
        for l in range(level,depth):
            bit=(index>>l)&1
            branch.append(dict(level=l,bit=bit,node_before=n))
            if bit: n=h(stock[key(l,2)],n)
            else:
                stock[key(l,2)]=n
                mutant[0 if m==1 else key(l,3) if m==2 else key(l,2)]=n
        assert 0<=level<=depth<=256 and 128+96*(depth-level)<2**32
        assert all(0<=v<U for v in [n,index,leaf,0,level,3])
        assert ((index>>level)&1)==0 and index!=U-1
        assert 3!=2 # frame2 side condition, M=3
        if m==3:
            stock=storage.copy();mutant=storage.copy()
            for s in [stock,mutant]:s[0]=index+1;s[key(depth,2)]=n
            stock[key(leaf,3)]=index+1;mutant[key(leaf,2)]=index+1
            assert index+1<U
            watch=key(leaf,3);expected=index+1;actual=0
        else:
            watch=0 if m==1 else key(level,3)
            expected=storage[watch];actual=mutant[watch]
        assert stock[watch]==expected and actual!=expected
        assert stock!=mutant
        rows.append(dict(mutant=f'M{m}',depth=depth,level=depth if m==3 else level,index=index,leaf=leaf,
          node=n if m==3 else leaf,A5=0,SELF=0,K=level if m==2 else None,M=3 if m==2 else None,
          WS=[level,3] if m==1 else [],exact_claim_WS=[level,3] if m!=3 else None,FMP=128,FMP_bound=128+96*(depth-level) if m!=3 else None,
          initial_storage={str(k):v for k,v in sorted(storage.items())},unlisted_storage=0,
          loop_branch_trace=branch if m!=3 else [],result_node=n,
          watched_slot=watch,stock_watched=expected,mutant_watched=actual,
          stock_final_storage={str(k):v for k,v in sorted(stock.items())},
          mutant_final_storage={str(k):v for k,v in sorted(mutant.items())}))
# Check all forty native observations against the independent concrete calculation.
for run in ['stock','mutants']:
    text=(D/f'logs/{run}.log').read_text()
    lines=[line for line in text.splitlines() if 'emit Observation(' in line]
    assert len(lines)==20,(run,len(lines))
    for line in lines:
        nums={k:int(v) for k,v in re.findall(r'(mutant|depth|result|size|watched|wrongSide): (\d+)',line)}
        m=nums['mutant']%10
        row=next(r for r in rows if r['mutant']==f'M{m}' and r['depth']==nums['depth'])
        state=row['stock_final_storage' if run=='stock' else 'mutant_final_storage']
        l=0 if nums['depth']==2 else 1
        assert nums['result']==row['result_node']
        assert nums['size']==state['0']
        assert nums['watched']==state[str(key(row['leaf'] if m==3 else l,3))]
        assert nums['wrongSide']==state[str(key(row['leaf'],2))]
# The vendored sources must equal the pinned dependencies: zk-kit.solidity at the soldeer lock's rev
# (ZKKIT_DIR) and the poseidon-solidity 0.0.5 soldeer package (POSEIDON_DIR); check.sh sets both.
import os
Z=Path(os.environ['ZKKIT_DIR'])/'packages/lean-imt/contracts'
for name in ['InternalLeanIMT.sol','Constants.sol','LICENSE']:
    assert (D/'vendor/stock'/name).read_bytes()==(Z/name).read_bytes(),name
assert (D/'vendor/poseidon-solidity/PoseidonT3.sol').read_bytes()==(Path(os.environ['POSEIDON_DIR'])/'PoseidonT3.sol').read_bytes()
for tag in ['M1','M2','M3']:
    assert (D/f'vendor/{tag}/Constants.sol').read_bytes()==(Z/'Constants.sol').read_bytes()
stock=(D/'vendor/stock/InternalLeanIMT.sol').read_text()
for tag,old,new in [('M1','self.sideNodes[level] = node;','assembly { sstore(0, node) }'),
                    ('M2','self.sideNodes[level] = node;','self.leaves[level] = node;'),
                    ('M3','self.leaves[leaf] = index;','self.sideNodes[leaf] = index;')]:
    mutant=(D/f'vendor/{tag}/InternalLeanIMT.sol').read_text()
    assert mutant==stock.replace(old,new,1)
    expected=''.join(difflib.unified_diff(stock.splitlines(True),mutant.splitlines(True),fromfile='stock/InternalLeanIMT.sol',tofile=f'{tag}/InternalLeanIMT.sol'))
    assert (D/f'diffs/{tag}.patch').read_text()==expected
# Check exact runtime extraction and the archived single-byte mutations again at audit time.
def literal(name):
    text=(D.parent/'k'/f'{name}-spec.k').read_text()
    return bytes.fromhex(re.search(r'PGM ==K #parseByteStack\("0x([0-9a-f]+)"\)',text)[1])
original=literal('loop1')
for tag,name,change in [('stock','loop1',None),('M1','loop1m',(2158,32,2)),
                        ('M2','loop3m2',(2149,2,3)),('M3','loop5em3',(2209,3,2))]:
    raw=bytes.fromhex((D/f'runtime/{tag}.hex').read_text()[2:])
    assert raw==literal(name)
    differences=[(i,a,b) for i,(a,b) in enumerate(zip(original,raw)) if a!=b]
    assert len(raw)==len(original) and differences==([] if change is None else [change])
for rec in json.loads((D/'runtime/instrumentation.json').read_text()):
    raw=bytes.fromhex((D/f"runtime/{rec['tag']}.hex").read_text()[2:])
    adapted=bytes.fromhex((D/f"runtime/{rec['tag']}-{rec['mode']}.hex").read_text()[2:])
    changes=[i for i,(a,b) in enumerate(zip(raw,adapted)) if a!=b]
    assert changes==rec['changed_original_offsets']
    assert all(i<4 or rec['exit']<=i<rec['exit']+5 for i in changes)
    stop=2170 if rec['mode']=='loop' else 2228
    assert raw[rec['entry']:stop]==adapted[rec['entry']:stop]
for tag in ['stock','M1','M2','M3']:
    full=(D/f'vendor/{tag}/InternalLeanIMT.sol').read_text()
    start=full.index('        for (uint256 level = 0; level < treeDepth; ) {')
    stop=full.index('\n        self.size = ++index;',start)
    end=full.index('\n    }',stop)
    extracted=(D/f'src/Harness_{tag}.sol').read_text()
    assert full[start:stop].replace('for (uint256 level = 0;','for (;',1) in extracted
    assert full[stop:end] in extracted
(D/'witnesses.json').write_text(json.dumps(rows,indent=2)+'\n')
print('PASS: six feasible witnesses; forty source/runtime observations match concrete model.')
print('PASS: vendored sources equal the pinned dependencies; three source diffs and four extracted loop/post regions agree.')
print('PASS: archived program literals, one-byte runtime mutants, and adapter change boundaries agree.')
print('Roots:',rows[0]['result_node'],rows[3]['result_node'])
