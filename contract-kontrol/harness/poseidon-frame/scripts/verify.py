#!/usr/bin/env python3
import json,os,pathlib,subprocess,sys
root=pathlib.Path(__file__).resolve().parent.parent
os.chdir(root)
(root/'results').mkdir(exist_ok=True)
def run(cmd, logfile=None, expected=0):
 if logfile:
  with open('results/'+logfile,'w') as f:
   rc=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT).returncode
 else:
  rc=subprocess.run(cmd).returncode
 assert rc==expected,(cmd,rc,expected)
run([sys.executable,'scripts/rebuild.py'],'rebuild-check.txt')
run([sys.executable,'scripts/scan.py'],'opcode-scan.txt')
run(['forge','build','--force','--offline'],'build.log')
run([sys.executable,'scripts/run.py','real-final','RealFrame','--match-test','^check_(frame_equal_inputs|call_context_same_result|wrong_selector)','--solver-timeout-branching','100ms'])
run([sys.executable,'scripts/run.py','short-calldata','RealFrame','--match-test','^check_short_calldata','--default-bytes-lengths',','.join(map(str,range(68))),'--solver-timeout-branching','100ms'])
run([sys.executable,'scripts/run.py','mutant-witness','MutantFrame','--match-test','^check_mutant_witness','--dump-smt-queries','--dump-smt-directory','results/mutant-witness-smt'],expected=1)
run(['forge','test','--match-contract','^DeploymentTest$','-vv'],'deployment.log')
run(['forge','test','--match-path','test/*Replay.t.sol','-vvvv'],'concrete-replay.log',expected=1)
expected={'real-final':3,'short-calldata':1,'mutant-witness':1}
summary={}
for label,count in expected.items():
 j=json.loads(pathlib.Path(f'results/{label}.json').read_text())
 rows=[r for a in j['test_results'].values() for r in a]
 assert len(rows)==count
 for r in rows:
  assert r['exitcode']==(1 if label=='mutant-witness' else 0)
  assert r['num_bounded_loops']==0
  assert r['num_paths'][0]>0
  if label=='mutant-witness':
   assert r['num_models']>0 and all(m['is_valid'] for m in r['models'])
 summary[label]=[{k:r[k] for k in ['name','exitcode','num_paths','num_models','num_bounded_loops']} for r in rows]
s=pathlib.Path('results/concrete-replay.log').read_text()
assert '[PASS] test_concrete_frame()' in s and '[FAIL: panic: assertion failed (0x01)] test_concrete_frame()' in s
assert '0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff' in s
assert '[PASS] test_constructor_runtime()' in pathlib.Path('results/deployment.log').read_text()
pathlib.Path('results/verification.json').write_text(json.dumps(summary,indent=2)+'\n')
print('VERIFY PASS: four real symbolic properties, one satisfiable mutant failure, native replay, and constructor identity.')
