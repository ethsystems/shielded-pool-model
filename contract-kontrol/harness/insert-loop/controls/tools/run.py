#!/usr/bin/env python3
from pathlib import Path
import os, subprocess, json, re, datetime, hashlib
D=Path(__file__).resolve().parents[1]
logdir=D/'logs';logdir.mkdir(exist_ok=True)
summary={}
for name,negative in [('stock',False),('mutants',True)]:
    env=os.environ.copy();env['LOOP_MUTANTS']=str(negative).lower()
    # Contain tool caches even when replayed under a different shell configuration.
    env['XDG_CACHE_HOME']=str(D/'tool-cache')
    env['FOUNDRY_DISABLE_NIGHTLY_WARNING']='1'
    cmd=['forge','test','--offline','-j','1','-vvvv']
    start=datetime.datetime.now().astimezone().isoformat()
    p=subprocess.run(cmd,cwd=D,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    (logdir/(name+'.log')).write_text(p.stdout)
    # Parse only the first suite, before the duplicate failing-test recap.
    first=p.stdout.split('Suite result:')[0]
    results=re.findall(r'^\[(PASS|FAIL)(?:: (.*?))?\] (test_\w+)\(\)',first,re.M)
    assert len(results)==21,(name,p.stdout[:1500],len(results))
    for status,reason,test in results:
        if test=='test_stub_matches_archived_runtime' or not negative:
            assert status=='PASS',(name,test,reason)
        else:
            expected=('loop-exact: sideNodes mismatch' if '_exact_' in test else
                      'loop-frame: slot 0 changed' if '_M1_' in test else
                      'loop-frame2: watched leaves key changed' if '_M2_' in test else
                      'post-loop-exact: leaves[LEAF] missing')
            assert status=='FAIL' and reason==expected,(name,test,status,reason)
    assert p.returncode==(1 if negative else 0),(name,p.returncode)
    summary[name]=dict(command=cmd,env=dict(LOOP_MUTANTS=env['LOOP_MUTANTS']),started=start,
      exit_code=p.returncode,passes=sum(x[0]=='PASS' for x in results),failures=sum(x[0]=='FAIL' for x in results),
      results=[dict(status=x,reason=y,test=z) for x,y,z in results],sha256=hashlib.sha256(p.stdout.encode()).hexdigest())
(logdir/'results.json').write_text(json.dumps(summary,indent=2)+'\n')
print('PASS: stock 21/21; mutants fail 20/20 at their specified postconditions; stub passes in both runs.')
