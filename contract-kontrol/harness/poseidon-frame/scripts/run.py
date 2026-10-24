#!/usr/bin/env python3
import datetime,json,os,pathlib,resource,subprocess,sys,time
label,contract=sys.argv[1:3]
args=sys.argv[3:]
root=pathlib.Path(__file__).resolve().parent.parent
os.chdir(root)
cmd=[os.environ.get('HALMOS', 'halmos'),'--contract',contract,'--storage-layout','generic','--solver-threads','1','--solver-command',os.environ.get('YICES', 'yices-smt2'),'--solver-timeout-assertion','60s','--json-output',f'results/{label}.json','--no-status']+args
start=datetime.datetime.now().astimezone().isoformat(); t=time.monotonic()
env=dict(os.environ,TMPDIR=str(root/'results'),FOUNDRY_LINT_LINT_ON_BUILD='false')
def limits():
 resource.setrlimit(resource.RLIMIT_CORE,(0,0))
 resource.setrlimit(resource.RLIMIT_AS,(2500*1024**2,2500*1024**2))
with open(f'results/{label}.log','w') as f:
 f.write('COMMAND '+repr(cmd)+'\n');f.flush()
 try:
  rc=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT,env=env,preexec_fn=limits,timeout=600).returncode
 except subprocess.TimeoutExpired:
  rc=124
r={'start':start,'end':datetime.datetime.now().astimezone().isoformat(),'wall_seconds':time.monotonic()-t,'exit_code':rc,'max_rss_kib':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,'command':cmd}
pathlib.Path(f'results/{label}.run.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
sys.exit(0 if rc==0 else 1)
