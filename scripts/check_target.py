#!/usr/bin/env python3
"""Compile the expanded intended statement against explicitly selected objects."""
from pathlib import Path
import argparse,json,subprocess
from common import ROOT,check_sources,environment

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--objects',type=Path,default=ROOT/'.cycle12-build/lib/lean');ap.add_argument('--lean');ap.add_argument('--packages',type=Path);ap.add_argument('--audit-bodies',action='store_true');ap.add_argument('--report-dir',type=Path,default=ROOT/'.cycle12-check');args=ap.parse_args()
    check_sources();lean,env=environment(args.lean,args.packages,args.objects)
    out=args.report_dir.resolve();out.mkdir(parents=True,exist_ok=True)
    env['CYCLE12_AUDIT_REPORT']=str(out/'main-dependency-audit.json');env['CYCLE12_FRESH_REPLAY']='0'
    source='tools/InspectMain.lean' if args.audit_bodies else 'tools/ExactStatement.lean'
    proc=subprocess.run([lean,'-j1','-DautoImplicit=false','-DmaxRecDepth=10000',source],cwd=ROOT,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (out/'target.log').write_text(proc.stdout)
    expected="'Cycle12.coefficient12' depends on axioms: [propext, Classical.choice, Quot.sound]"
    if proc.returncode or expected not in proc.stdout:
        print(proc.stdout[-5000:]);raise SystemExit('Exact target or axiom check failed')
    result={'passed':True,'expanded_statement_checked':True,'main_theorem':'Cycle12.coefficient12','axioms':['propext','Classical.choice','Quot.sound'],'proof_body_audit_requested':args.audit_bodies,'empty_environment_replay':False,'objects':str(args.objects.resolve())}
    (out/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
