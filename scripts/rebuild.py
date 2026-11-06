#!/usr/bin/env python3
"""Recompile the accepted local closure using only this build's project objects."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor,wait,FIRST_COMPLETED
import argparse,collections,datetime,hashlib,heapq,json,subprocess,threading,time
from common import ROOT,sources,check_sources,sha,environment

def lightweight_certificate(rel):
    path=Path(rel)
    if path.parent.as_posix() in {'Cycle12/BankParameterCertificates',
            'Cycle12/CapacityCertificates','Cycle12/RoutedCases'}:
        return path.name.startswith('Batch')
    if rel.startswith('Cycle12/FoldPotentialAnchors/'):
        return path.name.startswith('Point')
    return path.parent.as_posix()=='Cycle12/CoverAssembly' and path.name.startswith('Source')

def extra_certificate_memory_available():
    """Conservative optional Linux cgroup gate; other environments use the base limit."""
    try:
        root=Path('/sys/fs/cgroup')
        maximum=int((root/'memory.max').read_text())
        current=int((root/'memory.current').read_text())
        stats=dict(line.split() for line in (root/'memory.stat').read_text().splitlines())
        nonreclaimable=int(stats['anon'])+int(stats['shmem'])
        return current<maximum-1024**3 and nonreclaimable<min(8*1024**3,maximum//2)
    except (OSError,ValueError,KeyError):
        return False

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--target',help='Diagnostic module closure instead of the complete accepted closure')
    ap.add_argument('--plan',action='store_true',help='Check sources and dependency order; do not invoke Lean')
    ap.add_argument('--resume',action='store_true',help='Reuse only objects matching this output directory journal and unchanged sources')
    ap.add_argument('--restore-exact-current-run',action='store_true',help='After storage loss, defer recovery of byte-identical previously compiled objects until their exact prerequisite objects have been regenerated')
    ap.add_argument('--out',type=Path,default=ROOT/'.cycle12-build')
    ap.add_argument('--workers',type=int,default=1)
    ap.add_argument('--certificate-workers',type=int,help='Optional higher limit for selected small certificates only; memory gate and ordinary worker limit remain in effect')
    ap.add_argument('--timeout',type=float,default=0,help='Per-module seconds; zero means no time limit')
    ap.add_argument('--header-cache',action='store_true',help='Cache import headers only after byte-identical ordinary/cache compilation of a current source')
    ap.add_argument('--lean');ap.add_argument('--packages',type=Path)
    args=ap.parse_args()
    if args.restore_exact_current_run and not args.resume:
        ap.error('--restore-exact-current-run requires --resume')
    if args.workers<1:ap.error('--workers must be positive')
    certificate_workers=args.workers if args.certificate_workers is None else args.certificate_workers
    if certificate_workers<args.workers:ap.error('--certificate-workers must be at least --workers')
    check_sources();src=sources();by_module={d['module']:rel for rel,d in src.items()}
    if args.target:
        if args.target not in by_module:raise RuntimeError('Unknown module: '+args.target)
        keep=set();todo=[by_module[args.target]]
        while todo:
            rel=todo.pop()
            if rel in keep:continue
            keep.add(rel);todo.extend(by_module[x] for x in src[rel]['imports'] if x in by_module)
        src={rel:src[rel] for rel in keep};by_module={d['module']:rel for rel,d in src.items()}
    deps={rel:{by_module[x] for x in d['imports'] if x in by_module} for rel,d in src.items()}
    children={rel:set() for rel in src}
    for rel,ds in deps.items():
        for dep in ds:children[dep].add(rel)
    # A topological plan also detects missing/cyclic local dependencies.
    counts={rel:len(ds) for rel,ds in deps.items()};queue=[r for r,n in counts.items() if n==0];heapq.heapify(queue);ordered=[]
    while queue:
        rel=heapq.heappop(queue);ordered.append(rel)
        for ch in children[rel]:
            counts[ch]-=1
            if counts[ch]==0:heapq.heappush(queue,ch)
    if len(ordered)!=len(src):raise RuntimeError('Local import cycle')
    if args.plan:
        print(json.dumps({'passed':True,'modules':len(src),'entry':args.target or 'Cycle12.Coefficient12Complete','full_closure':not bool(args.target),'topological_plan':True,'compilation_started':False},indent=2));return
    out=args.out.resolve();obj=out/'lib/lean';journal=out/'compilation.jsonl'
    if out.exists() and any(out.iterdir()) and not args.resume:raise RuntimeError('Output is not empty. Choose a new --out or explicitly use --resume.')
    obj.mkdir(parents=True,exist_ok=True);(out/'logs').mkdir(exist_ok=True)
    lean,env=environment(args.lean,args.packages,obj)
    config={'lean':lean,'target':args.target,'packages':[{'name':d['name'],'rev':d['rev']} for d in json.loads((ROOT/'lake-manifest.json').read_text())['packages']], 'toolchain':(ROOT/'lean-toolchain').read_text().strip()}
    if args.resume:
        if not (out/'configuration.json').is_file():raise RuntimeError('Cannot resume without this build configuration')
        old=json.loads((out/'configuration.json').read_text())
        if old['packages']!=config['packages'] or old['toolchain']!=config['toolchain'] or old.get('target')!=config['target']:raise RuntimeError('Build dependency versions changed')
    (out/'configuration.json').write_text(json.dumps(config,indent=2)+'\n')
    header_groups=collections.Counter(tuple(d['imports']) for d in src.values())
    header_locks={key:threading.Lock() for key,n in header_groups.items() if n>=500}
    header_state={}
    previous={}
    if args.resume and journal.exists():
        for line in journal.read_text().splitlines():
            row=json.loads(line);previous[row['source']]=row
    recovery={}
    if args.restore_exact_current_run:
        recovery=json.loads((out/'exact-object-recovery-input.json').read_text())['candidates_by_source']
    done=set()
    for rel in ordered:
        row=previous.get(rel,{});p=obj/Path(rel).with_suffix('.olean')
        aux_ok=all((p.parent/name).is_file() and sha(p.parent/name)==digest for name,digest in row.get('auxiliary_objects_sha256',{}).items())
        if row.get('passed') and aux_ok and row.get('source_sha256')==src[rel]['sha256'] and p.is_file() and not p.is_symlink() and sha(p)==row.get('object_sha256') and deps[rel]<=done:done.add(rel)
    def compile_one(rel):
        output=obj/Path(rel).with_suffix('.olean');output.parent.mkdir(parents=True,exist_ok=True)
        if output.is_symlink():raise RuntimeError('Symlinked project object rejected: '+rel)
        if sha(ROOT/rel)!=src[rel]['sha256']:raise RuntimeError('Source changed during build: '+rel)
        implicit='true' if rel.split('/')[0] in {'ProbMethodCombinatorics','Cslib','ARA','ErdosProblems'} else 'false'
        cmd=[lean,'-j1','-DautoImplicit='+implicit,'-DmaxRecDepth=10000','-DmaxHeartbeats=4000000',rel,'-o',str(output)]
        log=out/'logs'/Path(rel).with_suffix('.log');log.parent.mkdir(parents=True,exist_ok=True)
        started=time.monotonic();record={'source':rel,'source_sha256':src[rel]['sha256'],'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'command':cmd,'proof_body_recompiled':True,'source_body_recompiled':True,'old_project_objects_reused':False}
        key=tuple(src[rel]['imports']);cached=None
        if args.header_cache and key in header_locks and implicit=='false':
            with header_locks[key]:
                if key not in header_state:
                    folder=out/'header-cache'/hashlib.sha256('\n'.join(key).encode()).hexdigest()[:16]
                    folder.mkdir(parents=True,exist_ok=True)
                    header=folder/'header.lean';snapshot=folder/'header.snapshot'
                    header.write_text(''.join('import '+m+'\n' for m in key))
                    deps_hash={m:sha(obj/Path(m.replace('.','/')+'.olean')) for m in key if m in by_module}
                    save=[lean,'-j1','-DautoImplicit=false','-DmaxRecDepth=10000','-DmaxHeartbeats=4000000',str(header),'--incr-save='+str(snapshot)]
                    with (folder/'save.log').open('w') as stream:
                        saved=subprocess.run(save,cwd=ROOT,env=env,stdout=stream,stderr=subprocess.STDOUT).returncode
                    probe=folder/'probe.olean'
                    normal=[lean,'-j1','-DautoImplicit=false','-DmaxRecDepth=10000','-DmaxHeartbeats=4000000',rel,'-o',str(probe)]
                    with (folder/'probe.log').open('w') as stream:
                        first=subprocess.run(normal,cwd=ROOT,env=env,stdout=stream,stderr=subprocess.STDOUT).returncode
                        first_sha=sha(probe) if first==0 and probe.exists() else None
                        second=subprocess.run(normal+['--incr-load='+str(snapshot)],cwd=ROOT,env=env,stdout=stream,stderr=subprocess.STDOUT).returncode if saved==0 and first==0 else None
                    second_sha=sha(probe) if second==0 and probe.exists() else None
                    accepted=saved==0 and first==0 and second==0 and first_sha==second_sha
                    evidence={'imports':key,'dependency_object_sha256':deps_hash,'probe_source':rel,'probe_source_sha256':src[rel]['sha256'],'save_exit':saved,'ordinary_exit':first,'cached_exit':second,'ordinary_object_sha256':first_sha,'cached_object_sha256':second_sha,'byte_identical_objects':accepted,'header_only':True,'every_source_body_recompiled':True,'old_project_objects_used':False}
                    (folder/'evidence.json').write_text(json.dumps(evidence,indent=2)+'\n')
                    if probe.exists():probe.unlink()
                    header_state[key]={'path':snapshot,'sha256':sha(snapshot),'accepted':True} if accepted else {'accepted':False}
                cached=header_state[key]
            if cached.get('accepted'):
                cmd=cmd+['--incr-load='+str(cached['path'])]
                record.update(command=cmd,reused_this_run_import_header_only=True,import_header_snapshot_sha256=cached['sha256'])
        with log.open('w') as stream:
            try:code=subprocess.run(cmd,cwd=ROOT,env=env,stdout=stream,stderr=subprocess.STDOUT,timeout=args.timeout or None).returncode
            except subprocess.TimeoutExpired:code='timeout'
        record.update(exit_code=code,elapsed_seconds=round(time.monotonic()-started,3),passed=code==0 and output.is_file())
        if record['passed']:
            record.update(object_sha256=sha(output),object_bytes=output.stat().st_size,
                          auxiliary_objects_sha256={p.name:sha(p) for suffix in ('.server','.private') if (p:=Path(str(output)+suffix)).exists()})
        else:
            if output.exists():output.unlink()
            record['diagnostic_tail']=log.read_text(errors='replace')[-3000:]
        return record
    ready=[rel for rel in ordered if rel not in done and deps[rel]<=done];heapq.heapify(ready);active={};failed=[]
    restored_exact=[]
    def recover_exact(rel):
        """Recover bytes of an actual compilation in this run, never substitute an old proof check."""
        if rel not in recovery or not deps[rel]<=done:
            return False
        row=previous.get(rel,{})
        if not (row.get('passed') and row.get('exit_code')==0 and
                row.get('source_sha256')==src[rel]['sha256'] and
                row.get('proof_body_recompiled') and row.get('source_body_recompiled') and
                row.get('old_project_objects_reused') is False):
            return False
        p=obj/Path(rel).with_suffix('.olean')
        if not p.is_file() or p.is_symlink() or sha(p)!=row.get('object_sha256'):
            return False
        if any(not (p.parent/n).is_file() or sha(p.parent/n)!=digest
               for n,digest in row.get('auxiliary_objects_sha256',{}).items()):
            return False
        prerequisite_hashes={}
        for dep in deps[rel]:
            digest=sha(obj/Path(dep).with_suffix('.olean'))
            if digest!=previous.get(dep,{}).get('object_sha256'):
                return False
            prerequisite_hashes[dep]=digest
        evidence={'source':rel,'source_sha256':src[rel]['sha256'],
                  'object_sha256':row['object_sha256'],
                  'original_compilation_started_utc':row['started_utc'],
                  'recovered_from':recovery[rel],
                  'prerequisite_object_sha256':prerequisite_hashes,
                  'actual_new_compilation_claimed':False}
        with (out/'exact-object-recovery-results.jsonl').open('a') as recovered:
            recovered.write(json.dumps(evidence)+'\n')
        restored_exact.append(rel)
        return True
    priority={}
    for rel in reversed(ordered):priority[rel]=1+max((priority[ch] for ch in children[rel]),default=0)
    ready=[(-priority[r],r) for r in ready];heapq.heapify(ready)
    with ThreadPoolExecutor(max_workers=certificate_workers) as pool,journal.open('a') as stream:
        while ready or active:
            limit=args.workers
            if (out/'concurrency.json').exists():
                limit=int(json.loads((out/'concurrency.json').read_text())['workers'])
                if not 1<=limit<=args.workers:raise RuntimeError('Invalid worker limit')
            while ready and not failed:
                candidate=ready[0][1]
                dispatch_limit=limit
                if (certificate_workers>limit and lightweight_certificate(candidate)
                        and all(lightweight_certificate(r) for r in active.values())
                        and extra_certificate_memory_available()):
                    dispatch_limit=certificate_workers
                if len(active)>=dispatch_limit:break
                _,rel=heapq.heappop(ready)
                if args.restore_exact_current_run and recover_exact(rel):
                    done.add(rel)
                    for ch in children[rel]:
                        if deps[ch]<=done:heapq.heappush(ready,(-priority[ch],ch))
                    continue
                active[pool.submit(compile_one,rel)]=rel
            if not active:break
            completed,_=wait(active,timeout=10,return_when=FIRST_COMPLETED)
            for task in completed:
                rel=active.pop(task);row=task.result();stream.write(json.dumps(row)+'\n');stream.flush()
                if row['passed']:
                    done.add(rel)
                    for ch in children[rel]:
                        if deps[ch]<=done:heapq.heappush(ready,(-priority[ch],ch))
                    if len(done)%50==0:print(f'{len(done)}/{len(src)} modules complete',flush=True)
                else:failed.append(rel);print('Failed: '+rel+'; see '+str(out/'logs'/Path(rel).with_suffix('.log')),flush=True)
            state={'compiled':len(done),'total':len(src),'failed':failed,'active':list(active.values()),'ready':len(ready),'workers':limit,'certificate_workers':certificate_workers,'complete':False}
            (out/'status.json').write_text(json.dumps(state,indent=2)+'\n')
            for key,cached in header_state.copy().items():
                if cached.get('accepted') and not cached.get('removed') and all(r in done for r,d in src.items() if tuple(d['imports'])==key):
                    path=cached['path']
                    if path.exists():path.unlink()
                    for extra in path.parent.glob('header.snapshot.*'):extra.unlink()
                    cached['removed']=True
    result={'passed':len(done)==len(src) and not failed,'compiled_or_hash_valid_resume':len(done),'total':len(src),'failed':failed,'external_library_objects_reused':True,'full_accepted_closure':not bool(args.target),'target':args.target,'new_output':str(out),'deferred_exact_current_run_objects_recovered':len(restored_exact)}
    (out/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
    if not result['passed']:raise SystemExit(1)
if __name__=='__main__':main()
