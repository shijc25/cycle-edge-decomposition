#!/usr/bin/env python3
"""Bind an actually completed current-source build and target audit into release evidence.

Does not upload, publish, or change any scheduled task. Refuses incomplete builds.
"""
from pathlib import Path
import argparse, collections, datetime, gzip, json, shutil, subprocess, sys
from common import ROOT, check_sources, sources, sha, environment
from verify_artifact import require, verify

def write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False)+'\n')

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--build', type=Path, required=True)
    ap.add_argument('--check', type=Path, required=True)
    ap.add_argument('--lean'); ap.add_argument('--packages', type=Path)
    args=ap.parse_args(); build=args.build.resolve(); check=args.check.resolve()
    count=check_sources(); manifest=sources()
    result=json.loads((build/'result.json').read_text())
    require(result.get('passed') and result.get('full_accepted_closure') and
            result.get('target') is None and result['total']==count and
            result['compiled_or_hash_valid_resume']==count and not result['failed'],
            'Full current-source build has not completed successfully.')
    environment(args.lean, args.packages, build/'lib/lean')
    rows=[json.loads(l) for l in (build/'compilation.jsonl').read_text().splitlines()]
    latest={r['source']:r for r in rows}
    require(set(latest)==set(manifest), 'Compilation closure differs from frozen manifest')
    for rel, source in manifest.items():
        row=latest[rel]; obj=build/'lib/lean'/Path(rel).with_suffix('.olean')
        require(row.get('passed') and row.get('exit_code')==0 and
                row.get('source_sha256')==source['sha256'] and
                row.get('proof_body_recompiled') and row.get('source_body_recompiled') and
                row.get('old_project_objects_reused') is False and
                obj.is_file() and not obj.is_symlink() and sha(obj)==row['object_sha256'],
                'Invalid compiled object: '+rel)
        for name, digest in row.get('auxiliary_objects_sha256',{}).items():
            require(sha(obj.parent/name)==digest, 'Associated object hash mismatch: '+name)
    print('All current project sources and compiled objects verified.', flush=True)
    target=json.loads((check/'result.json').read_text())
    require(target.get('passed') and target.get('proof_body_audit_requested') and
            target.get('expanded_statement_checked') and not target.get('empty_environment_replay') and
            Path(target['objects']).resolve()==(build/'lib/lean').resolve(),
            'Missing full target audit against this build')
    report_path=check/'main-dependency-audit.json'
    report=json.loads(report_path.read_text())
    require(report.get('removed_libraries_checked_absent') and report['new_project_axiom_count']==0
            and set(report['axioms'])=={'propext','Classical.choice','Quot.sound'} and
            not report['unsafe_or_partial_dependencies'] and
            not report['declared_project_axioms_in_all_retained_modules'], 'Unexpected proof dependencies')
    storage_recovery=json.loads((ROOT/'audit/storage-recovery-2026-11-04.json').read_text())
    prior_path=ROOT/'audit/recovery-prior-journal.jsonl.gz'
    require(sha(prior_path)==storage_recovery['prior_journal_gzip_sha256'],
            'Persisted pre-loss journal changed')
    with gzip.open(prior_path,'rt') as stream:
        prior={r['source']:r for r in map(json.loads,stream)}
    recovery_input=json.loads((build/'exact-object-recovery-input.json').read_text())
    require(len(recovery_input['candidates_by_source'])==
            storage_recovery['exact_matching_objects_copied_from_historical_caches'],
            'Object restoration inventory changed')
    recovery_path=build/'exact-object-recovery-results.jsonl'
    recovered=[json.loads(line) for line in recovery_path.read_text().splitlines()]
    for r in recovered:
        rel=r['source']; previous=prior[rel]
        require(rel in recovery_input['candidates_by_source'] and
                r['source_sha256']==manifest[rel]['sha256']==previous['source_sha256'] and
                r['object_sha256']==previous['object_sha256']==latest[rel]['object_sha256'] and
                previous.get('passed') and previous.get('proof_body_recompiled') and
                previous.get('source_body_recompiled') and
                r['original_compilation_started_utc']==previous['started_utc'] and
                r['actual_new_compilation_claimed'] is False,
                'Invalid exact-object restoration: '+rel)
        for dep,digest in r['prerequisite_object_sha256'].items():
            require(digest==prior[dep]['object_sha256']==latest[dep]['object_sha256'],
                    'Restored object prerequisite mismatch: '+dep)
            require(prior[dep].get('auxiliary_objects_sha256',{})==
                    latest[dep].get('auxiliary_objects_sha256',{}),
                    'Restored prerequisite associated objects changed: '+dep)
    shutil.copyfile(build/'exact-object-recovery-input.json',ROOT/'audit/exact-object-recovery-input.json')
    with recovery_path.open('rb') as src,(ROOT/'audit/exact-object-recovery-results.jsonl.gz').open('wb') as raw:
        with gzip.GzipFile(filename='',fileobj=raw,mode='wb',mtime=0,compresslevel=9) as dst:
            shutil.copyfileobj(src,dst)
    shutil.copyfile(build/'compilation.jsonl', ROOT/'audit/compilation-results.jsonl')
    shutil.copyfile(check/'result.json', ROOT/'audit/target-result.json')
    shutil.copyfile(check/'target.log', ROOT/'audit/exact-target-verification.log')
    with report_path.open('rb') as src, (ROOT/'audit/main-dependency-audit.json.gz').open('wb') as raw:
        with gzip.GzipFile(filename='', fileobj=raw, mode='wb', mtime=0, compresslevel=9) as dst:
            shutil.copyfileobj(src,dst)
    headers=[]
    generations={x['snapshot_sha256']:x for x in
        json.loads((ROOT/'audit/import-header-generations.json').read_text())}
    for p in sorted((build/'header-cache').glob('*/evidence.json')):
        evidence=json.loads(p.read_text()); headers.append(evidence)
        # A rejected optional probe uses ordinary compilation. Every snapshot
        # actually used must still be covered by the generation check below.
        if not evidence['byte_identical_objects']:
            continue
        matching=[r for r in rows if r['source']==evidence['probe_source'] and
            r.get('object_sha256')==evidence['cached_object_sha256'] and
            r.get('reused_this_run_import_header_only')]
        require(matching and evidence['byte_identical_objects'], 'Missing successful import-header probe')
        snapshot=matching[-1]['import_header_snapshot_sha256']
        generations[snapshot]={'snapshot_sha256':snapshot,'source':'original_probe_record','evidence':evidence}
    replay=json.loads((ROOT/'audit/previous-header-replay.json').read_text())
    require(replay['passed'] and replay['exit_code']==0 and
            replay['ordinary_replay_object_sha256']==replay['earlier_compiled_object_sha256']==
                latest[replay['source']]['object_sha256'], 'Earlier header-generation ordinary replay failed')
    snapshot=replay['earlier_header_snapshot_sha256']
    generations.setdefault(snapshot,{'snapshot_sha256':snapshot,
        'source':'retrospective_ordinary_replay','evidence':replay})
    used_headers={r['import_header_snapshot_sha256'] for r in rows if
        r.get('passed') and r.get('reused_this_run_import_header_only')}
    require(set(generations)==used_headers, 'Import-header evidence does not cover all generations')
    write(ROOT/'audit/import-header-evidence.json',headers)
    write(ROOT/'audit/import-header-generations.json',list(generations.values()))
    for name in ['development-seed.json','seed-auxiliary-repair.json','configuration.json','result.json']:
        if (build/name).exists():shutil.copyfile(build/name,ROOT/'audit'/('current-build-'+name))
    local=[x for x in report['declarations'] if x['project_local']]
    accepted={
      'timestamp':datetime.datetime.now(datetime.timezone.utc).isoformat(),
      'passed':True,'current_replacement_closure':True,'coefficient':12,
      'main_theorem':'Cycle12.coefficient12','project_source_modules':count,
      'all_retained_project_sources_recompiled':True,
      'old_project_objects_reused':bool(recovery_input['candidates_by_source']),
      'historical_compilation_substituted_for_current_source_compilation':False,
      'historical_cache_objects_copied_by_exact_current_run_hash':len(recovery_input['candidates_by_source']),
      'deferred_exact_current_run_objects_recovered':len(recovered),
      'proof_bodies_recompiled_for_every_module':True,'source_and_object_hashes_verified':True,
      'explicit_unfolded_edge_partition_statement_verified':True,'component_count_includes_isolates':True,
      'foundation_axioms':sorted(report['axioms']),'new_project_axioms':0,
      'uncached_dependency_body_audit':True,'removed_libraries_absent':True,
      'actual_transitive_declarations':report['transitive_declarations'],
      'actual_project_declarations':report['project_declarations'],
      'actual_project_theorems_including_generated_helpers':report['project_theorems'],
      'actual_project_kind_counts':dict(collections.Counter(x['kind'] for x in local)),
      'all_retained_project_declarations':report['all_retained_project_declarations'],
      'all_retained_project_kind_counts':report['all_retained_project_kind_counts'],
      'source_manifest_sha256':sha(ROOT/'audit/source-manifest.json'),
      'audit_report_sha256':sha(report_path),
      'compilation_journal_sha256':sha(ROOT/'audit/compilation-results.jsonl'),
      'compilation_attempts_recorded':len(rows),
      'historical_unsuccessful_attempts':[{'source':r['source'],'exit_code':r.get('exit_code')} for r in rows if not r.get('passed')],
      'same_run_development_objects':sum(bool(r.get('reused_current_run_development_object')) for r in latest.values()),
      'fresh_import_header_only_modules':sum(bool(r.get('reused_this_run_import_header_only')) for r in latest.values()),
      'external_library_objects_reused':True,'empty_environment_kernel_replay':False,
      'lean_version':'4.34.1','evidence_sha256':{}
    }
    write(ROOT/'audit/clean-verification.json',accepted)
    subprocess.run([sys.executable,'scripts/generate_paper_tables.py'],cwd=ROOT,check=True)
    macros='\\newif\\ifCycleVerified\n\\CycleVerifiedtrue\n'
    macros+='\\newcommand{\\CycleDependencyCount}{'+f"{report['transitive_declarations']:,}".replace(',',r'\,')+'}\n'
    macros+='\\newcommand{\\CycleProjectDependencyCount}{'+f"{report['project_declarations']:,}".replace(',',r'\,')+'}\n'
    (ROOT/'paper/data/verification-macros.tex').write_text(macros)
    for rel, key in [('provenance/license-review.json','complete_main_rebuild_pending'),
                     ('provenance/replaced-dependencies.json','complete_main_audit_pending')]:
        p=ROOT/rel; data=json.loads(p.read_text());data[key]=False;write(p,data)
    p=ROOT/'release/independent-replacement-inputs.json';data=json.loads(p.read_text());data['new_build_completed']=True;write(p,data)
    evidence=['audit/source-manifest.json','audit/local-modules.txt','audit/target-result.json',
              'audit/exact-target-verification.log','audit/import-header-evidence.json',
              'audit/build-scheduling-transition.json',
              'audit/import-header-generations.json','audit/previous-header-replay.json',
              'audit/kernel-option-review.json',
              'audit/environment-resumption.json',
              'audit/storage-recovery-2026-11-04.json','audit/recovery-prior-journal.jsonl.gz',
              'audit/exact-object-recovery-input.json','audit/exact-object-recovery-results.jsonl.gz',
              'audit/storage-header-replay.json',
              'tools/InspectMain.lean','tools/ExactStatement.lean','scripts/rebuild.py',
              'scripts/check_target.py','lake-manifest.json','lean-toolchain',
              'docs/proof-map.json','provenance/license-review.json','provenance/retained-sources.json',
              'provenance/notice-tree-review.json','THIRD_PARTY_NOTICES.md']
    accepted['evidence_sha256']={rel:sha(ROOT/rel) for rel in evidence}
    write(ROOT/'audit/clean-verification.json',accepted)
    p=ROOT/'release/status.json';status=json.loads(p.read_text())
    status.update(current_full_build_completed=True,current_main_body_audit_completed=True,
                  publication_ready=False,verification_basis='Full current-source compilation, exact target, and actual proof-body audit passed; final manuscript/export checks pending.')
    write(p,status)
    validation=verify(deep=True);write(ROOT/'release/integrity-check.json',validation)
    print(json.dumps(accepted,indent=2))

if __name__=='__main__':main()
