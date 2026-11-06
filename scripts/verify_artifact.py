#!/usr/bin/env python3
"""Verify current release sources and recorded evidence; never invoke Lean."""
import argparse, collections, gzip, hashlib, json
from common import ROOT, check_sources, sha, sources

REMOVED = ('ErdosProblems', 'ProbMethodCombinatorics')
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def verify(deep=False):
    count = check_sources()
    manifest = sources()
    accepted = json.loads((ROOT/'audit/clean-verification.json').read_text())
    require(accepted.get('passed') and accepted.get('current_replacement_closure'),
            'Current replacement closure has not passed the complete build and main audit.')
    require(count == accepted['project_source_modules'], 'Source count mismatch')
    for rel, digest in accepted['evidence_sha256'].items():
        require(sha(ROOT/rel) == digest, 'Evidence hash mismatch: '+rel)
    require(sha(ROOT/'audit/source-manifest.json') == accepted['source_manifest_sha256'],
            'Frozen source-manifest mismatch')
    kernel_review = json.loads((ROOT/'audit/kernel-option-review.json').read_text())
    require(kernel_review['passed'] and not kernel_review['matches'] and
            kernel_review['all_checked_source_hashes_match'] and
            kernel_review['source_modules'] == count and
            kernel_review['source_manifest_sha256'] == accepted['source_manifest_sha256'],
            'Project source kernel-option review is missing or inconsistent')
    modules = {d['module'] for d in manifest.values()}
    require(not any(m.startswith(REMOVED) for m in modules), 'Removed library in source closure')
    require(not any(m.startswith(REMOVED) for d in manifest.values() for m in d['imports']),
            'Removed library import in source closure')
    journal = ROOT/'audit/compilation-results.jsonl'
    require(sha(journal) == accepted['compilation_journal_sha256'], 'Journal hash mismatch')
    latest = {}
    cached_rows = []
    with journal.open() as f:
        for line in f:
            row = json.loads(line)
            require(row['source'] in manifest, 'Compilation journal contains an unknown source')
            latest[row['source']] = row
            if row.get('passed') and row.get('reused_this_run_import_header_only'):
                cached_rows.append(row)
    for rel, data in manifest.items():
        row = latest.get(rel, {})
        require(row.get('passed') and row.get('exit_code') == 0 and
                row.get('source_sha256') == data['sha256'] and row.get('object_sha256') and
                row.get('source_body_recompiled') and row.get('proof_body_recompiled') and
                row.get('old_project_objects_reused') is False,
                'Missing successful current-source compilation record: '+rel)
    recovery=json.loads((ROOT/'audit/storage-recovery-2026-11-04.json').read_text())
    prior_path=ROOT/'audit/recovery-prior-journal.jsonl.gz'
    require(sha(prior_path)==recovery['prior_journal_gzip_sha256'],
            'Pre-loss current-run journal hash mismatch')
    with gzip.open(prior_path,'rt') as stream:
        prior={r['source']:r for r in map(json.loads,stream)}
    recovery_input=json.loads((ROOT/'audit/exact-object-recovery-input.json').read_text())
    require(accepted['historical_compilation_substituted_for_current_source_compilation'] is False,
            'A historical compilation was substituted for a current-source compilation')
    require(accepted['historical_cache_objects_copied_by_exact_current_run_hash']==
            recovery['exact_matching_objects_copied_from_historical_caches']==
            len(recovery_input['candidates_by_source']), 'Recovery inventory count mismatch')
    with gzip.open(ROOT/'audit/exact-object-recovery-results.jsonl.gz','rt') as stream:
        recovered=[json.loads(line) for line in stream]
    require(len(recovered)==accepted['deferred_exact_current_run_objects_recovered'] and
            len({r['source'] for r in recovered})==len(recovered), 'Recovery record count mismatch')
    by_module={data['module']:rel for rel,data in manifest.items()}
    for r in recovered:
        rel=r['source'];previous=prior[rel]
        require(rel in recovery_input['candidates_by_source'] and
                r['source_sha256']==manifest[rel]['sha256']==previous['source_sha256'] and
                r['object_sha256']==previous['object_sha256']==latest[rel]['object_sha256'] and
                previous.get('passed') and previous.get('proof_body_recompiled') and
                previous.get('source_body_recompiled') and
                r['original_compilation_started_utc']==previous['started_utc'] and
                r['actual_new_compilation_claimed'] is False,
                'Recovery does not match an actual pre-loss current-run compilation: '+rel)
        dependencies={by_module[m] for m in manifest[rel]['imports'] if m in by_module}
        require(set(r['prerequisite_object_sha256'])==dependencies,
                'Recovery omitted a prerequisite: '+rel)
        for dep,digest in r['prerequisite_object_sha256'].items():
            require(digest==prior[dep]['object_sha256']==latest[dep]['object_sha256'],
                    'Recovery prerequisite differs from the recorded current build: '+dep)
            require(prior[dep].get('auxiliary_objects_sha256',{})==
                    latest[dep].get('auxiliary_objects_sha256',{}),
                    'Recovery prerequisite associated objects differ: '+dep)
    generations = json.loads((ROOT/'audit/import-header-generations.json').read_text())
    require({x['snapshot_sha256'] for x in generations} ==
            {r['import_header_snapshot_sha256'] for r in cached_rows},
            'Import-header evidence does not cover the recorded generations')
    for generation in generations:
        evidence = generation['evidence']
        if generation['source'] == 'original_probe_record':
            rel = evidence['probe_source']; digest = evidence['cached_object_sha256']
            require(evidence['save_exit'] == evidence['ordinary_exit'] == evidence['cached_exit'] == 0
                    and evidence['byte_identical_objects'] and evidence['header_only']
                    and evidence['ordinary_object_sha256'] == digest
                    and evidence['probe_source_sha256'] == manifest[rel]['sha256'],
                    'Invalid original import-header probe')
        elif generation['source'] == 'retrospective_ordinary_replay':
            rel = evidence['source']; digest = evidence['earlier_compiled_object_sha256']
            require(evidence['passed'] and evidence['exit_code'] == 0
                    and evidence['ordinary_replay_object_sha256'] == digest
                    and evidence['source_sha256'] == manifest[rel]['sha256'],
                    'Invalid ordinary replay of an earlier header generation')
        else:
            raise RuntimeError('Unknown import-header evidence kind')
        require(any(r['source'] == rel and r['object_sha256'] == digest and
                    r['import_header_snapshot_sha256'] == generation['snapshot_sha256']
                    for r in cached_rows), 'Probe is not linked to an actually compiled object')
    digest = hashlib.sha256()
    with gzip.open(ROOT/'audit/main-dependency-audit.json.gz', 'rb') as f:
        for block in iter(lambda: f.read(1024*1024), b''):
            digest.update(block)
    require(digest.hexdigest() == accepted['audit_report_sha256'], 'Dependency report hash mismatch')
    target = json.loads((ROOT/'audit/target-result.json').read_text())
    require(target.get('passed') and target.get('expanded_statement_checked') and
            target.get('proof_body_audit_requested') and not target.get('empty_environment_replay'),
            'Incomplete target audit')
    licenses = json.loads((ROOT/'provenance/license-review.json').read_text())
    require(licenses['unestablished_source_license_files_in_current_closure'] == 0,
            'Unresolved current source license')
    for row in licenses['retained_source_files']:
        require(row['license'] == 'Apache-2.0' and sha(ROOT/row['path']) == row['sha256'],
                'Third-party license inventory/source mismatch: '+row['path'])
    notices = json.loads((ROOT/'provenance/notice-tree-review.json').read_text())
    require(notices['passed'] and all(g['passed'] for g in notices['groups']),
            'Pinned upstream license/notice scope review is incomplete')
    matched_paths = {p for g in notices['groups'] for p in g['source_blob_matches']}
    require(matched_paths == {r['path'] for r in licenses['retained_source_files']},
            'Upstream Git blob checks do not cover the retained third-party source inventory')
    for group in notices['groups']:
        for legal in group['applicable_legal_files']:
            retained = legal.get('retained_as')
            if retained:
                require(sha(ROOT/retained) == legal['sha256'], 'Third-party notice hash mismatch')
            elif 'LICENSE' in legal['path'].split('/')[-1].upper():
                require(sha(ROOT/'LICENSES'/(group['dependency']+'-LICENSE.txt')) == legal['sha256'],
                        'Applicable upstream license differs from bundled copy')
            else:
                raise RuntimeError('Unaccounted applicable legal file: '+legal['path'])
    require(json.loads((ROOT/'release/public-exclusions.json').read_text())['paths'] == [],
            'A required project source is excluded from the public export')
    if deep:
        with gzip.open(ROOT/'audit/main-dependency-audit.json.gz', 'rt') as f:
            report = json.load(f)
        require(report['entry'] == 'Cycle12.coefficient12' and report['all_declaration_bodies_found']
                and report['uncached_body_traversal'] and report['removed_libraries_checked_absent'],
                'Incomplete actual proof-body traversal')
        require(set(report['axioms']) == ALLOWED_AXIOMS and
                report['new_project_axiom_count'] == 0 and not report['new_project_axioms'] and
                not report['unsafe_or_partial_dependencies'] and
                not report['declared_project_axioms_in_all_retained_modules'],
                'Unexpected trusted declarations')
        rows = report['declarations']
        require(len(rows) == report['transitive_declarations'] == accepted['actual_transitive_declarations'],
                'Transitive declaration count mismatch')
        by_name = {r['name']: r for r in rows}
        require(len(by_name) == len(rows), 'Duplicate dependency declarations')
        require(not any(r['module'].startswith(REMOVED) for r in rows), 'Removed library in actual proof')
        require(all(r['project_local'] == (r['module'] in modules) for r in rows),
                'Project ownership does not match source closure')
        project = [r for r in rows if r['project_local']]
        require(len(project) == report['project_declarations'] == accepted['actual_project_declarations'],
                'Project declaration count mismatch')
        require(sum(r['kind'] == 'theorem' for r in project) == report['project_theorems'],
                'Project theorem count mismatch')
        for link in json.loads((ROOT/'docs/proof-map.json').read_text()):
            row = by_name.get(link['declaration'])
            require(row and row['module'] == link['module'] and link['actual_dependency'] is True
                    and not link.get('pending_final_body_audit'),
                    'Invalid paper correspondence: '+link['declaration'])
    return {'passed': True, 'release_source_modules': count,
            'all_current_sources_have_successful_compilation_records': True,
            'current_replacement_closure': True, 'removed_libraries_absent': True,
            'audit_uncompressed_sha256': digest.hexdigest(), 'deep_audit_checked': deep,
            'lean_recompiled_by_this_command': False}

if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--deep-audit', action='store_true')
    args = ap.parse_args()
    print(json.dumps(verify(args.deep_audit), indent=2))
