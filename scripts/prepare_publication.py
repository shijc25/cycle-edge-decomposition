#!/usr/bin/env python3
"""Compile/check the final manuscript and metadata after full proof verification.

Produces local publication-ready files only; no upload or account access.
"""
from pathlib import Path
import argparse, datetime, hashlib, json, re, shutil, subprocess
from common import ROOT, sha
from verify_artifact import verify, require

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--paper-build', type=Path, required=True)
    args=ap.parse_args(); validation=verify(deep=True)
    require(r'\CycleVerifiedtrue' in (ROOT/'paper/data/verification-macros.tex').read_text(),
            'Final verification macros are not enabled')
    out=args.paper_build.resolve();out.mkdir(parents=True,exist_ok=True)
    with (out/'latexmk.log').open('w') as log:
        subprocess.run(['latexmk','-pdf','-interaction=nonstopmode','-halt-on-error',
                        '-outdir='+str(out),'main.tex'],cwd=ROOT/'paper',stdout=log,
                       stderr=subprocess.STDOUT,check=True)
    log=(out/'main.log').read_text(errors='replace')
    require(not re.search(r'Overfull \\[hv]box|There were undefined references|Citation .*undefined|Reference .*undefined',log),
            'The manuscript has overflow or unresolved references; inspect its log')
    pdf=out/'main.pdf'
    text=subprocess.check_output(['pdftotext',str(pdf),'-'],text=True)
    require('working verification draft' not in text.lower() and
            'still in progress' not in text.lower() and 'jiacheng shi' in text.lower(),
            'Working-draft marker or author mismatch in final manuscript')
    main=(ROOT/'paper/main.tex').read_text()
    acknowledgement=r'\section*{Acknowledgements and use of AI tools}'
    require(main.rfind(acknowledgement)>main.rfind(r'\bibliography{') and
            not re.search(r'\\(?:input|section|bibliography)\b',main.split(acknowledgement,1)[1]),
            'AI acknowledgement must be the last section')
    # Zenodo vocabulary IDs are lowercase; SPDX names in LICENSE/CITATION retain their case.
    for rel, license_name in [('.zenodo.json','apache-2.0'),('release/zenodo-paper.json','cc-by-4.0')]:
        data=json.loads((ROOT/rel).read_text())
        require(data['creators']==[{'name':'Shi, Jiacheng'}] and data['license']==license_name,
                'Author/license mismatch: '+rel)
        require(not any(k in data for k in ['doi','prereserve_doi']),
                'Unexpected preassigned publication identifier: '+rel)
        published = datetime.date.fromisoformat(data['publication_date'])
        require(published.isoformat() == data['publication_date'] and
                r'\date{' + published.strftime('%B ') + str(published.day) + published.strftime(', %Y') + '}' in main,
                'Publication date differs from the manuscript: '+rel)
        require(data.get('version') == '1.0.0', 'Unexpected release version: '+rel)
    names=[p.relative_to(ROOT).as_posix() for p in ROOT.rglob('*') if p.is_file()]
    require(not any(re.search(r'Cycle(?:13|1249|124|122)(?:/|\.)',n,re.I) for n in names),
            'Historical coefficient source path remains')
    require(not (ROOT/'scripts/fetch_external_sources.py').exists(), 'Obsolete restoration script remains')
    shutil.copyfile(pdf,ROOT/'paper/main.pdf')
    record={'passed':True,'source_and_recorded_proof_integrity':validation,
            'paper_pdf_sha256':sha(ROOT/'paper/main.pdf'),'paper_source_sha256':sha(ROOT/'paper/main.tex'),
            'paper_inputs_sha256':{p.relative_to(ROOT).as_posix():sha(p)
                for p in sorted((ROOT/'paper').rglob('*'))
                if p.is_file() and p.suffix in {'.tex','.bib','.txt','.json'}},
            'metadata_sha256':{rel:sha(ROOT/rel) for rel in
                ['.zenodo.json','CITATION.cff','release/zenodo-paper.json','release/author.json',
                 'release/licensing.json','THIRD_PARTY_NOTICES.md','LICENSE','paper/LICENSE.txt']},
            'no_overfull_boxes':True,'all_references_resolved':True,'ai_acknowledgement_last':True,
            'author':'Jiacheng Shi','no_invented_identifiers':True,
            'public_paths_use_current_coefficient':True}
    (ROOT/'release/manuscript-validation.json').write_text(json.dumps(record,indent=2)+'\n')
    path=ROOT/'release/status.json';status=json.loads(path.read_text())
    require(status['current_full_build_completed'] and status['current_main_body_audit_completed'],
            'Final proof status is incomplete')
    # Record the actual final export inventory, including newly generated audit files.
    from export_public import inventory
    public_names=sorted(rel for rel,_ in inventory())
    obsolete=[n for n in public_names if re.search(r'Cycle(?:13|1249|124|123|122)(?:/|[.]|_|-)',n,re.I)]
    old_basename=[n for n in public_names if re.search(r'(?:coefficient|target|proof)(?:13|12p49|12p4|12p3|12p2)(?:\D|$)',Path(n).name,re.I)]
    require(not obsolete and not old_basename,'Historical coefficient filename remains in the final export inventory')
    naming={'public_files':len(public_names),'obsolete_cycle_paths':obsolete,
            'other_historical_coefficient_basenames':old_basename,
            'internal_Cycle13_namespace_retained':True,'main_theorem':'Cycle12.coefficient12',
            'scope':'Final exported source inventory; preserved historical archives are outside this inventory.',
            'inventory_sha256':hashlib.sha256('\n'.join(public_names).encode()).hexdigest()}
    (ROOT/'release/naming-review.json').write_text(json.dumps(naming,indent=2)+'\n')
    status.update(publication_ready=True,verification_basis='Current-source full build, exact theorem and proof-body audit, source/license inventory, and final manuscript checks passed.')
    path.write_text(json.dumps(status,indent=2)+'\n')
    print(json.dumps(record,indent=2))

if __name__=='__main__':main()
