#!/usr/bin/env python3
"""Prepare a public source ZIP locally. Does not upload or publish anything."""
from pathlib import Path
import argparse,hashlib,json,os,zipfile
from common import ROOT,check_sources,sha
from verify_artifact import verify
SKIP_DIRS={'.git','.lake','.cycle12-build','.cycle12-check','__pycache__','dist'}
PREPARATION_ONLY={'scripts/checkpoint_replacements.py','scripts/seed_current_development_build.py','scripts/prepare_replacement_manifest.py','scripts/build_replacements.py'}
BUILD_SUFFIXES={'.pyc','.olean','.ilean','.ir','.aux','.bbl','.blg','.fdb_latexmk','.fls','.log','.out','.toc'}

def inventory(private=False):
    excluded=set(json.loads((ROOT/'release/public-exclusions.json').read_text())['paths'])
    files=[]
    for base,dirs,names in os.walk(ROOT):
        dirs[:]=sorted(d for d in dirs if d not in SKIP_DIRS)
        for name in sorted(names):
            p=Path(base)/name;rel=p.relative_to(ROOT).as_posix()
            if rel in PREPARATION_ONLY:continue
            if p.is_symlink():raise RuntimeError('Symlink excluded from source release: '+rel)
            if not private and rel in excluded:continue
            if name.endswith(('.olean.private','.olean.server')):continue
            if p.suffix in BUILD_SUFFIXES and not rel.startswith('audit/'):continue
            if rel in {'audit/main-dependency-audit.json','audit/inspection-progress.json'}:continue
            if p.stat().st_size>=100*1024*1024:raise RuntimeError('Oversized GitHub source artifact: '+rel)
            files.append((rel,p))
    return files

def export(output,private=False):
    verify(deep=True)
    status=json.loads((ROOT/'release/status.json').read_text())
    if not status.get('publication_ready'):raise RuntimeError('Publication preparation is not complete.')
    manuscript=json.loads((ROOT/'release/manuscript-validation.json').read_text())
    if not manuscript.get('passed') or sha(ROOT/'paper/main.pdf')!=manuscript['paper_pdf_sha256']:
        raise RuntimeError('The final manuscript PDF is not the checked version.')
    for group in ['paper_inputs_sha256','metadata_sha256']:
        for rel,digest in manuscript[group].items():
            if sha(ROOT/rel)!=digest:raise RuntimeError('Publication input changed after validation: '+rel)
    output=output.resolve()
    if output.exists():raise RuntimeError('Refusing to replace an existing archive: '+str(output))
    files=inventory(private)
    included={rel for rel,p in files}
    naming=json.loads((ROOT/'release/naming-review.json').read_text())
    if (naming.get('obsolete_cycle_paths') or naming.get('other_historical_coefficient_basenames') or
        naming.get('public_files')!=len(files) or
        naming.get('inventory_sha256')!=hashlib.sha256('\n'.join(sorted(included)).encode()).hexdigest()):
        raise RuntimeError('The export inventory differs from the final naming review.')
    from common import sources
    if not set(sources())<=included:raise RuntimeError('A required source is missing from the export.')
    if any(rel.startswith(('ErdosProblems/','ProbMethodCombinatorics/')) for rel in included):raise RuntimeError('A removed library remains in the public tree.')
    output.parent.mkdir(parents=True,exist_ok=True)
    temporary=output.with_name(output.name+'.partial-'+str(os.getpid()))
    try:
        with zipfile.ZipFile(temporary,'x',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
            for rel,p in files:z.write(p,'cycle12/'+rel)
        with zipfile.ZipFile(temporary) as z:
            bad=z.testzip()
            if bad:raise RuntimeError('Bad ZIP member: '+bad)
            for rel,p in files:
                if hashlib.sha256(z.read('cycle12/'+rel)).hexdigest()!=sha(p):raise RuntimeError('Archive source mismatch: '+rel)
        # The final archive name is exposed only after all integrity checks pass.
        # Hard linking also refuses a destination created concurrently.
        os.link(temporary,output)
    finally:
        if temporary.exists():temporary.unlink()
    result={'passed':True,'archive':str(output),'sha256':sha(output),'bytes':output.stat().st_size,'files':len(files),'private_review_copy':private,'external_source_files_omitted':0,'crc_and_all_file_hashes_checked':True,'published':False}
    output.with_suffix(output.suffix+'.json').write_text(json.dumps(result,indent=2)+'\n')
    return result

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();print(json.dumps(export(a.output),indent=2))
