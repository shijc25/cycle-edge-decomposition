"""Shared, portable paths and version checks. No publication operations."""
from pathlib import Path
import hashlib, json, os, shutil, subprocess
ROOT = Path(__file__).resolve().parents[1]

def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for b in iter(lambda: f.read(1024*1024), b''): h.update(b)
    return h.hexdigest()

def sources():
    return json.loads((ROOT/'audit/source-manifest.json').read_text())['sources']

def check_sources():
    errors=[]
    for rel, row in sources().items():
        p=ROOT/rel
        if not p.is_file() or sha(p)!=row['sha256']: errors.append(rel)
    if errors: raise RuntimeError('Missing/changed release sources: '+', '.join(errors[:20]))
    return len(sources())

def environment(lean=None, packages=None, objects=None):
    lean=lean or os.environ.get('CYCLE12_LEAN') or shutil.which('lean')
    if not lean: raise RuntimeError('Install the toolchain in lean-toolchain, or pass --lean.')
    lean=str(Path(lean).absolute())
    version=subprocess.check_output([lean,'--version'],text=True)
    if 'version 4.34.1' not in version: raise RuntimeError('Wrong Lean version: '+version)
    packages=Path(packages or ROOT/'.lake/packages').resolve()
    manifest=json.loads((ROOT/'lake-manifest.json').read_text())
    paths=[]
    for p in manifest['packages']:
        folder=packages/p['name']
        rev=subprocess.check_output(['git','-C',str(folder),'rev-parse','HEAD'],text=True).strip()
        if rev!=p['rev']: raise RuntimeError('Wrong dependency revision: '+p['name'])
        if subprocess.run(['git','-C',str(folder),'diff','--quiet','HEAD','--']).returncode:
            raise RuntimeError('Tracked dependency source changed: '+p['name'])
        lib=folder/'.lake/build/lib/lean'
        if p['name']=='mathlib' and not lib.is_dir(): raise RuntimeError('Missing Mathlib library cache: '+str(lib))
        paths.append(lib)
    env=dict(os.environ)
    env['LEAN_PATH']=os.pathsep.join(map(str,[Path(objects).resolve()]+paths))
    env['PATH']=str(Path(lean).parent)+os.pathsep+env.get('PATH','')
    return lean,env
