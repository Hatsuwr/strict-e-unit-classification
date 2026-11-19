#!/usr/bin/env python3
# Modified for the source-focused edition, 12 November 2026.
"""Pinned Linux x86_64 prerequisite setup; does not compile project proofs.
Usage: python3 setup_dependencies.py RELEASE_ROOT TOOLCHAIN_ROOT
Requires Python >=3.12, curl, tar and zstd. Paths may be relative.
Dependency archives are verified against DEPENDENCY_PINS.json. Existing source
files are verified against those archives, never silently overwritten. Cache
bootstrap uses unchanged upstream functions, omitting browser-only widget JS.
"""
import hashlib,json,os,pathlib,platform,subprocess,sys,tarfile,shutil,re
if sys.argv[1:] in (['-h'], ['--help']):
 print(__doc__); sys.exit(0)
if len(sys.argv) != 3:
 print(__doc__, file=sys.stderr); sys.exit(2)
if sys.version_info < (3, 12):
 raise SystemExit('Setup requires Python 3.12 or newer.')
if sys.platform != 'linux' or platform.machine().lower() not in ('x86_64', 'amd64'):
 raise SystemExit('Setup supports Linux x86_64 only.')
for executable in ('curl', 'tar', 'zstd'):
 if not shutil.which(executable): raise SystemExit('Missing required executable: '+executable)
if '--rate ' not in subprocess.check_output(['curl','--help','all'],text=True):
 raise SystemExit('Installed curl lacks --rate support; install a curl version that provides it.')
if not __debug__:
 raise RuntimeError("Run without Python -O: integrity checks must remain enabled")
R=pathlib.Path(sys.argv[1]).resolve(); T=pathlib.Path(sys.argv[2]).resolve(); P=R/'project'
pins=json.loads((R/'DEPENDENCY_PINS.json').read_text()); D=T/'downloads'; D.mkdir(parents=True,exist_ok=True)
def run(a,**kw): subprocess.run([str(x) for x in a],check=True,**kw)
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''): h.update(b)
 return h.hexdigest()
def download(url,name,digest,size=None):
 a=D/name
 candidate=a if a.exists() else pathlib.Path(str(a)+'.part')
 if candidate != a: run(['curl','-fL','--connect-timeout','15','--max-time','600','-o',candidate,url])
 if size is not None: assert candidate.stat().st_size==size,(name,'size mismatch')
 assert sha(candidate)==digest,(name,'SHA256 mismatch')
 if candidate != a: candidate.replace(a)
 return a
packages=P/'.lake/packages'; packages.mkdir(parents=True,exist_ok=True); receipt=[]
for p in pins['packages']:
 a=download(p['source_archive_url'],p['source_archive_filename'],p['sha256'],p['bytes']); out=packages/p['name']
 with tarfile.open(a) as tf:
  members=[]; files=[]
  for m in tf.getmembers():
   parts=pathlib.PurePosixPath(m.name).parts
   assert '..' not in parts and not m.name.startswith('/')
   if len(parts)<2: continue
   rel='/'.join(parts[1:])
   if m.isfile(): files.append({'path':rel,'sha256':hashlib.sha256(tf.extractfile(m).read()).hexdigest(),'bytes':m.size})
   elif m.issym(): files.append({'path':rel,'symlink':m.linkname})
   elif not m.isdir(): raise RuntimeError('Unexpected nonregular archive entry: '+m.name)
   m.name=rel; members.append(m)
  if not out.exists(): out.mkdir(); tf.extractall(out,members=members,filter='data')
  for f in files:
   q=out/f['path']
   if 'symlink' in f:
    assert q.is_symlink() and os.readlink(q)==f['symlink']; continue
   assert q.is_file() and q.stat().st_size==f['bytes'] and sha(q)==f['sha256'],('source mismatch',str(q))
 receipt.append({'name':p['name'],'revision':p['git_revision'],'archive_sha256':p['sha256'],'archive_url':p['source_archive_url'],'files':files})
(T/'INSTALLED_SOURCE_MANIFEST.json').write_text(json.dumps({'format':1,'packages':receipt},indent=2)+'\n')
a=download(pins['toolchain']['official_release_url'],'lean-4.19.0-linux.tar.zst',pins['toolchain']['sha256'],pins['toolchain']['bytes']); L=T/'lean-4.19.0-linux'
if not L.exists(): run(['tar','--zstd','-xf',a,'-C',T])
# Stream regular-file bytes and link targets; owner metadata varies by machine.
z=subprocess.Popen(['zstd','-dc',str(a)],stdout=subprocess.PIPE)
with tarfile.open(fileobj=z.stdout,mode='r|') as tf:
 for m in tf:
  q=T/m.name
  if m.isfile():
   h=hashlib.sha256(); f=tf.extractfile(m)
   for b in iter(lambda:f.read(1048576),b''): h.update(b)
   assert q.is_file() and q.stat().st_size==m.size and sha(q)==h.hexdigest(),('toolchain mismatch',m.name)
  elif m.issym(): assert q.is_symlink() and os.readlink(q)==m.linkname,('toolchain link mismatch',m.name)
  elif m.islnk(): assert q.is_file() and sha(q)==sha(T/m.linkname),('toolchain hardlink mismatch',m.name)
assert z.wait()==0
run([L/'bin/lean','--version'])
u=pins['cache_unpacker']; a=download(u['official_release_url'],'leantar.tar.gz',u['archive_sha256']); U=T/'unpacker'; U.mkdir(exist_ok=True)
with tarfile.open(a) as tf: tf.extractall(U,filter='data')
leantar=next(x for x in U.rglob('leantar') if x.is_file()); assert sha(leantar)==u['binary_sha256']
cache=T/'mathlib-cache'; cache.mkdir(exist_ok=True); shutil.copy2(leantar,cache/'leantar-0.1.15'); B=packages/'mathlib/.lake/build/lib/lean'; (B/'Cache').mkdir(parents=True,exist_ok=True)
W=T/'cache-tools'; W.mkdir(exist_ok=True); curl=shutil.which('curl'); assert curl
(W/'curl').write_text('#!/usr/bin/env python3\nimport os,sys\nos.execv('+repr(curl)+', ['+repr(curl)+', "--rate", "4/s"]+[x for x in sys.argv[1:] if x != "--parallel"])\n'); (W/'curl').chmod(0o755)
env=os.environ.copy(); env['PATH']=str(W)+':'+str(leantar.parent)+':'+str(L/'bin')+':'+env['PATH']; env['MATHLIB_CACHE_DIR']=str(cache)
env['LEAN_PATH']=str(B); env['LEAN_SRC_PATH']=':'.join(str(packages/p['name']) for p in pins['packages'])
for mod in ['Lean','IO','Hashing','Requests']:
 run([L/'bin/lean','-o',B/'Cache'/f'{mod}.olean','Cache/'+mod+'.lean'],cwd=packages/'mathlib',env=env)
# Determine the direct external imports required by the project.
roots=set()
for f in P.glob('*.lean'):
 for line in f.read_text().splitlines():
  if line.startswith('import '):
   for name in line.removeprefix('import ').split('--')[0].split():
    if any((packages/p['name']/pathlib.Path(*name.split('.'))).with_suffix('.lean').exists() for p in pins['packages']): roots.add(name)
assert roots
(T/'CACHE_ROOTS.json').write_text(json.dumps(sorted(roots),indent=2)+'\n')
root_names=', '.join('`'+name for name in sorted(roots))
main=T/'FetchOfficialCache.lean'; main.write_text('''import Cache.Requests
open Cache IO Hashing Requests System in
def main : IO Unit := CacheM.run do
  let names : List Lean.Name := [ROOT_NAMES]
  let mut roots : Std.HashMap Lean.Name FilePath := {}
  for name in names do
    roots := roots.insert name (← Lean.findLean (← read).srcSearchPath name)
  let memo ← getHashMemo roots
  let needed ← memo.filterByRootModules names
  IO.println s!"Required cache closure: {needed.size} modules"
  let parallel ← validateCurl
  validateLeanTar
  downloadFiles needed false parallel
  for (_, hash) in needed.toArray do
    unless (← (CACHEDIR / hash.asLTar).pathExists) do
      throw <| IO.userError s!"Missing official cache archive: {hash.asLTar}"
  unpackCache needed false
'''.replace('ROOT_NAMES',root_names))
run([L/'bin/lean','--run',main],cwd=P,env=env)
env['LEAN_PATH']=':'.join(str(packages/p['name']/'.lake/build/lib/lean') for p in pins['packages'])
smoke=T/'DependencySmoke.lean'; smoke.write_text(''.join('import '+name+'\n' for name in sorted(roots))+'#check Nat.add_comm\n')
run([L/'bin/lean',smoke],cwd=P,env=env)
print('Prerequisites installed and Required dependency import smoke test passed. Project proof replay was not run.')
