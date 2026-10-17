"""Fetch hash-pinned public source archives only; no compilation or lifecycle hooks.
Requires Python 3.12+ for the standard-library safe tar extraction filter.
"""
import hashlib,json,os,sys,tarfile,tempfile,urllib.request
from pathlib import Path
if sys.version_info<(3,12):raise SystemExit('Python 3.12+ required')
root=Path(__file__).resolve().parent
lock=json.loads((root/'dependencies.lock.json').read_text())
rows=[r for r in lock['dependencies'] if r['role']=='ordinary_build_dependency']
vendor=root/'vendor';vendor.mkdir(exist_ok=True)
for r in rows:
 dest=root/r['vendor_dir']
 if dest.exists():raise SystemExit('Refusing existing directory: '+str(dest)+'; use a clean checkout')
 with tempfile.TemporaryDirectory(prefix='.fetch-',dir=vendor) as tmp:
  tmp=Path(tmp);archive=tmp/'source.tar.gz';h=hashlib.sha256();size=0
  with urllib.request.urlopen(r['archive_url']) as response,archive.open('wb') as out:
   while data:=response.read(1024*1024):out.write(data);h.update(data);size+=len(data)
  if size!=r['archive_bytes'] or h.hexdigest()!=r['archive_sha256']:raise SystemExit('Archive identity mismatch: '+r['name'])
  target=tmp/'unpacked';target.mkdir()
  with tarfile.open(archive,'r:gz') as t:t.extractall(target,filter='data')
  roots=list(target.iterdir())
  if len(roots)!=1 or not roots[0].is_dir():raise SystemExit('Unexpected archive layout: '+r['name'])
  os.rename(roots[0],dest)
 print('Verified source archive:',r['name'],r['revision'])
# Module paths are searched only in the nine exact extracted package directories.
dirs=[root/r['vendor_dir'] for r in rows];count=0
for r in json.loads((root/'dependency-source-manifest.json').read_text()):
 if r['source_class']!='official':continue
 rel=Path(r['module'].replace('.','/')+'.lean');found=[d/rel for d in dirs if (d/rel).is_file()]
 if len(found)!=1:raise SystemExit('Missing or ambiguous upstream module: '+r['module'])
 b=found[0].read_bytes()
 if len(b)!=r['bytes'] or hashlib.sha256(b).hexdigest()!=r['sha256']:raise SystemExit('Selected upstream source differs: '+r['module'])
 count+=1
print('PASS:',count,'selected upstream source hashes; no build or compiled cache used')
