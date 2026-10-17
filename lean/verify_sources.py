"""Verify exact shipped source bytes. This does not compile Lean."""
import hashlib,json
from pathlib import Path
root=Path(__file__).resolve().parent
rows=json.loads((root/'source-manifest.json').read_text())
seen=set()
for r in rows:
 p=root/r['path']
 if p.is_symlink() or not p.is_file():raise SystemExit('Missing or symlink source: '+r['path'])
 b=p.read_bytes()
 if len(b)!=r['bytes'] or hashlib.sha256(b).hexdigest()!=r['sha256']:raise SystemExit('Source differs: '+r['path'])
 if r['path'] in seen:raise SystemExit('Duplicate path: '+r['path'])
 seen.add(r['path'])
actual={p.relative_to(root).as_posix() for p in (root/'Lean').rglob('*.lean')}
if actual!=seen:raise SystemExit('Manifest/source-tree coverage mismatch')
print('PASS:',len(rows),'exact local Lean source files; no build performed')
