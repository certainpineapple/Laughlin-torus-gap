#!/usr/bin/env python3
"""Rebuild selected local Lean sources, with explicitly reused pinned dependency caches.
No downloads, package hooks, source changes, or historical local objects are used.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOTS = ['torus.shared.FermionPhysicalUniformGap', 'torus.shared.BosonPhysicalFockThird']

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def module_path(name, suffix):
    return Path(*name.split('.')).with_suffix(suffix)

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--source-dir', type=Path, default=Path(__file__).resolve().parent)
    ap.add_argument('--dependencies', type=Path, help='Directory containing the nine pinned vendor directories; defaults to SOURCE/vendor')
    ap.add_argument('--lean', default=shutil.which('lean'))
    ap.add_argument('--work-dir', type=Path, help='Fresh output directory; defaults to SOURCE/.rebuild')
    ap.add_argument('--resume', action='store_true', help='Reuse only outputs with matching source and output hashes in this run state')
    ap.add_argument('--verify-only', action='store_true', help='Verify complete recorded outputs and repeat final axiom checks; requires --resume')
    ap.add_argument('--target', action='append', help='Optional local module target (repeatable); default is both final roots')
    ap.add_argument('--memory-mb', type=int, default=7168)
    args = ap.parse_args()
    source = args.source_dir.resolve()
    deps_root = (args.dependencies or source / 'vendor').resolve()
    work = (args.work_dir or source / '.rebuild').resolve()
    if not args.lean:
        ap.error('Lean 4.34.1 is required; specify --lean or add it to PATH')
    lean = str(Path(args.lean).resolve())
    lock = json.loads((source / 'dependencies.lock.json').read_text())
    commit = subprocess.check_output([lean, '--githash'], text=True).strip()
    if commit != lock['toolchain']['lean_commit']:
        raise RuntimeError('Wrong Lean commit: ' + commit)
    version = subprocess.check_output([lean, '--version'], text=True).strip()
    lib = Path(subprocess.check_output([lean, '--print-libdir'], text=True).strip())
    local = {r['module']: r for r in json.loads((source / 'source-manifest.json').read_text())}
    upstream = {r['module']: r for r in json.loads((source / 'dependency-source-manifest.json').read_text())}
    for n, r in local.items():
        if sha(source / r['path']) != r['sha256']:
            raise RuntimeError('Local source hash mismatch: ' + n)
    targets = args.target or ROOTS
    order, seen = [], set()
    def visit(n):
        if n not in local or n in seen:
            return
        seen.add(n)
        for d in local[n]['imports']:
            visit(d)
        order.append(n)
    for n in targets:
        if n not in local:
            raise RuntimeError('Unknown local target: ' + n)
        visit(n)
    state_path = work / 'rebuild-state.json'
    if args.verify_only and not args.resume:
        ap.error('--verify-only requires --resume')
    if args.resume:
        state = json.loads(state_path.read_text())
        if state['lean_commit'] != commit:
            raise RuntimeError('Recorded toolchain mismatch')
    else:
        if work.exists() and any(work.iterdir()):
            raise RuntimeError('Output directory is not empty; use a fresh directory or verified --resume')
        work.mkdir(parents=True, exist_ok=True)
        state = {'schema': 'SELECTED_LOCAL_REBUILD_STATE_V1', 'lean_commit': commit, 'modules': {}}
    out = work / 'build/lib/lean'
    cache = work / 'dependency-cache-overlay'
    out.mkdir(parents=True, exist_ok=True)
    cache.mkdir(parents=True, exist_ok=True)
    packages = []
    for d in lock['dependencies']:
        if d['role'] != 'ordinary_build_dependency':
            continue
        package = deps_root / Path(d['vendor_dir']).name
        if not package.is_dir():
            raise RuntimeError('Missing pinned dependency source: ' + str(package))
        packages.append(package)
        existing = package / '.lake/build/lib/lean'
        if existing.is_dir():
            for f in existing.rglob('*'):
                if f.is_file():
                    q = cache / f.relative_to(existing)
                    if not q.exists():
                        q.parent.mkdir(parents=True, exist_ok=True)
                        q.symlink_to(f.resolve())
    # Fail rather than allowing official caches to supply a project module.
    for n in local:
        if (cache / module_path(n, '.olean')).exists():
            raise RuntimeError('Dependency cache contains a local project module: ' + n)
    env = os.environ.copy()
    env['LEAN_PATH'] = str(out) + os.pathsep + str(cache)
    env['LEAN_SRC_PATH'] = ''
    logs = work / 'logs'
    logs.mkdir(exist_ok=True)
    def save():
        tmp = state_path.with_suffix('.tmp')
        tmp.write_text(json.dumps(state, indent=2) + '\n')
        tmp.replace(state_path)
    suffixes = ['.olean', '.olean.private', '.olean.server', '.ir', '.ir.sig', '.ilean']
    def artifacts(output_root, n):
        return {ext: sha(output_root / module_path(n, ext)) for ext in suffixes if (output_root / module_path(n, ext)).is_file()}
    def compile_module(n, src, package_root, output_root, kind, expected):
        dest = output_root / module_path(n, '.olean')
        old = state['modules'].get(n)
        if old:
            if old['source_sha256'] != expected or not dest.is_file() or artifacts(output_root, n) != old['artifacts']:
                raise RuntimeError('Unverified recorded output: ' + n)
            return
        if args.verify_only:
            raise RuntimeError('Missing successful rebuild record: ' + n)
        if dest.exists():
            raise RuntimeError('Refusing an unrecorded output: ' + str(dest))
        if sha(src) != expected:
            raise RuntimeError('Source hash mismatch: ' + n)
        dest.parent.mkdir(parents=True, exist_ok=True)
        # Never write through an inherited cache companion symlink.
        for ext in suffixes:
            companion = output_root / module_path(n, ext)
            if companion.is_symlink():
                companion.unlink()
        cmd = [lean, '-j1', '-M' + str(args.memory_mb), '-DautoImplicit=false', '-R', str(package_root), '-o', str(dest), str(src)]
        print('BUILD', n, flush=True)
        t = time.monotonic()
        p = subprocess.run(cmd, cwd=package_root, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        (logs / (n + '.log')).write_text(p.stdout)
        if p.returncode:
            print(p.stdout, file=sys.stderr)
            raise RuntimeError('Compilation failed: ' + n + '; exit=' + str(p.returncode))
        if 'sorryAx' in p.stdout:
            raise RuntimeError('Rejected sorryAx diagnostic: ' + n)
        state['modules'][n] = {'kind': kind, 'source_sha256': expected, 'artifacts': artifacts(output_root, n), 'seconds': time.monotonic() - t}
        save()
        print('PASS', n, flush=True)
    # Reuse existing external caches. Recompile absent selected upstream modules
    # only from their hash-checked pinned source files, in dependency order.
    missing = [n for n in upstream if not (lib / module_path(n, '.olean')).exists() and not (cache / module_path(n, '.olean')).exists()]
    visiting = set()
    def external(n):
        if n not in missing:
            return
        if n in visiting:
            raise RuntimeError('External import cycle: ' + n)
        visiting.add(n)
        found = [(p, p / module_path(n, '.lean')) for p in packages if (p / module_path(n, '.lean')).is_file()]
        if len(found) != 1:
            raise RuntimeError('Cannot resolve missing dependency source: ' + n)
        package, src = found[0]
        data = src.read_text()
        for dep in re.findall(r'(?m)^\s*(?:(?:public|private|meta)\s+)*import\s+([A-Za-z0-9_.]+)', data):
            external(dep)
        compile_module(n, src, package, cache, 'rebuilt_upstream_dependency', upstream[n]['sha256'])
        visiting.remove(n)
        missing.remove(n)
    for n in list(missing):
        external(n)
    # Also verify any upstream modules generated by this run and now present.
    for n, r in list(state['modules'].items()):
        if r['kind'] == 'rebuilt_upstream_dependency':
            if artifacts(cache, n) != r['artifacts']:
                raise RuntimeError('Rebuilt dependency output changed: ' + n)
    for n in order:
        r = local[n]
        compile_module(n, source / r['path'], source / 'Lean', out, 'rebuilt_local_source', r['sha256'])
    if targets == ROOTS:
        p = subprocess.run([lean, '-j1', '-M' + str(args.memory_mb), str(source / 'RebuildCheck.lean')], cwd=source, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        (work / 'axioms.txt').write_text(p.stdout)
        print(p.stdout, end='')
        if p.returncode or 'sorryAx' in p.stdout:
            raise RuntimeError('Final axiom check failed')
        reports = re.findall(r'depends on axioms:\s*\[([^]]*)\]', p.stdout)
        if len(reports) != 3 or any(set(re.findall(r'[A-Za-z_.]+', r)) != {'propext', 'Classical.choice', 'Quot.sound'} for r in reports):
            raise RuntimeError('Unexpected final axiom sets')
    summary = {'lean': version, 'local_modules_verified': len(order), 'targets': targets, 'upstream_cache_reused': True, 'upstream_rebuilt': [n for n,r in state['modules'].items() if r['kind'] == 'rebuilt_upstream_dependency'], 'scope': 'selected local-source rebuild, not a clean rebuild of the Lean toolchain or all upstream dependencies'}
    (work / 'rebuild-summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2))

if __name__ == '__main__':
    main()
