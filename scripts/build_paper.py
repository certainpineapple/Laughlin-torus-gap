"""Compile either shared-source edition with XeLaTeX and BibTeX, without latexmk."""
from pathlib import Path
import argparse
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent.parent

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('language', choices=['en', 'zh'])
    parser.add_argument('--build-dir', type=Path)
    args = parser.parse_args()
    build = (args.build_dir or ROOT / 'build' / args.language).resolve()
    build.mkdir(parents=True, exist_ok=True)
    job = 'paper-' + args.language
    engine = shutil.which('xelatex')
    bibtex = shutil.which('bibtex')
    if not engine or not bibtex:
        raise SystemExit('XeLaTeX and BibTeX are required on PATH.')
    engine_args = [engine, '-no-shell-escape', '-interaction=nonstopmode',
                   '-halt-on-error', '-file-line-error',
                   '-output-directory=' + str(build), job + '.tex']
    commands = [engine_args, [bibtex, str(build / job)], engine_args, engine_args]
    for number, command in enumerate(commands, 1):
        result = subprocess.run(command, cwd=ROOT / 'paper', stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, check=False)
        output = result.stdout.decode('utf-8', errors='replace')
        (build / ('pass-' + str(number) + '.txt')).write_text(output, encoding='utf-8')
        if result.returncode:
            print(output[-10000:])
            raise SystemExit(result.returncode)
        print('Completed pass', number, flush=True)
    log = (build / (job + '.log')).read_text(encoding='utf-8', errors='replace')
    problems = re.findall(r'^.*(?:undefined|multiply defined|Missing character:|Overfull \\[hv]box).*$', log, re.M)
    if problems:
        print('\n'.join(problems))
        raise SystemExit('Build has unresolved references, glyphs, or overflow; inspect the log.')
    output_dir = ROOT / 'output' / 'pdf'
    output_dir.mkdir(parents=True, exist_ok=True)
    destination = output_dir / ('laughlin-torus-boson-fermion-' + args.language + '.pdf')
    shutil.copy2(build / (job + '.pdf'), destination)
    print(destination)

if __name__ == '__main__':
    main()
