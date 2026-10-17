"""Compare a v2 source archive to this comment-revised release (no Lean execution)."""
from pathlib import Path
import re, json, hashlib, tarfile, argparse
def parts(s):
    """Yield (is_comment,text); nested comments, strings, chars, raw strings, quoted identifiers."""
    i=0; start=0; n=len(s)
    while i<n:
        if s.startswith('--',i) or s.startswith('/-',i):
            if start<i: yield False,s[start:i]
            a=i
            if s.startswith('--',i):
                e=s.find('\n',i); i=n if e<0 else e
            else:
                depth=1;i+=2
                while depth:
                    if i>=n: raise ValueError('Unclosed block comment')
                    if s.startswith('/-',i):depth+=1;i+=2
                    elif s.startswith('-/',i):depth-=1;i+=2
                    else:i+=1
            yield True,s[a:i];start=i;continue
        m=re.match(r'r(#+)?"',s[i:]) if s[i]=='r' and (i==0 or not(s[i-1].isalnum() or s[i-1] in "_'")) else None
        if m:
            closer='"'+(m.group(1) or '');e=s.find(closer,i+len(m[0]))
            if e<0:raise ValueError('Unclosed raw string')
            i=e+len(closer);continue
        if s[i]=='"':
            i+=1
            while i<n:
                if s[i]=='\\':i+=2
                elif s[i]=='"':i+=1;break
                else:i+=1
            else:raise ValueError('Unclosed string')
            continue
        if s[i]=='«':
            e=s.find('»',i+1)
            if e<0:raise ValueError('Unclosed quoted identifier')
            i=e+1;continue
        if s[i]=="'":
            m=re.match(r"'(?:\\(?:u[0-9A-Fa-f]{4}|x[0-9A-Fa-f]{2}|.)|[^'\\\n])'",s[i:])
            if m:i+=len(m[0]);continue
        i+=1
    if start<n:yield False,s[start:]
def noncomments(s):return ''.join(t if not c else '\x00COMMENT\x00' for c,t in parts(s))

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('baseline_v2_archive',type=Path)
    args=ap.parse_args()
    root=Path(__file__).resolve().parent
    report=json.loads((root/'COMMENT_ONLY_VALIDATION.json').read_text())
    assert hashlib.sha256(args.baseline_v2_archive.read_bytes()).hexdigest()==report['baseline_v2_archive_sha256']
    rows=json.loads((root/'source-manifest.json').read_text())
    with tarfile.open(args.baseline_v2_archive) as tf:
        for row in rows:
            before=tf.extractfile('lean/'+row['path']).read().decode()
            after=(root/row['path']).read_bytes()
            assert hashlib.sha256(after).hexdigest()==row['sha256'], row['path']
            assert noncomments(before)==noncomments(after.decode()), row['path']
    print(f'PASS: {len(rows)} modules, identical non-comment streams; no Lean compilation performed')
if __name__=='__main__':main()
