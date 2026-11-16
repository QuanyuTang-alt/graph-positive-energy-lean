#!/usr/bin/env python3
"""Validate a source-only partial snapshot; never a main-theorem certificate."""
import json
from pathlib import Path
import re
import subprocess

root = Path(__file__).resolve().parents[1]
files = subprocess.check_output(['git', 'ls-files'], cwd=root, text=True).splitlines()
assert files, 'Stage the explicitly approved source tree first'

def mask_comments(s):
    out = list(s)
    i, depth = 0, 0
    while i < len(s):
        if depth:
            if s.startswith('/-', i):
                depth += 1
                out[i:i+2] = '  '
                i += 2
            elif s.startswith('-/', i):
                depth -= 1
                out[i:i+2] = '  '
                i += 2
            else:
                if s[i] != '\n':
                    out[i] = ' '
                i += 1
        elif s.startswith('--', i):
            j = s.find('\n', i)
            j = len(s) if j < 0 else j
            out[i:j] = ' ' * (j-i)
            i = j
        elif s.startswith('/-', i):
            depth = 1
            out[i:i+2] = '  '
            i += 2
        else:
            i += 1
    assert depth == 0, 'Unterminated Lean comment'
    return ''.join(out)

for name in files:
    p = root/name
    assert not p.is_symlink(), name
    assert not name.startswith(('.lake/', '.github/workflows/')), name
    assert p.suffix.lower() not in {'.tex','.pdf','.tar','.olean','.ilean','.o','.trace'}, name
    if p.suffix == '.lean':
        text = p.read_text(encoding='utf-8')
        # Copyright/provenance ordinary comments may precede module; documentation may not.
        assert re.match(r'\s*(?:(?:--[^\n]*(?:\n|$))|(?:/-(?![!-])[\s\S]*?-/)\s*)*module\b', text), name
        assert len(text.splitlines()) <= 10000, name
        code = mask_comments(text)
        assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b|sorryAx|Lean\.ofReduceBool', code), name
    if p.suffix in {'.md','.yaml','.json','.lean','.txt','.py','.toml'}:
        text = p.read_text(encoding='utf-8')
        assert not re.search(r'/' + r'(?:Users|home)/|gh[pousr]_[A-Za-z0-9]{15,}|github_pat_[A-Za-z0-9_]{15,}', text), name
manifest = json.loads((root/'lake-manifest.json').read_text())
assert all(p['type'] == 'git' and re.fullmatch('[0-9a-f]{40}',p['rev']) and
           p['url'].startswith('https://github.com/') for p in manifest['packages'])
logs = (root/'verification/axioms.txt').read_text()
assert len(re.findall(r"depends on axioms:", logs)) == 136
for row in logs.splitlines():
    if 'depends on axioms:' in row:
        axioms = row.split('[')[1].split(']')[0].split(', ')
        assert set(axioms) <= {'propext','Classical.choice','Quot.sound'}, row
assert 'Build completed successfully' in (root/'verification/build.txt').read_text()
assert '尚未完成' in (root/'README.md').read_text()
print('PASS: source/module/pin/privacy/no-CI and recorded supporting audits.')
print('76 supporting theorems, 60 definitions. Principal theorems NOT FORMALIZED.')
print('Comparator NOT RUN. Isolated principal acceptance NOT PASSED. Palomar-ready NO.')
