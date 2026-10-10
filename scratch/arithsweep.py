#!/usr/bin/env python3
"""arithsweep.py FILE.lean

Replaces bare `omega` with `omega_arith` in FILE (in place), importing
`VerifiedGarbage.Proof.Framework.Omega` if the file does not already, and
reverting the replacements on lines that fail until the file compiles.
Keeps the result only if it compiles with no error and its heartbeats drop
by more than 1%; otherwise restores the original.

Every run uses the file's `lake setup-file` (Lake's own options and
imports), and a run counts as clean only if `lean` exits 0 with no error.
Run it from inside the checkout (ROOT is the git toplevel's `lean/`), one
file at a time: a file mid-edit breaks the builds of the files importing it.
"""
import os, re, subprocess, sys

TOP = subprocess.run(['git', 'rev-parse', '--show-toplevel'], capture_output=True, text=True,
                     check=True).stdout.strip()
ROOT = os.path.join(TOP, 'lean')
sys.path.insert(0, os.path.join(TOP, 'ci'))
import lean_shards  # noqa: E402

ENV = dict(os.environ, PATH=os.path.expanduser('~/.elan/bin') + ':' + os.environ['PATH'])
TOK = re.compile(r'(?<![\w.])omega(?![\w])')
OMEGA = 'VerifiedGarbage.Proof.Framework.Omega'
path = os.path.abspath(sys.argv[1])
rel = os.path.relpath(path, ROOT)
module = rel[:-5].replace('/', '.')
orig = open(path).read()
SETUP = path + '.setup.json'


def setup():
    p = subprocess.run(['lake', 'setup-file', '--log-level=warning', rel], cwd=ROOT, env=ENV,
                       capture_output=True, text=True)
    if p.returncode != 0:
        raise SystemExit(f'{rel}: lake setup-file failed (an import does not build)')
    open(SETUP, 'w').write(p.stdout)


def run(measure=False):
    """(clean, errors by line, heartbeats)"""
    cmd = ['lake', 'env', 'lean', '--setup', SETUP]
    if measure:
        cmd += ['-j1', '-DElab.async=false', '-Dtrace.profiler=true', '-Dtrace.profiler.useHeartbeats=true',
                '-Dtrace.profiler.threshold=1000000000', '-Dtrace.Elab.command=true']
    p = subprocess.run(cmd + [rel], cwd=ROOT, env=ENV, capture_output=True, text=True, timeout=1800)
    out = p.stdout + p.stderr
    errs = {int(m.group(1)) for m in re.finditer(r'^' + re.escape(rel) + r':(\d+):\d+: error', out, re.M)}
    if p.returncode != 0 and not errs:
        raise SystemExit(f'{rel}: lean failed without an error in the file:\n{out[:500]}')
    hb = sum(float(m.group(1)) for m in re.finditer(r'^\[Elab.command\] \[([0-9.]+)\]', out, re.M))
    return p.returncode == 0 and not errs, errs, hb


def restore(msg):
    open(path, 'w').write(orig)
    print(f'{rel}: {msg}')


def main():
    lines = orig.split('\n')
    cand = {i for i, l in enumerate(lines) if TOK.search(l) and not l.lstrip().startswith('--')}
    if not cand:
        print(f'{rel}: no bare omega'); return
    setup()
    ok0, _, hb0 = run(True)
    if not ok0:
        print(f'{rel}: does not compile as is'); return
    mods = lean_shards.modules()
    closure = lean_shards.closures(lean_shards.imports(mods))
    cur = list(lines)
    added = 0
    if OMEGA not in closure.get(module, ()):
        last = max(i for i, l in enumerate(cur) if l.startswith('import '))
        cur.insert(last + 1, f'import {OMEGA}')
        added = 1
        cand = {i + 1 if i > last else i for i in cand}
        lines = list(cur)
    active = set(cand)
    for i in active:
        cur[i] = TOK.sub('omega_arith', cur[i])
    first = min(cand)
    try:
        open(path, 'w').write('\n'.join(cur))
        if added:
            setup()
        for _ in range(40):
            ok, errs, _ = run()
            if ok:
                break
            if any(e - 1 < first for e in errs):
                restore('errors before the first replacement'); return
            bad = set()
            for e in errs:
                i = e - 1
                if i in active:
                    bad.add(i)
                else:
                    above = [j for j in active if j < i]
                    below = [j for j in active if j >= i]
                    if above: bad.add(max(above))
                    if below: bad.add(min(below))
            if not bad:
                restore('errors on no replaced line'); return
            for i in bad:
                cur[i] = lines[i]; active.discard(i)
            if not active:
                restore('every replacement fails'); return
            open(path, 'w').write('\n'.join(cur))
        else:
            restore('gave up'); return
        ok1, _, hb1 = run(True)
        if not ok1:
            restore('the measured run has errors'); return
        verdict = 'KEEP' if hb1 < hb0 * 0.99 else 'REVERT'
        print(f'{rel}: {len(active)}/{len(cand)} lines{" +import" if added else ""}, '
              f'heartbeats {hb0/1e6:.0f}M -> {hb1/1e6:.0f}M ({100*(hb1-hb0)/hb0:+.1f}%) {verdict}')
        if verdict == 'REVERT':
            open(path, 'w').write(orig)
    except BaseException:
        open(path, 'w').write(orig)
        raise
    finally:
        if os.path.exists(SETUP):
            os.remove(SETUP)


main()
