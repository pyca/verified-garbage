#!/usr/bin/env python3
"""arithsweep.py FILE.lean [--measure]

Replaces bare `omega` with `omega_arith` in FILE (in place), reverting the
occurrences on lines that fail, until the file compiles. With --measure,
prints instructions:u of the original and the result (lean with the
lakefile's options). Restores the original if the result is not faster or
does not compile.
"""
import os, re, subprocess, sys, json

ROOT = os.path.join(subprocess.run(['git', 'rev-parse', '--show-toplevel'], capture_output=True, text=True, check=True).stdout.strip(), 'lean')
ENV = dict(os.environ, PATH=os.path.expanduser('~/.elan/bin') + ':' + os.environ['PATH'])
TOK = re.compile(r'(?<![\w.])omega(?![\w])')
path = os.path.abspath(sys.argv[1])
rel = os.path.relpath(path, ROOT)
orig = open(path).read()

opts = []
for line in open(os.path.join(ROOT, 'lakefile.toml')):
    m = re.match(r'^weak\.([A-Za-z_.]+) = (true|false)', line)
    if m:
        opts.append(f'-D{m.group(1)}={m.group(2)}')


SETUP = None


def setup():
    global SETUP
    if SETUP is None:
        out = subprocess.run(['lake', 'setup-file', '--log-level=warning', rel], cwd=ROOT, env=ENV,
                             capture_output=True, text=True, check=True).stdout
        SETUP = path + '.setup.json'
        open(SETUP, 'w').write(out)
    return SETUP


def run(measure=False):
    if measure:
        cmd = ['lake', 'env', 'lean', '--setup', setup(), '-j1', '-DElab.async=false', '-Dtrace.profiler=true',
               '-Dtrace.profiler.useHeartbeats=true', '-Dtrace.profiler.threshold=1000000000',
               '-Dtrace.Elab.command=true', rel]
    else:
        cmd = ['lake', 'env', 'lean', *opts, rel]
    p = subprocess.run(cmd, cwd=ROOT, env=ENV, capture_output=True, text=True, timeout=1800)
    out = p.stdout + p.stderr
    errs = set()
    for m in re.finditer(r'^' + re.escape(rel) + r':(\d+):\d+: error', out, re.M):
        errs.add(int(m.group(1)))
    hb = None
    if measure:
        hb = sum(float(m.group(1)) for m in re.finditer(r'^\[Elab.command\] \[([0-9.]+)\]', out, re.M))
    return errs, hb


def main():
    measure = '--measure' in sys.argv
    lines = orig.split('\n')
    cand = {i for i, l in enumerate(lines) if TOK.search(l) and not l.lstrip().startswith('--')}
    if not cand:
        print(rel, 'no bare omega'); return
    errs0, ins0 = run(measure)
    if errs0:
        print(rel, 'does not compile as is'); return
    cur = list(lines)
    active = set(cand)
    for i in active:
        cur[i] = TOK.sub('omega_arith', cur[i])
    for it in range(8):
        open(path, 'w').write('\n'.join(cur))
        errs, _ = run()
        if not errs:
            break
        # revert lines with errors; an error may be reported at the start of the
        # enclosing tactic block, so revert the nearest active line at or above
        bad = set()
        for e in errs:
            i = e - 1
            near = [j for j in active if j >= i]
            hit = [j for j in active if j == i]
            if hit:
                bad.add(i)
            else:
                below = sorted(j for j in active if j >= i)
                above = sorted((j for j in active if j < i), reverse=True)
                if above: bad.add(above[0])
                if below: bad.add(below[0])
        if not bad:
            break
        for i in bad:
            cur[i] = lines[i]; active.discard(i)
    else:
        errs = {1}
    if errs:
        open(path, 'w').write(orig)
        print(rel, 'gave up'); return
    if measure:
        _, ins1 = run(True)
    if SETUP:
        os.remove(SETUP)
    if measure:
        verdict = 'KEEP' if ins1 and ins0 and ins1 < ins0 * 0.99 else 'REVERT'
        print(f'{rel}: {len(active)}/{len(cand)} lines, heartbeats {ins0/1e6:.0f}M -> {ins1/1e6:.0f}M '
              f'({100*(ins1-ins0)/ins0:+.1f}%) {verdict}')
        if verdict == 'REVERT':
            open(path, 'w').write(orig)
    else:
        print(f'{rel}: {len(active)}/{len(cand)} lines converted')


main()
