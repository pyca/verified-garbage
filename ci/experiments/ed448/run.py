"""Temporary N2 experiment entry; this branch never changes production assembly."""
import os
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parents[3]
out = Path('/tmp/vg-ed448-arm64')
out.mkdir(exist_ok=True)

def run(*args, **kwargs):
    print('+', *args, flush=True)
    return subprocess.run(args, check=True, cwd=kwargs.pop('cwd', root), **kwargs)

# The normal benchmark checkout excludes Lean; restore sources only for this experiment.
run('git', 'sparse-checkout', 'disable')
run('bash', '-c', "curl --proto '=https' --tlsv1.2 -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none")
os.environ['PATH'] = str(Path.home()/'.elan/bin') + ':' + os.environ['PATH']
toolchain = (root/'lean/lean-toolchain').read_text().strip()
run('elan', 'toolchain', 'install', toolchain)
run('bash', '-o', 'pipefail', '-c', 'python3 ci/fetch_lean_cache.py | zstd -dc | python3 ci/lean_cache.py unpack lean')
run('lake', 'build', '--log-level=warning',
    'VerifiedGarbage.Impl.Ed448.AArch64.VerifyWindow',
    'VerifiedGarbage.Impl.Ed448.SignedWindow',
    'VerifiedGarbage.TCB.AArch64.Print',
    'VerifiedGarbage.Impl.Ed448.AArch64.Verify',
    'VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Resident',
    'VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector.Resident', cwd=root/'lean')
run('lake', 'env', 'lean', '--run', str(root/'ci/experiments/ed448/Prototype.lean'), 'linux', cwd=root/'lean')
run(sys.executable, str(root/'ci/experiments/ed448/vectors.py'))
for cmd in [('clang','--version'), ('openssl','version','-a'), ('lscpu',)]:
    run(*cmd)
for name in ['prototype','whole']:
    run('clang', '-O3', '-I'+str(out), str(root/f'ci/experiments/ed448/{name}.c'), str(out/'prototype.S'),
        *(['-lcrypto'] if name=='whole' else []), '-o', str(out/name))
# All builds precede native timings. The raw results are in the workflow log and summary.
for name, args in [('prototype',[]),('whole',['sha3'])]:
    result = run(str(out/name), *args, capture_output=True, text=True)
    print(result.stderr, end='', flush=True)
    print(result.stdout, end='', flush=True)
    summary = os.environ.get('GITHUB_STEP_SUMMARY')
    if summary:
        with open(summary, 'a') as f:
            f.write(f'\n### Unproved Ed448 {name}\n\n```text\n{result.stderr}{result.stdout}```\n')
