"""Measure an unchanged Rust vector test on two library revisions."""
import hashlib
import json
import os
from pathlib import Path
import resource
import shlex
import shutil
import subprocess
import time

root = Path.cwd()
work = Path(os.environ['RUNNER_TEMP']) / 'rsa-test-confirm'
work.mkdir(exist_ok=True)
env = dict(os.environ, WYCHEPROOF_ROOT=str(root / 'wycheproof'))
kind = os.environ.get('RSA_CONFIRM_KIND', 'tests')
target_name = 'verified_garbage' if kind == 'lib' else 'tests'
target_args = ['--lib'] if kind == 'lib' else ['--test', 'tests']
test = os.environ.get('RSA_CONFIRM_TEST', 'wycheproof::rsa_keygen::rsa_keygen_primes')
print('VECTOR_REVISION', subprocess.check_output(['git', '-C', str(root / 'wycheproof'), 'rev-parse', 'HEAD'], text=True).strip(), flush=True)
revisions = {}
binaries = {}
for side in ['base', 'head']:
    checkout = root / side
    build_env = dict(env, CARGO_TARGET_DIR=str(work / ('target-' + side)))
    revisions[side] = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=checkout, text=True).strip()
    result = subprocess.run(['cargo', 'test', *target_args, '--features', 'cpu-features-env', '--no-run', '--message-format=json'], cwd=checkout, env=build_env, check=True, stdout=subprocess.PIPE, text=True)
    artifacts = [json.loads(line) for line in result.stdout.splitlines()]
    binary = next(item['executable'] for item in artifacts if item.get('reason') == 'compiler-artifact' and item.get('executable') and item['target']['name'] == target_name)
    binaries[side] = work / ('tests-' + side)
    shutil.copy2(binary, binaries[side])
    print('BINARY', side, hashlib.sha256(binaries[side].read_bytes()).hexdigest(), flush=True)
assert binaries['base'].read_bytes() != binaries['head'].read_bytes(), 'Comparison binaries are identical'
target = env.get('CARGO_BUILD_TARGET', '')
runner = shlex.split(env.get('CARGO_TARGET_' + target.upper().replace('-', '_') + '_RUNNER', ''))
for round_number in range(3):
    for side in (['base', 'head'] if round_number % 2 == 0 else ['head', 'base']):
        before = resource.getrusage(resource.RUSAGE_CHILDREN)
        start = time.perf_counter()
        result = subprocess.run([*runner, str(binaries[side]), '--exact', test, '--nocapture', '--test-threads=1'], env=env, cwd=root / side, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        wall = time.perf_counter() - start
        after = resource.getrusage(resource.RUSAGE_CHILDREN)
        print(result.stdout, flush=True)
        result.check_returncode()
        assert '1 passed' in result.stdout and '0 failed' in result.stdout, result.stdout
        print('RSA_TEST_CONFIRM ' + json.dumps(dict(round=round_number, side=side, revision=revisions[side], test=test, features=env.get('VG_CPU_FEATURES', ''), wall_s=wall, user_s=after.ru_utime-before.ru_utime, system_s=after.ru_stime-before.ru_stime)), flush=True)
