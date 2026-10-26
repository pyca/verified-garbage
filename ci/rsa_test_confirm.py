"""Measure complete vector tests with the same build path and fresh executables."""
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
stage = work / 'source'
env = dict(os.environ, CARGO_TARGET_DIR=str(work / 'target'), WYCHEPROOF_ROOT=str(root / 'wycheproof'))
kind = env.get('RSA_CONFIRM_KIND', 'tests')
target_name = 'verified_garbage' if kind == 'lib' else 'tests'
target_args = ['--lib'] if kind == 'lib' else ['--test', 'tests']
tests = env.get('RSA_CONFIRM_TESTS', env.get('RSA_CONFIRM_TEST', 'wycheproof::rsa_keygen::rsa_keygen_primes')).split(',')
sides = env.get('RSA_CONFIRM_SIDES', 'base,head').split(',')
print('VECTOR_REVISION', subprocess.check_output(['git', '-C', str(root / 'wycheproof'), 'rev-parse', 'HEAD'], text=True).strip(), flush=True)
revisions = {}
binaries = {}
for side in sides:
    checkout = root / side
    revisions[side] = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=checkout, text=True).strip()
    shutil.rmtree(stage, ignore_errors=True)
    excluded = {'.git', 'lean', 'docs', 'target', 'bench', 'wycheproof'}
    def skip(directory, names):
        return excluded.intersection(names) if Path(directory) == checkout else []
    # Match bench_compare.py: one source path and target directory; new
    # source mtimes force Cargo to rebuild each library revision.
    shutil.copytree(checkout, stage, ignore=skip, copy_function=shutil.copy)
    result = subprocess.run(['cargo', 'test', *target_args, '--features', 'cpu-features-env', '--no-run', '--message-format=json'], cwd=stage, env=env, check=True, stdout=subprocess.PIPE, text=True)
    artifacts = [json.loads(line) for line in result.stdout.splitlines()]
    artifact = next(item for item in artifacts if item.get('reason') == 'compiler-artifact' and item.get('executable') and item['target']['name'] == target_name)
    assert not artifact['fresh'], 'Test binary was unexpectedly reused'
    assert any(item.get('reason') == 'compiler-artifact' and item['target']['name'] == 'verified_garbage' and not item['fresh'] for item in artifacts), 'Library was unexpectedly reused'
    binaries[side] = work / ('tests-' + side)
    shutil.copy2(artifact['executable'], binaries[side])
    print('BINARY', side, hashlib.sha256(binaries[side].read_bytes()).hexdigest(), 'STAGE', stage, 'FRESH', artifact['fresh'], flush=True)
assert len({path.read_bytes() for path in binaries.values()}) == len(sides), 'Comparison binaries are identical'
target = env.get('CARGO_BUILD_TARGET', '')
runner = shlex.split(env.get('CARGO_TARGET_' + target.upper().replace('-', '_') + '_RUNNER', ''))
for test_number, test in enumerate(tests):
    copies = []
    for round_number in range(3):
        if len(sides) == 2:
            order = sides if round_number % 2 == 0 else sides[::-1]
        else:
            order = sides[round_number:] + sides[:round_number]
        for side in order:
            binary = work / f'test-{test_number}-{side}-{round_number}'
            shutil.copy2(binaries[side], binary)
            copies.append(binary)
            before = resource.getrusage(resource.RUSAGE_CHILDREN)
            start = time.perf_counter()
            result = subprocess.run([*runner, str(binary), '--exact', test, '--nocapture', '--test-threads=1'], env=env, cwd=root / side, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            wall = time.perf_counter() - start
            after = resource.getrusage(resource.RUSAGE_CHILDREN)
            print(result.stdout, flush=True)
            result.check_returncode()
            assert '1 passed' in result.stdout and '0 failed' in result.stdout, result.stdout
            print('RSA_TEST_CONFIRM ' + json.dumps(dict(round=round_number, side=side, revision=revisions[side], test=test, features=env.get('VG_CPU_FEATURES', ''), wall_s=wall, user_s=after.ru_utime-before.ru_utime, system_s=after.ru_stime-before.ru_stime, fresh_copy=True, same_source_path=True)), flush=True)
    for binary in copies:
        binary.unlink()
