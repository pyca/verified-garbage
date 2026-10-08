"""Experimental N2 sampling pass; writes measurements only outside the checkout."""
import glob
from pathlib import Path
import subprocess
import sys

candidates = sorted(glob.glob('/usr/lib/linux-tools/*/perf'))
if not candidates:
    subprocess.run(['sudo', 'apt-get', 'update', '-qq'], check=True)
    subprocess.run(['sudo', 'apt-get', 'install', '-y', 'linux-tools-generic'], check=True)
    candidates = sorted(glob.glob('/usr/lib/linux-tools/*/perf'))
if not candidates:
    raise SystemExit('No concrete perf executable installed')
perf = candidates[-1]
binary = Path(sys.argv[1]).resolve()
data = '/tmp/vg-mldsa-profile.data'
print(f'Profiling {binary} using {perf}', flush=True)
command = [
    'sudo', 'env', 'VG_BENCH_MODULES=mldsa65', 'VG_CPU_FEATURES=sha3',
    perf, 'record', '-e', 'cpu-clock:u', '-F', '997', '-o', data, '--',
    str(binary), 'mldsa65_sign/verified-garbage/', '--bench', '--noplot',
    '--warm-up-time', '1', '--measurement-time', '20', '--sample-size', '100',
    '--nresamples', '1000',
]
subprocess.run(command, check=True)
subprocess.run([
    'sudo', perf, 'report', '-i', data, '--stdio', '--no-children',
    '--percent-limit', '0.5', '--sort', 'symbol',
], check=True)
