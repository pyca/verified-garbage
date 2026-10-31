"""Unverified kernel experiment; not a public API or OpenSSL benchmark."""
import csv
import hashlib
import io
import json
import platform
import shutil
import statistics
import subprocess
import tempfile
from pathlib import Path
root = Path(__file__).parent
assert platform.machine() == 'ppc64le', platform.machine()
print('Native architecture:', platform.machine(), flush=True)
for line in Path('/proc/cpuinfo').read_text().splitlines()[:40]:
    if line.startswith(('cpu', 'clock', 'revision')):
        print(line, flush=True)
for path in sorted(root.glob('*')):
    if path.is_file():
        print(path.name, hashlib.sha256(path.read_bytes()).hexdigest(), flush=True)
subprocess.run(['cc', '--version'], check=True)
variants = ['scalar', 'table_loop']
with tempfile.TemporaryDirectory() as td:
    td = Path(td)
    binary = td/'probe'
    subprocess.run(['cc', '-O3', '-mcpu=power8', str(root/'probe.c'),
                    str(root/'sha256-probe.s'), '-o', str(binary)], check=True)
    actual = subprocess.run([str(binary)], input=(root/'input.bin').read_bytes(),
                            stdout=subprocess.PIPE, check=True).stdout
    expected = (root/'expected.bin').read_bytes()
    assert actual == b''.join(expected[i:i+32]*2 for i in range(0, len(expected), 32))
    print('PASS: 32 Spec-derived cases x 2 kernels. Each timed size also checks the candidate against the proven scalar baseline.', flush=True)
    raw = []
    for copy in range(8):
        fresh = td/f'probe-{copy}'
        shutil.copy(binary, fresh)
        output = subprocess.run([str(fresh), '--bench'], stdout=subprocess.PIPE,
                                check=True, text=True).stdout
        for n, sample, v, ns in csv.reader(io.StringIO(output)):
            raw.append({'copy': copy, 'blocks': int(n), 'sample': int(sample),
                        'variant': variants[int(v)], 'ns': float(ns)})
    Path('sha256-table-kernel-samples.json').write_text(json.dumps(raw, indent=2)+'\n')
    print('Timings include a 32-byte state reset. 25 samples, rotated interleaving, 50ms warmup, eight fresh binary copies. The table pointer uses an extra experimental ABI argument. No public API or OpenSSL comparison.', flush=True)
    for n in [1, 16, 256]:
        best = {}
        for v in variants:
            medians = [statistics.median(r['ns'] for r in raw if r['copy'] == c and
                       r['blocks'] == n and r['variant'] == v) for c in range(8)]
            best[v] = min(medians)
            print(f'{n*64} bytes {v}: {min(medians):.3f} ns best, {max(medians):.3f} ns max copy median', flush=True)
        print(f'{n*64} bytes scalar -> table_loop: {(1-best["table_loop"]/best["scalar"])*100:.2f}% less time', flush=True)
