"""Experimental shared-vs-inline comparison; no measurements enter the checkout."""
import os
from pathlib import Path
import subprocess
import sys
import bench_compare

SYMBOL = 'vg_keccak_resident_sha3_internal'


def rounds_from_module(text):
    lines = text.splitlines(keepends=True)
    start = next(i for i, line in enumerate(lines) if line.startswith('        "movz x16,'))
    end = next(i for i in range(start, len(lines)) if lines[i].strip() == '"ret",')
    return ''.join(lines[start:end])


def inline(text, rounds):
    needle = '        "bl {' + SYMBOL + '}",\n'
    replaced = text.replace(needle, rounds)
    return ''.join(line for line in replaced.splitlines(keepends=True)
                   if SYMBOL + ' = sym ' not in line)


def measure(binary, label, references=False):
    print('RESIDENT COMPARISON: ' + label, flush=True)
    env = {**os.environ, 'VG_CPU_FEATURES': 'sha3',
           'VG_BENCH_MODULES': 'mldsa44 mldsa65 mldsa87',
           'CRITERION_HOME': '/tmp/vg-mldsa-resident-' + label}
    pattern = '_sign/' if references else '_sign/verified-garbage/'
    subprocess.run([binary, pattern, '--bench', '--noplot', '--warm-up-time', '1',
                    '--measurement-time', '5', '--sample-size', '100',
                    '--nresamples', '5000'], env=env, check=True)


def main():
    root = Path(__file__).resolve().parent.parent
    assembly = root / 'src/asm/aarch64'
    saved = {p: p.read_text() for p in assembly.glob('mldsa*.rs')}
    mixed = rounds_from_module((assembly / 'resident.rs').read_text())
    original = Path(__file__).with_name('mldsa_resident_original.body').read_text()
    assert original.splitlines()[-1].strip() == '"ret",'
    original = ''.join(original.splitlines(keepends=True)[:-1])
    assert sum(text.count('"bl {' + SYMBOL + '}"') for text in saved.values()) > 0
    measure(sys.argv[1], 'shared-mix10', references=True)
    try:
        for label, rounds in [('inline-mix10', mixed), ('inline-original', original)]:
            for path, text in saved.items():
                path.write_text(inline(text, rounds))
            binary = bench_compare.build(root / 'bench')
            measure(binary, label)
    finally:
        for path, text in saved.items():
            path.write_text(text)


if __name__ == '__main__':
    main()
