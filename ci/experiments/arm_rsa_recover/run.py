#!/usr/bin/env python3
"""Build an isolated unproven recovery experiment using emitted Montgomery code.

No assembly is authored here: instructions are extracted verbatim from the
checked-in Lean emitter output. Build products and synthetic cases go in --work.
"""
import argparse
import hashlib
import json
import platform
from pathlib import Path
import random
import re
import shlex
import struct
import subprocess

ROOT = Path(__file__).resolve().parents[3]


def root_reference(n, exponent, base):
    """Spec.Rsa.recoverStep, via Python's independent modular exponentiation."""
    if not exponent:
        return None
    t = (exponent & -exponent).bit_length() - 1
    y = pow(base, exponent >> t, n)
    if y in (1, n - 1):
        return None
    for _ in range(t):
        x = y * y % n
        if x == 1:
            return y
        if x == n - 1:
            return None
        y = x
    return None


def cases(path, quick):
    rng = random.Random(0x61726D7637)
    entries = []
    for bits in ([512, 1024] if quick else [512, 1024, 2048, 4096]):
        # Fresh primes from OpenSSL are synthetic property-test inputs, not KATs.
        primes = []
        for _ in range(2):
            p = int(subprocess.check_output([
                'openssl', 'prime', '-generate', '-bits', str(bits // 2), '-hex'
            ], text=True).strip(), 16)
            primes.append(p)
        p, q = primes
        n = p * q
        import math
        lam = math.lcm(p - 1, q - 1)
        # Any odd invertible public exponent gives an ed-1 with the right roots.
        public = next(v for v in [65537, 17, 3, 5, 7] if math.gcd(v, lam) == 1)
        private = pow(public, -1, lam)
        length = 8 * ((private.bit_length() + 7) // 8 + (public.bit_length() + 7) // 8)
        for base in [2, 3, 17, 101]:
            entries.append((bits, length, n, public * private - 1, base, 'valid-key'))
        # Invalid-key inputs matter: preserve exactly the spec's root/none result.
        for exponent in [0, 2, 1 << (bits - 1), rng.getrandbits(bits - 1) * 2]:
            entries.append((bits, bits, n, exponent, 2, 'invalid-key'))
    manifest = []
    with path.open('wb') as f:
        f.write(struct.pack('<I', len(entries)))
        for bits, length, n, exponent, base, kind in entries:
            root = root_reference(n, exponent, base)
            R = pow(2, bits, n)
            f.write(struct.pack('<IIII', bits // 32, length, base, root is not None))
            f.write(n.to_bytes(bits // 8, 'little'))
            f.write(exponent.to_bytes(4 * ((length + 31) // 32), 'little'))
            f.write((0 if root is None else root * R % n).to_bytes(bits // 8, 'little'))
            manifest.append(dict(bits=bits, exponent_bits=length, n=str(n),
                                 exponent=str(exponent), base=base, kind=kind,
                                 expected_root=None if root is None else str(root)))
    path.with_suffix('.json').write_text(json.dumps(manifest, indent=2) + '\n')


def extract(path):
    source = (ROOT / 'src/asm/arm/rsa_mont.rs').read_text()
    functions = dict(re.findall(
        r'fn (\w+)\([^)]*\)[^{]*\{\s*core::arch::naked_asm!\(\s*r"(.*?)"',
        source, re.S))
    output = ['.syntax unified', '.arch armv7-a', '.arm', '.text']
    for name in ['vg_rsa_mont_mul', 'vg_rsa_mont_mul_umaal']:
        body = functions[name].replace('{{', '{').replace('}}', '}')
        assert not re.search(r'^bl\s', body, re.M), 'unexpected external dependency'
        output += ['.balign 4', f'.global {name}', f'.type {name}, %function',
                   f'{name}:', body, f'.size {name}, .-{name}']
    output.append('.section .note.GNU-stack,"",%progbits')
    path.write_text('\n'.join(output) + '\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--work', type=Path, required=True)
    parser.add_argument('--cc', default='arm-linux-gnueabihf-gcc')
    parser.add_argument('--runner', default='', help='empty for native ARMv7 execution')
    parser.add_argument('--quick', action='store_true')
    parser.add_argument('--revision', help='source revision, if git is unavailable in the build container')
    args = parser.parse_args()
    args.work.mkdir(parents=True, exist_ok=True)
    build = args.work.resolve()
    extract(build / 'mont.S')
    cases(build / 'cases.bin', args.quick)
    subprocess.run([args.cc, '-O3', '-Wall', '-Wextra', '-Werror', '-march=armv7-a',
                    '-mfpu=vfpv3-d16', '-mfloat-abi=hard', str(Path(__file__).with_name('prototype.c')),
                    str(build / 'mont.S'), '-o', str(build / 'prototype')], check=True)
    metadata = dict(revision=args.revision or subprocess.check_output(['git', '-C', str(ROOT), 'rev-parse', 'HEAD'], text=True).strip(),
                    compiler=subprocess.check_output([args.cc, '--version'], text=True).splitlines()[0],
                    runner=args.runner or 'native', unproven=True)
    (build / 'metadata.json').write_text(json.dumps(metadata, indent=2) + '\n')
    metadata['prototype_sha256'] = hashlib.sha256(Path(__file__).with_name('prototype.c').read_bytes()).hexdigest()
    metadata['generated_mont_sha256'] = hashlib.sha256((ROOT / 'src/asm/arm/rsa_mont.rs').read_bytes()).hexdigest()
    metadata['machine'] = platform.machine()
    metadata['openssl'] = subprocess.check_output(['openssl', 'version'], text=True).strip()
    (build / 'metadata.json').write_text(json.dumps(metadata, indent=2) + '\n')
    for kernel in ['baseline', 'umaal']:
        with (build / f'{kernel}-samples.log').open('w') as samples:
            output = subprocess.check_output(shlex.split(args.runner) +
                                            [str(build / 'prototype'), str(build / 'cases.bin'), kernel],
                                            text=True, stderr=samples)
        (build / f'{kernel}.csv').write_text(output)
        print(output, end='')


if __name__ == '__main__':
    main()
