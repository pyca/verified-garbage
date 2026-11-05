#!/usr/bin/env python3
"""Run a command with matching x86 AES-GCM-SIV feature ceilings.

Only removes capabilities; never enables instructions absent from the host.
OpenSSL 4.x documents these logical-vector bit positions in OPENSSL_ia32cap(3).
AWS-LC also honors the first two vectors of OPENSSL_ia32cap.
"""

import argparse
import os
import subprocess


PROFILES = {
    "scalar": "none",
    "aesni": "aes,ssse3",
    "pclmul": "pclmulqdq,ssse3",
    "aesni_pclmul": "aes,pclmulqdq,ssse3",
    "scalar_avx2": "avx,avx2",
    "aesni_avx2": "aes,ssse3,avx,avx2",
    "pclmul_avx2": "pclmulqdq,ssse3,avx,avx2",
    "aesni_pclmul_avx": "aes,pclmulqdq,ssse3,avx,avx2",
    "vaes": "aes,ssse3,avx,avx2,vaes",
    "vpclmul": "pclmulqdq,ssse3,avx,avx2,vpclmulqdq",
    "vaes_pclmul": "aes,pclmulqdq,ssse3,avx,avx2,vaes",
    "aesni_vpclmul": "aes,pclmulqdq,ssse3,avx,avx2,vpclmulqdq",
    "vaes_vpclmul": "aes,pclmulqdq,ssse3,avx,avx2,vaes,vpclmulqdq",
    "avx512": "aes,pclmulqdq,ssse3,avx,avx2,vaes,vpclmulqdq,avx512f,avx512bw,avx512vl",
}

# Also clear other crypto/vector capabilities not named in these profiles.
# Preserve baseline SSE2 and OpenSSL's CPU-vendor/cache-topology flags.
BITS = [
    {"pclmulqdq": 33, "ssse3": 41, "aes": 57, "avx": 60},
    {"bmi1": 3, "avx2": 5, "bmi2": 8, "avx512f": 16,
     "avx512dq": 17, "adx": 19, "avx512ifma": 21, "avx512cd": 28,
     "sha": 29, "avx512bw": 30, "avx512vl": 31, "gfni": 40,
     "vaes": 41, "vpclmulqdq": 42},
]


def environment(profile):
    features = PROFILES[profile]
    allowed = set(features.split(","))
    masks = [sum(1 << bit for name, bit in vector.items() if name not in allowed)
             for vector in BITS]
    return {"VG_CPU_FEATURES": features,
            "OPENSSL_ia32cap": ":".join(f"~0x{mask:x}" for mask in masks) + ":0:0:0"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("profile", choices=PROFILES)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    env = environment(args.profile)
    print(" ".join(f"{k}={v}" for k, v in env.items()), flush=True)
    command = args.command
    if command[:1] == ["--"]:
        command = command[1:]
    if command:
        raise SystemExit(subprocess.call(command, env=os.environ | env))


if __name__ == "__main__":
    main()
