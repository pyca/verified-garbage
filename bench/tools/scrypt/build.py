#!/usr/bin/env python3
"""Build isolated scrypt probes from a checkout, without editing its crates.

The kernel probe copies the generated machine bytes verbatim. Only assembler
directives, symbol references, and the existing branch labels surround them.
The phase probe calls the public API and the generated public primitives.
"""

import base64
import json
import pathlib
import re
import subprocess
import sys


def main():
    if len(sys.argv) != 3:
        raise SystemExit("usage: build.py CHECKOUT OUTPUT_DIRECTORY")
    root = pathlib.Path(sys.argv[1]).resolve()
    out = pathlib.Path(sys.argv[2]).resolve()
    out.mkdir(parents=True, exist_ok=True)
    here = pathlib.Path(__file__).resolve().parent
    names = ["vg_scrypt_blockmix", "vg_scrypt_romix"]
    text = ".intel_syntax noprefix\n.text\n"
    text += "".join(f".global {name}\n" for name in names)
    for name in names:
        src = (root / "crates/verified-garbage-asm-x86_64/src/internal" / f"{name}.rs").read_text()
        body = re.search(r'r#"(.*?)"#', src, re.S).group(1)
        body = re.sub(
            r'\.base64 "([A-Za-z0-9+/=]+)"',
            lambda m: ".byte " + ",".join(str(b) for b in base64.b64decode(m[1])),
            body,
        )
        body = re.sub(r"\{(\w+)\}", r"\1", body)
        text += f"\n.p2align 6\n{name}:\n{body}\n"
    asm = out / "kernel.s"
    asm.write_text(text + '\n.section .note.GNU-stack,"",@progbits\n')
    subprocess.run(
        ["cc", "-O3", "-g", str(here / "kernel.c"), str(asm), "-o", str(out / "kernel")],
        check=True,
    )
    # A separate workspace keeps this probe out of production and coverage.
    manifest = out / "Cargo.toml"
    manifest.write_text(
        '[package]\nname = "scrypt-phases"\nversion = "0.1.0"\nedition = "2024"\n'
        '[workspace]\n[[bin]]\nname = "phases"\n'
        f'path = {json.dumps(str(here / "phases.rs"))}\n'
        '[dependencies]\nverified-garbage = { path = '
        + json.dumps(str(root))
        + ', features = ["cpu-features-env"] }\n'
        'verified-garbage-asm-x86_64 = { path = '
        + json.dumps(str(root / "crates/verified-garbage-asm-x86_64"))
        + ' }\n[profile.release]\ndebug = 1\n'
    )
    subprocess.run(["cargo", "build", "--release", "--manifest-path", str(manifest)], check=True)
    metadata = {
        "checkout": str(root),
        "revision": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip(),
        "dirty_files": subprocess.check_output(["git", "status", "--short"], cwd=root, text=True),
        "rustc": subprocess.check_output(["rustc", "-Vv"], text=True),
        "cc": subprocess.check_output(["cc", "--version"], text=True),
        "cpu": subprocess.check_output(["lscpu"], text=True),
    }
    (out / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")


if __name__ == "__main__":
    main()
