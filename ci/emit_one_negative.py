#!/usr/bin/env python3
"""Checks that `EmitOne.lean` refuses a registration file whose internal
functions another module's file declares, rather than write them into its own.

Which module's file declares an internal function (`VG.Rust.internalOwner`)
depends on every registration file of the target, and `EmitOne.lean` loads
only those it is given: the AES-GCM registration alone would declare in
`gcm.rs` the internal functions `aes.rs` declares (`vg_aes_ctr32`, …), which
Rust rejects (`duplicate_mod`), and `--check` would then pass on those files.
This runs `EmitOne.lean --check AesGcm.AArch64` and checks that it fails,
naming `aes.rs`, and that it does not report `gcm.rs` out of date (the refusal
comes before any file is compared). It first checks its premise in the
generated crate: `aes.rs` declares `vg_aes_ctr32` and `gcm.rs` calls it there.

Run it from the repository root after a full build (CI runs it in the job
that assembles the build, after `Emit.lean --check`).

  emit_one_negative.py
"""

import pathlib
import subprocess
import sys

LEAN = pathlib.Path("lean")
SRC = pathlib.Path("crates") / "verified-garbage-asm-aarch64" / "src"
TARGET = "AesGcm.AArch64"
FN = "vg_aes_ctr32"
DECL = f'#[path = "internal/{FN}.rs"]'
CALL = f"sym super::aes::{FN}::{FN}"
REFUSAL = "which aes.rs declares"


def main() -> int:
    if DECL not in (SRC / "aes.rs").read_text() or CALL not in (SRC / "gcm.rs").read_text():
        print(f"{SRC}/aes.rs no longer declares {FN}, or {SRC}/gcm.rs no longer calls it: "
              "choose another registration whose internal functions another module's file "
              "declares", file=sys.stderr)
        return 1
    r = subprocess.run(["lake", "env", "lean", "--run", "EmitOne.lean", "--check", TARGET],
                       cwd=LEAN, capture_output=True, text=True)
    out = r.stdout + r.stderr
    if r.returncode != 0 and REFUSAL in out and FN in out and "out of date" not in out:
        print(f"EmitOne.lean --check {TARGET} refuses the internal functions aes.rs declares")
        return 0
    print(f"EmitOne.lean --check {TARGET} did not refuse the internal functions aes.rs "
          f"declares (exit {r.returncode}):\n{out}", file=sys.stderr)
    return 1


if __name__ == "__main__":
    sys.exit(main())
