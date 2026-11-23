#!/usr/bin/env python3
"""Checks that `EmitOne.lean --check` agrees with the crates `Emit.lean` wrote,
on its fast path and on its fallback, and that it fails on a crate it would
not write.

Which module's file declares an internal function (`VG.Rust.internalOwner`)
depends on every registration file of the target, and `EmitOne.lean` loads
first only those it is given: alone, the AES-GCM registration would declare in
`gcm.rs` the internal functions `aes.rs` declares (`vg_aes_ctr32`, …), which
Rust rejects (`duplicate_mod`). It then emits every registration file of the
target, as `Emit.lean` does. This checks, after `Emit.lean --check` has passed:

* `EmitOne.lean --check Rc2.AArch64` passes on the fast path (it does not say
  it emits every registration file);
* `EmitOne.lean --check AesGcm.AArch64` passes on the fallback (it says so);
* with `gcm.rs` declaring `vg_aes_ctr32` too (as `aes.rs` does), it fails,
  reporting `gcm.rs` out of date. The file is restored whatever happens.

It first checks its premise in the generated crate: `aes.rs` declares
`vg_aes_ctr32` and `gcm.rs` calls it there.

Run it from the repository root after a full build (CI runs it in the job
that assembles the build, after `Emit.lean --check`).

  check_emit_one.py
"""

import pathlib
import subprocess
import sys

LEAN = pathlib.Path("lean")
SRC = pathlib.Path("crates") / "verified-garbage-asm-aarch64" / "src"
GCM = SRC / "gcm.rs"
FN = "vg_aes_ctr32"
DECL = f'#[rustfmt::skip]\n#[path = "internal/{FN}.rs"]\npub(crate) mod {FN};\n'
CALL = f"sym super::aes::{FN}::{FN}"
FALLBACK = "EmitOne: so it emits every registration file of AArch64"


def emit_one_check(name: str) -> tuple[int, str]:
    r = subprocess.run(["lake", "env", "lean", "--run", "EmitOne.lean", "--check", name],
                       cwd=LEAN, capture_output=True, text=True)
    return r.returncode, r.stdout + r.stderr


def fail(what: str, code: int, out: str) -> int:
    print(f"{what} (exit {code}):\n{out}", file=sys.stderr)
    return 1


def main() -> int:
    gcm = GCM.read_text()
    if DECL not in (SRC / "aes.rs").read_text() or CALL not in gcm:
        print(f"{SRC}/aes.rs no longer declares {FN}, or {GCM} no longer calls it: "
              "choose another registration whose internal functions another module's file "
              "declares", file=sys.stderr)
        return 1
    code, out = emit_one_check("Rc2.AArch64")
    if code != 0 or FALLBACK in out:
        return fail("EmitOne.lean --check Rc2.AArch64 did not pass on its fast path", code, out)
    print("EmitOne.lean --check Rc2.AArch64 passes on its fast path")
    code, out = emit_one_check("AesGcm.AArch64")
    if code != 0 or FALLBACK not in out:
        return fail("EmitOne.lean --check AesGcm.AArch64 did not pass on its fallback", code, out)
    print("EmitOne.lean --check AesGcm.AArch64 passes, emitting every registration file")
    try:
        GCM.write_text(gcm + "\n" + DECL)
        code, out = emit_one_check("AesGcm.AArch64")
    finally:
        GCM.write_text(gcm)
    if code == 0 or f"{GCM.name} is out of date" not in out:
        return fail(f"EmitOne.lean --check AesGcm.AArch64 passed with {GCM.name} declaring {FN}",
                    code, out)
    print(f"EmitOne.lean --check AesGcm.AArch64 fails with {GCM.name} declaring {FN}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
