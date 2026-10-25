module

public import VerifiedGarbage.Impl.Sha1.RISCV64
public import VerifiedGarbage.Impl.MdStream.RISCV64

/-!
# Streaming SHA-1: RISC-V implementation

The streaming state (84 bytes at `state`) is the hash value followed by a
64-byte buffer (see `VG.Spec.Sha1.Repr`). `init(state = a0)` stores `H⁽⁰⁾`
(`initWords`); `update` and `finalize` are the generic streaming code
(`Impl/MdStream/RISCV64.lean`) calling `vg_sha1_compress`, with SHA-1's
big-endian length field and digest (`lenBE`, `outBE`).
-/

@[expose] public section

namespace VG.Impl.Sha1.RISCV64.Stream

open VG.RISCV64
open VG.Impl.MdStream.RISCV64 (Params lenBE outBE)

def init : Prog isa := MdStream.RISCV64.initWords Spec.Sha1.H0.toList

def params : Params where
  N := 20
  len := lenBE 20
  out := outBE 5

def update : Prog isa := MdStream.RISCV64.update params "vg_sha1_compress" compress

def finalize : Prog isa := MdStream.RISCV64.finalize params "vg_sha1_compress" compress

end VG.Impl.Sha1.RISCV64.Stream
