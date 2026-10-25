module

public import VerifiedGarbage.Impl.Sm3.RISCV64
public import VerifiedGarbage.Impl.MdStream.RISCV64

/-!
# Streaming SM3: RISC-V implementation

The streaming state (96 bytes at `state`) is the hash value followed by a
64-byte buffer (see `VG.Spec.Sm3.Repr`). `init(state = a0)` stores `IV`
(`initWords`); `update` and `finalize` are the generic streaming code
(`Impl/MdStream/RISCV64.lean`) calling `vg_sm3_compress`, with SM3's
big-endian length field and digest (`lenBE`, `outBE`).
-/

@[expose] public section

namespace VG.Impl.Sm3.RISCV64.Stream

open VG.RISCV64
open VG.Impl.MdStream.RISCV64 (Params lenBE outBE)

def init : Prog isa := MdStream.RISCV64.initWords Spec.Sm3.iv.toList

def params : Params where
  N := 32
  len := lenBE 32
  out := outBE 8

def update : Prog isa := MdStream.RISCV64.update params "vg_sm3_compress" compress

def finalize : Prog isa := MdStream.RISCV64.finalize params "vg_sm3_compress" compress

end VG.Impl.Sm3.RISCV64.Stream
