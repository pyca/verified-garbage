module

public import VerifiedGarbage.Impl.Ecdh.AArch64
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.AArch64
public import VerifiedGarbage.Impl.Residue.AArch64.Scrub

@[expose] public section

namespace VG.Impl.Ecdh.AArch64.BrainpoolP512r1

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64

/-- `R = [k]P`, for the `k` in `K`'s slot and the point `P` at `PX` and `PY`, by
a call of `vg_brainpoolp512r1_mul`, with `3 b R mod p` at `EXPP`'s slot for the complete
addition that may follow. -/
def qMul : Prog isa :=
  .seq (.block (setConst 8 (brainpoolp512r1.sl EXPP) (brainpoolp512r1.mont (3 * brainpoolp512r1.C.b))))
    (brainpoolp512r1.mulAt "vg_brainpoolp512r1_mul" PX PY)

/-- ECDH with a validated peer and the general complete ladder. -/
def exchange : Prog isa :=
  .seq (.block Cfg.args) <|
  .seq (Cfg.prefix' brainpoolp512r1) <|
  .seq (.block (Cfg.peer brainpoolp512r1)) <|
  .seq (Cfg.validate brainpoolp512r1) <|
  .seq qMul <|
  .seq brainpoolp512r1.pPow (Cfg.middle brainpoolp512r1)

end VG.Impl.Ecdh.AArch64.BrainpoolP512r1

namespace VG.Impl.Ecdh.AArch64.Fn

/-- ECDH over brainpoolP512r1 as emitted: its code, then the registers it writes
that the calling convention does not preserve cleared, but the 32 bits of its
result (`Impl.Residue.AArch64.scrubAll`; it uses no stack), so that it returns
without secret residue. -/
def exchangeBrainpoolP512r1 : Prog VG.AArch64.isa :=
  VG.Impl.Residue.AArch64.scrubAll 0 32
    ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
     [.v16, .v17, .v18, .v24, .v25, .v26, .v28, .v29],
     []⟩
    VG.Impl.Ecdh.AArch64.BrainpoolP512r1.exchange

end VG.Impl.Ecdh.AArch64.Fn
