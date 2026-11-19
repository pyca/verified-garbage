module

public import VerifiedGarbage.Impl.Ecdh.AArch64
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP320r1.AArch64

@[expose] public section

namespace VG.Impl.Ecdh.AArch64.BrainpoolP320r1

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64

/-- `R = [k]P`, for the `k` in `K`'s slot and the point `P` at `PX` and `PY`, by
a call of `vg_brainpoolp320r1_mul`, with `3 b R mod p` at `EXPP`'s slot for the complete
addition that may follow. -/
def qMul : Prog isa :=
  .seq (.block (setConst 5 (brainpoolp320r1.sl EXPP) (brainpoolp320r1.mont (3 * brainpoolp320r1.C.b))))
    (brainpoolp320r1.mulAt "vg_brainpoolp320r1_mul" PX PY)

/-- ECDH with a validated peer and the general complete ladder. -/
def exchange : Prog isa :=
  .seq (.block Cfg.args) <|
  .seq (Cfg.prefix' brainpoolp320r1) <|
  .seq (.block (Cfg.peer brainpoolp320r1)) <|
  .seq (Cfg.validate brainpoolp320r1) <|
  .seq qMul <|
  .seq brainpoolp320r1.pPow (Cfg.middle brainpoolp320r1)

end VG.Impl.Ecdh.AArch64.BrainpoolP320r1
