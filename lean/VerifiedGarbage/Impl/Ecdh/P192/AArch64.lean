module

public import VerifiedGarbage.Impl.Ecdh.AArch64
public import VerifiedGarbage.Impl.Ecdsa.P192.AArch64

@[expose] public section

namespace VG.Impl.Ecdh.AArch64.P192

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64

/-- `R = [k]P`, for the `k` in `K`'s slot and the point `P` at `PX` and `PY`, by
a call of `vg_p192_mul`, with `3 b R mod p` at `EXPP`'s slot for the complete
addition that may follow. -/
def qMul : Prog isa :=
  .seq (.block (setConst 4 (p192.sl EXPP) (p192.mont (3 * p192.C.b))))
    (p192.mulAt "vg_p192_mul" PX PY)

/-- ECDH with a validated peer and the general complete ladder. -/
def exchange : Prog isa :=
  .seq (.block Cfg.args) <|
  .seq (Cfg.prefix' p192) <|
  .seq (.block (Cfg.peer p192)) <|
  .seq (Cfg.validate p192) <|
  .seq qMul <|
  .seq p192.pPow (Cfg.middle p192)

end VG.Impl.Ecdh.AArch64.P192
