module

public import VerifiedGarbage.Impl.Ecdh.AArch64
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.AArch64

@[expose] public section

namespace VG.Impl.Ecdh.AArch64.Secp256k1

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64

/-- `R = [k]P`, for the `k` in `K`'s slot and the point `P` at `PX` and `PY`, by
a call of `vg_secp256k1_mul`, with `3 b R mod p` at `EXPP`'s slot for the complete
addition that may follow. -/
def qMul : Prog isa :=
  .seq (.block (setConst 4 (secp256k1.sl EXPP) (secp256k1.mont (3 * secp256k1.C.b))))
    (secp256k1.mulAt "vg_secp256k1_mul" PX PY)

/-- ECDH with a validated peer and the general complete ladder. -/
def exchange : Prog isa :=
  .seq (.block Cfg.args) <|
  .seq (Cfg.prefix' secp256k1) <|
  .seq (.block (Cfg.peer secp256k1)) <|
  .seq (Cfg.validate secp256k1) <|
  .seq qMul <|
  .seq secp256k1.pPow (Cfg.middle secp256k1)

end VG.Impl.Ecdh.AArch64.Secp256k1
