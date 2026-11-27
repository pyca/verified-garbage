module

public import VerifiedGarbage.Impl.Ecdh.AArch64
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.AArch64
public import VerifiedGarbage.Impl.Scrub.AArch64.Scrub

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

namespace VG.Impl.Ecdh.AArch64.Fn

/-- ECDH over secp256k1 as emitted: its code, then the registers it writes
that the calling convention does not preserve cleared, but the 32 bits of its
result (`Impl.Scrub.AArch64.scrubAll`; it uses no stack), so that it returns
without secret residue. -/
def exchangeSecp256k1 : Prog VG.AArch64.isa :=
  VG.Impl.Scrub.AArch64.scrubAll 0 32
    ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x16, .x17],
     [.v28, .v29],
     []⟩
    VG.Impl.Ecdh.AArch64.Secp256k1.exchange

end VG.Impl.Ecdh.AArch64.Fn
