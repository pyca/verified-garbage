module

public import VerifiedGarbage.Impl.Ecdh.AArch64
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.AArch64

@[expose] public section

namespace VG.Impl.Ecdh.AArch64.Secp256k1

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64

def ladderQ : LadderCfg :=
  { Ecdsa.AArch64.Secp256k1.ladderCfg with G := secp256k1.pt PX PY ONEP }

def qMul : Prog isa :=
  .seq (.block (setConst 4 (secp256k1.sl EXPP) (secp256k1.mont (3 * secp256k1.C.b))))
    (ladder ladderQ)

/-- ECDH with a validated peer and the general complete ladder. -/
def exchange : Prog isa :=
  .seq (.block Cfg.args) <|
  .seq (Cfg.prefix' secp256k1) <|
  .seq (.block (Cfg.peer secp256k1)) <|
  .seq (Cfg.validate secp256k1) <|
  .seq qMul <|
  .seq secp256k1.pPow (Cfg.middle secp256k1)

end VG.Impl.Ecdh.AArch64.Secp256k1
