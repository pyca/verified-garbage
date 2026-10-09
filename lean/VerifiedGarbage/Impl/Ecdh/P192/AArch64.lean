import VerifiedGarbage.Impl.Ecdh.AArch64
import VerifiedGarbage.Impl.Ecdsa.P192.AArch64

namespace VG.Impl.Ecdh.AArch64.P192

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64

def ladderQ : LadderCfg :=
  { Ecdsa.AArch64.P192.ladderCfg with G := p192.pt PX PY ONEP }

def qMul : Prog isa :=
  .seq (.block (setConst 4 (p192.sl EXPP) (p192.mont (3 * p192.C.b))))
    (ladder ladderQ)

/-- ECDH with a validated peer and the general complete ladder. -/
def exchange : Prog isa :=
  .seq (.block Cfg.args) <|
  .seq (Cfg.prefix' p192) <|
  .seq (.block (Cfg.peer p192)) <|
  .seq (Cfg.validate p192) <|
  .seq qMul <|
  .seq p192.pPow (Cfg.middle p192)

end VG.Impl.Ecdh.AArch64.P192
