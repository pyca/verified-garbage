module

public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Sum
public import VerifiedGarbage.Impl.Ecdh.P192.AArch64

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.AArch64.P192

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64

abbrev slots := GeneralSum.slots
abbrev sum := GeneralSum.sum

/-- `[u]G + [v]Q`: `u`, then `v`, to `K`'s slot, which the calls of
`vg_p192_mul` read, with `r` kept meanwhile in `EM`'s slot (free until the final
check) and put back. -/
def points : Prog isa :=
  .seq (.block (copy p192.n (p192.sl EM) (p192.sl K) ++ copy p192.n (p192.sl K) (p192.sl U))) <|
  .seq Ecdsa.AArch64.P192.gMul <|
  .seq (.block (Cfg.save p192)) <|
  .seq (.block (copy p192.n (p192.sl K) (p192.sl V))) <|
  .seq Ecdh.AArch64.P192.qMul <|
  .seq (sum p192) (.block (copy p192.n (p192.sl K) (p192.sl EM)))

def verifyWithPoints (c : Ecdsa.AArch64.Cfg) (pointCode : Prog isa) : Prog isa :=
  .seq (.block (Cfg.args c)) <|
  .seq (Ecdh.AArch64.Cfg.prefixWith c (some D)) <|
  .seq (.block (Cfg.loadS c)) <|
  .seq (.block (Ecdh.AArch64.Cfg.peer c)) <|
  .seq (Ecdh.AArch64.Cfg.validate c) <|
  .seq (Cfg.scalars c) <| .seq c.nPow <|
  .seq (Cfg.uv c) <| .seq pointCode (Cfg.tail c)

def verify : Prog isa := verifyWithPoints p192 points

end VG.Impl.Ecdsa.Verify.AArch64.P192
