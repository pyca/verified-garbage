import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64
import VerifiedGarbage.Impl.Ecdh.P192.AArch64

namespace VG.Impl.Ecdsa.Verify.AArch64.P192

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64

/-- General complete addition uses `a` and `3b`. -/
def slots (c : Ecdsa.AArch64.Cfg) : RcbSlots := { c.rcbSlots with b3 := c.sl EXPP }

def sum (c : Ecdsa.AArch64.Cfg) : Prog isa :=
  .seq (fprogB c.MP' (rcb (slots c) (c.pt UX UY UZ) (c.pt RX RY RZ) (c.pt DX DY DZ)))
    (.block (copy c.n (c.sl RX) (c.sl DX) ++
      (copy c.n (c.sl RY) (c.sl DY) ++ copy c.n (c.sl RZ) (c.sl DZ))))

def points : Prog isa :=
  .seq (bits (p192.sl U) (bitsAt p192.n 0) (8 * p192.n)) <|
  .seq Ecdsa.AArch64.P192.gMul <|
  .seq (.block (Cfg.save p192)) <|
  .seq (bits (p192.sl V) (bitsAt p192.n 0) (8 * p192.n)) <|
  .seq Ecdh.AArch64.P192.qMul (sum p192)

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
