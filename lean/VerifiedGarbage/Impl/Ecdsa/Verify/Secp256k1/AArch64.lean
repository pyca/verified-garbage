module

public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64
public import VerifiedGarbage.Impl.Ecdh.Secp256k1.AArch64

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.AArch64.Secp256k1

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64

/-- General complete addition uses `a` and `3b`. -/
def slots (c : Ecdsa.AArch64.Cfg) : RcbSlots := { c.rcbSlots with b3 := c.sl EXPP }

def sum (c : Ecdsa.AArch64.Cfg) : Prog isa :=
  .seq (fprogB c.MP' (rcb (slots c) (c.pt UX UY UZ) (c.pt RX RY RZ) (c.pt DX DY DZ)))
    (.block (copy c.n (c.sl RX) (c.sl DX) ++
      (copy c.n (c.sl RY) (c.sl DY) ++ copy c.n (c.sl RZ) (c.sl DZ))))

def points : Prog isa :=
  .seq (bits (secp256k1.sl U) (bitsAt secp256k1.n 0) (8 * secp256k1.n)) <|
  .seq Ecdsa.AArch64.Secp256k1.gMul <|
  .seq (.block (Cfg.save secp256k1)) <|
  .seq (bits (secp256k1.sl V) (bitsAt secp256k1.n 0) (8 * secp256k1.n)) <|
  .seq Ecdh.AArch64.Secp256k1.qMul (sum secp256k1)

def verifyWithPoints (c : Ecdsa.AArch64.Cfg) (pointCode : Prog isa) : Prog isa :=
  .seq (.block (Cfg.args c)) <|
  .seq (Ecdh.AArch64.Cfg.prefixWith c (some D)) <|
  .seq (.block (Cfg.loadS c)) <|
  .seq (.block (Ecdh.AArch64.Cfg.peer c)) <|
  .seq (Ecdh.AArch64.Cfg.validate c) <|
  .seq (Cfg.scalars c) <| .seq c.nPow <|
  .seq (Cfg.uv c) <| .seq pointCode (Cfg.tail c)

def verify : Prog isa := verifyWithPoints secp256k1 points

end VG.Impl.Ecdsa.Verify.AArch64.Secp256k1
