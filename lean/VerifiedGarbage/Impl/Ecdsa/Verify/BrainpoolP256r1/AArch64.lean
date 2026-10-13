module

public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP256r1.AArch64

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP256r1

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64

/-- General complete addition uses `a` and `3b`. -/
def slots (c : Ecdsa.AArch64.Cfg) : RcbSlots := { c.rcbSlots with b3 := c.sl EXPP }

def sum (c : Ecdsa.AArch64.Cfg) : Prog isa :=
  .seq (fprogB c.MP' (rcb (slots c) (c.pt UX UY UZ) (c.pt RX RY RZ) (c.pt DX DY DZ)))
    (.block (copy c.n (c.sl RX) (c.sl DX) ++
      (copy c.n (c.sl RY) (c.sl DY) ++ copy c.n (c.sl RZ) (c.sl DZ))))

/-- `[u]G + [v]Q`: `u`, then `v`, to `K`'s slot, which the calls of
`vg_brainpoolp256r1_mul` read, with `r` kept meanwhile in `EM`'s slot (free until the final
check) and put back. -/
def points : Prog isa :=
  .seq (.block (copy brainpoolp256r1.n (brainpoolp256r1.sl EM) (brainpoolp256r1.sl K) ++ copy brainpoolp256r1.n (brainpoolp256r1.sl K) (brainpoolp256r1.sl U))) <|
  .seq Ecdsa.AArch64.BrainpoolP256r1.gMul <|
  .seq (.block (Cfg.save brainpoolp256r1)) <|
  .seq (.block (copy brainpoolp256r1.n (brainpoolp256r1.sl K) (brainpoolp256r1.sl V))) <|
  .seq Ecdh.AArch64.BrainpoolP256r1.qMul <|
  .seq (sum brainpoolp256r1) (.block (copy brainpoolp256r1.n (brainpoolp256r1.sl K) (brainpoolp256r1.sl EM)))

def verifyWithPoints (c : Ecdsa.AArch64.Cfg) (pointCode : Prog isa) : Prog isa :=
  .seq (.block (Cfg.args c)) <|
  .seq (Ecdh.AArch64.Cfg.prefixWith c (some D)) <|
  .seq (.block (Cfg.loadS c)) <|
  .seq (.block (Ecdh.AArch64.Cfg.peer c)) <|
  .seq (Ecdh.AArch64.Cfg.validate c) <|
  .seq (Cfg.scalars c) <| .seq c.nPow <|
  .seq (Cfg.uv c) <| .seq pointCode (Cfg.tail c)

def verify : Prog isa := verifyWithPoints brainpoolp256r1 points

end VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP256r1
