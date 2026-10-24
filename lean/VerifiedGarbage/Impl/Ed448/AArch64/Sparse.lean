module

public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Joint

/-! Ed448 verification with public joint sparse scalar multiplication.
Decoding, canonicality checks, cofactoring, final comparisons and restoration
are the existing implementation's; only the double-scalar computation changes. -/

@[expose] public section

namespace VG.Impl.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (slot)
open VG.Impl.X448.AArch64.Base (constSlot)

/-- Compare [4]Q with [4]R; Q already includes both scalar multiples. -/
def cross : Prog isa :=
  .seq Point56.doubleCall <| .seq Point56.doubleCall <|
  .seq (.block (Point56.copy3 0 3 ++ Curve448.AArch64.copy (slot 3) RX ++
    Curve448.AArch64.copy (slot 4) RY ++ constSlot (slot 5) 1)) <|
  .seq Point56.doubleCall <| .seq Point56.doubleCall <|
  X448.AArch64.Fast.opsK [.mul (slot 12) (slot 0) (slot 5), .mul (slot 13) (slot 3) (slot 2),
    .mul (slot 14) (slot 1) (slot 5), .mul (slot 15) (slot 4) (slot 2)]

/-- The fixed-work prefix, grouped for its caller proofs. -/
def prepare : Prog isa := .seq (.seq wfront normalizeKey) oddTable

def verifyEquation : Prog isa :=
  .seq wfront <| .seq normalizeKey <| .seq oddTable <| .seq joint <| .seq cross wfinish

end VG.Impl.Ed448.AArch64.Sparse
