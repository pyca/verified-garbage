module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtNarrowPower

/-! # The CRT coefficient `h = (m_p - m_q) qInv mod p` at p's own width

The narrow workspace holds p, prepared at its width; p's full-width workspace
holds `m_q` in array 1, `qInv` in array 4, `m_p` in array 6 and a cleared
array 5. `qInv mod p` is kept in array 4 while `m_q` is reduced; the result
goes to array 5.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm.Crt
open VG VG.Arm

/-- `qInv mod p` into the narrow array 1 and back to the full array 4. -/
def inverseHalf : Prog isa := .seq (reduceHalf 224 4) (copyOut 224 4 1)
/-- `m_p - (m_q mod p) mod p` into the narrow array 6. -/
def differenceHalf : Prog isa := .seq (reduceHalf 224 1) (.seq (copyLow 224 6 5) (subModArray 6 5 1))
/-- `qInv mod p` again, in Montgomery form, times the difference, into the full array 5. -/
def productHalf : Prog isa := .seq (copyLow 224 4 1) (.seq (montOp 1 1 4) (.seq (montOp 5 6 1) (copyOut 224 5 5)))
def coefficient : Prog isa := .seq inverseHalf (.seq differenceHalf productHalf)

end VG.Impl.Bignum.Arm.Crt
