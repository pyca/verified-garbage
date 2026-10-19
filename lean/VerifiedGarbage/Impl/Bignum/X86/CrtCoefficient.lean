module

public import VerifiedGarbage.Impl.Mont.X86.Words
public import VerifiedGarbage.Impl.Mont.X86.MulAt

/-! # Compute the CRT coefficient in the p-factor workspace -/

@[expose] public section
namespace VG.Impl.Bignum.X86
open VG VG.X86 VG.Impl.Mont.X86.Dynamic

/-- Slots six, five and eight contain m_p, m_q and qInv. Slot seven receives h.
`m_q` is reduced first, by multiplications by `R²` (slot four) and by one (slot three). -/
def crtCoefficient (n : Nat) : Prog isa :=
  .seq (callMul n (slot n 5) (slot n 5) (slot n 4)) <|
  .seq (callMul n (slot n 5) (slot n 5) (slot n 3))
    (.seq (subW (contextMod n) (slot n 2) (slot n 7) (slot n 6) (slot n 5))
      (.seq (callMul n (slot n 8) (slot n 8) (slot n 4)) (callMul n (slot n 7) (slot n 7) (slot n 8))))

end VG.Impl.Bignum.X86
