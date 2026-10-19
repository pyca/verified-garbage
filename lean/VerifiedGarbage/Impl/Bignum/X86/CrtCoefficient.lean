module

public import VerifiedGarbage.Impl.Bignum.X86.ReduceOperand

/-! # Compute the CRT coefficient in the p-factor workspace -/

@[expose] public section
namespace VG.Impl.Bignum.X86
open VG VG.X86 VG.Impl.Mont.X86.Dynamic

/-- Slots six, five and eight contain m_p, m_q and qInv. Slot seven receives h. -/
def crtCoefficient (n : Nat) : Prog isa :=
  .seq (reduceOperand n 5)
    (.seq (subW (contextMod n) (slot n 2) (slot n 7) (slot n 6) (slot n 5))
      (.seq (mul (contextMod n) 0 (slot n 2) (slot n 8) (slot n 8) (slot n 4))
        (mul (contextMod n) 0 (slot n 2) (slot n 7) (slot n 7) (slot n 8))))

end VG.Impl.Bignum.X86
