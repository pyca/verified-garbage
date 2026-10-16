module

public import VerifiedGarbage.Impl.Bignum.Arm.ReduceOperand
public import VerifiedGarbage.Impl.Bignum.Arm.SubModArray

/-! # Compute the CRT residue difference modulo p

Array 6 contains m_p, and array 1 contains m_q copied from q's workspace.
The full-width m_q is reduced modulo p before modular subtraction.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm.Crt
open VG VG.Arm

def difference : Prog isa := .seq (reduceOperand 1) (subModArray 5 6 1)

end VG.Impl.Bignum.Arm.Crt
