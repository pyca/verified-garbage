module

public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCallMont
import Mathlib.Tactic.SplitIfs

/-! The default Montgomery implementation used by AArch64 RSA callers. -/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

def Mont.base : Mont := Mont.calledSquareEight

end VG.Proof.Bignum.AArch64
