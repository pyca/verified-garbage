module

public import VerifiedGarbage.Impl.Sha3.AArch64.RoundConstants
public import VerifiedGarbage.Spec.Sha3
import VerifiedGarbage.Proof.Sha3.RcLit
meta import VerifiedGarbage.Proof.Sha3.RcLit

/-! # The tables of round constants are the specification's -/

@[expose] public section

namespace VG.Proof.Sha3.AArch64.RoundConstants

open VG.Impl.Sha3.AArch64.RoundConstants
open VG.Spec.Sha3 (RC)

theorem rcs_eq : ∀ r < 24, rcs.getD r 0 = RC r := by lit_decide
theorem rcs2_eq : ∀ r < 24, rcs2.getD (2 * r) 0 = RC r ∧ rcs2.getD (2 * r + 1) 0 = RC r := by lit_decide
theorem rcs_length : rcs.length = 24 := rfl
theorem rcs2_length : rcs2.length = 48 := rfl

end VG.Proof.Sha3.AArch64.RoundConstants
