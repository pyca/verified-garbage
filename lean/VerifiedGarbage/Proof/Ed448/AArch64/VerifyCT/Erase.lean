module
public import VerifiedGarbage.Proof.Framework.AArch64.TaintSplit
public import VerifiedGarbage.Impl.Ed448.AArch64.VerifyEquation

import VerifiedGarbage.Proof.Framework.KernelRfl

/-!
# Ed448 verification's equation on AArch64: its comparisons, erased

Untrusted: everything here is checked by Lean. The comparison of two slots
without what the analysis does not read (`Proof/Framework/AArch64/TaintSplit.lean`)
is the same code whatever the slots.
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64

/-- The comparison of two slots, erased: the same code for any slots. -/
def eqSlotsE : Prog isa := Code.eraseT (eqSlots 0 0)

theorem eqSlots_eraseT (a b : Nat) : Code.eraseT (eqSlots a b) = eqSlotsE := by kernel_rfl

end VG.Proof.Ed448.AArch64
