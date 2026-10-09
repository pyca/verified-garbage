import VerifiedGarbage.Impl.Ed448.AArch64.VerifyWindow
import VerifiedGarbage.Proof.X448.AArch64.Base.Erase

/-!
# Ed448 verification's equation on AArch64: its comparisons, erased

Untrusted: everything here is checked by Lean. The comparison of two slots
without what the analysis does not read (`Proof/Framework/AArch64/TaintSplit.lean`)
is the same code whatever the slots.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64

/-- The comparison of two slots, erased: the same code for any slots. -/
def eqSlotsE : List Instr := (eqSlots 0 0).map Instr.eraseT

theorem eqSlots_eraseT (a b : Nat) : (eqSlots a b).map Instr.eraseT = eqSlotsE := by kernel_rfl

end VG.Proof.Ed448.AArch64
