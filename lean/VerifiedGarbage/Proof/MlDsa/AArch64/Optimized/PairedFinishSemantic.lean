import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFinish

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Response

def FlagMasks (v : BitVec 128) : Prop := ∀e<4,vword v e=0 ∨ vword v e= -1

theorem flag_lanes_zero (v : BitVec 128) :
    (∀e<4,vword v e=0) ↔ vword v 0=0 ∧ vword v 1=0 ∧ vword v 2=0 ∧ vword v 3=0 := by
  constructor
  · intro h
    exact ⟨h 0 (by decide),h 1 (by decide),h 2 (by decide),h 3 (by decide)⟩
  · rintro ⟨h0,h1,h2,h3⟩ e he
    rcases (show e=0 ∨ e=1 ∨ e=2 ∨ e=3 by omega) with rfl | rfl | rfl | rfl <;>
      with_reducible assumption

/-- Exact success-bit reduction for the four SIMD rejection-mask lanes. -/
theorem finishValue_accept (v : BitVec 128) (hv : FlagMasks v) :
    finishValue v= @ite _ (∀e<4,vword v e=0) (Classical.propDecidable _) 1 0 := by
  rw [flag_lanes_zero,finishValue]
  rcases hv 0 (by decide) with h0 | h0 <;>
    rcases hv 1 (by decide) with h1 | h1 <;>
    rcases hv 2 (by decide) with h2 | h2 <;>
    rcases hv 3 (by decide) with h3 | h3 <;>
    rw [h0,h1,h2,h3] <;> simp

end VG.Proof.MlDsa.AArch64.Optimized.Paired
