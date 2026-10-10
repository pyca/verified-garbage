import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
import VerifiedGarbage.Impl.Ecdsa.P256.AArch64
import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Jacobian
import VerifiedGarbage.Impl.Weierstrass.AArch64.Forward
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Kernel

namespace VG.Proof.Weierstrass.AArch64.Forward.P256ED
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Weierstrass.AArch64.Forward


def K := VG.Impl.Ecdsa.Verify.AArch64.Cfg.jacWinCfg VG.Impl.Ecdsa.AArch64.p256

def original := fprog K.M (dblJMul K.S K.E K.D)
def optimized := VG.Impl.Weierstrass.AArch64.Forward.optimize original
theorem original_lit : original=P256Bounds.leftED.lit := P256Bounds.leftED.lit_eq
theorem optimized_lit : optimized=P256Bounds.rightED.lit := P256Bounds.rightED.lit_eq

theorem wf : wfK 8192 original (RegSet.empty,false)=true := by
  rw [original_lit]; decide +kernel

theorem leftBound : ∀ i∈original,instrBound i≤8192 := by
  rw [original_lit]; exact bound_of_listAllK (by decide +kernel)

theorem rightBound : ∀ i∈optimized,instrBound i≤8192 := by
  rw [optimized_lit]; exact bound_of_listAllK (by decide +kernel)

theorem checked : OptChecked 8192 original optimized :=
  ⟨rfl,wf,writes_of_bound leftBound,writes_of_bound rightBound⟩

end VG.Proof.Weierstrass.AArch64.Forward.P256ED
