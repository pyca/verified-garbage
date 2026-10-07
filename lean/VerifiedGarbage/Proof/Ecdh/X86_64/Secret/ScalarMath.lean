import VerifiedGarbage.Proof.Weierstrass.Window5Secret

/-! Multiplication composition used by the radix-32 accumulator. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG.Proof.Weierstrass VG.Spec.Weierstrass

theorem mul_composition {C : Curve} (hC : Law C) {P : Point C}
    (hP : onCurve C P=true) (a b : Nat) : mul a (mul b P)=mul (a*b) P := by
  obtain ⟨A,_,f,hf⟩ := hC.group
  apply hf.inj (hC.onCurve_mul (hC.onCurve_mul hP b) a) (hC.onCurve_mul hP _)
  rw [hf.mul (hC.onCurve_mul hP b),hf.mul hP,hf.mul hP,Int.natCast_mul]
  exact (Lean.Grind.IntModule.mul_zsmul _ _ _).symm

end VG.Proof.Ecdh.X86_64.Secret
