import VerifiedGarbage.Proof.Weierstrass.Comb
import VerifiedGarbage.Proof.Weierstrass.FastNaf

/-! Group identities for interleaved public two-scalar multiplication. -/
namespace VG.Proof.Weierstrass
open Spec.Weierstrass

variable {C : Curve}

/-- Accumulating Q's digit followed by G's digit groups the two independent sums. -/
theorem Law.joint_add (hC : Law C) {A B D E : Point C}
    (hA : onCurve C A=true) (hB : onCurve C B=true)
    (hD : onCurve C D=true) (hE : onCurve C E=true) :
    Spec.Weierstrass.add (Spec.Weierstrass.add (Spec.Weierstrass.add A B) E) D = Spec.Weierstrass.add (Spec.Weierstrass.add A D) (Spec.Weierstrass.add B E) := by
  obtain ⟨M, _, f, hf⟩ := hC.group
  apply hf.inj (hC.onCurve_add (hC.onCurve_add (hC.onCurve_add hA hB) hE) hD)
    (hC.onCurve_add (hC.onCurve_add hA hD) (hC.onCurve_add hB hE))
  rw [hf.add (hC.onCurve_add (hC.onCurve_add hA hB) hE) hD,
    hf.add (hC.onCurve_add hA hB) hE, hf.add hA hB,
    hf.add (hC.onCurve_add hA hD) (hC.onCurve_add hB hE),
    hf.add hA hD, hf.add hB hE]
  grind

/-- A shared double advances both scalar accumulators. -/
theorem Law.joint_double (hC : Law C) {P Q : Point C}
    (hP : onCurve C P=true) (hQ : onCurve C Q=true) (a b : Nat) :
    Spec.Weierstrass.add (Spec.Weierstrass.add (mul a P) (mul b Q)) (Spec.Weierstrass.add (mul a P) (mul b Q)) =
      Spec.Weierstrass.add (mul (2*a) P) (mul (2*b) Q) := by
  have hA := hC.onCurve_mul hP a
  have hB := hC.onCurve_mul hQ b
  obtain ⟨M, _, f, hf⟩ := hC.group
  apply hf.inj (hC.onCurve_add (hC.onCurve_add hA hB) (hC.onCurve_add hA hB))
    (hC.onCurve_add (hC.onCurve_mul hP _) (hC.onCurve_mul hQ _))
  rw [hf.add (hC.onCurve_add hA hB) (hC.onCurve_add hA hB), hf.add hA hB,
    hf.add (hC.onCurve_mul hP _) (hC.onCurve_mul hQ _),
    hf.mul hP, hf.mul hQ, hf.mul hP, hf.mul hQ]
  have ha : ((2*a : Nat) : Int) = (a : Int)+(a : Int) := by omega
  have hb : ((2*b : Nat) : Int) = (b : Int)+(b : Int) := by omega
  rw [ha,hb,Lean.Grind.IntModule.add_zsmul,Lean.Grind.IntModule.add_zsmul]
  grind

/-- The accumulator after processing all digits down to j. -/
def jointPoint (P Q : Point C) (u v j : Nat) : Point C :=
  add (mul (FastNaf.residual 7 u j) P) (mul (FastNaf.residual 5 v j) Q)

theorem jointPoint_curve (hC : Law C) {P Q : Point C}
    (hP : onCurve C P=true) (hQ : onCurve C Q=true) (u v j : Nat) :
    onCurve C (jointPoint P Q u v j)=true :=
  hC.onCurve_add (hC.onCurve_mul hP _) (hC.onCurve_mul hQ _)

theorem jointPoint_zero (P Q : Point C) (u v : Nat) :
    jointPoint P Q u v 0=add (mul u P) (mul v Q) := by
  simp only [jointPoint,FastNaf.residual_zero]

theorem jointPoint_topB (P Q : Point C) {B u v : Nat}
    (hu : u<2^B) (hv : v<2^B) : jointPoint P Q u v (B+1)=.infinity := by
  rw [jointPoint,FastNaf.residual_zero_top 7 hu,FastNaf.residual_zero_top 5 hv]
  have h0 (X : Point C) : mul 0 X=.infinity := by rw [Spec.Weierstrass.mul]; rfl
  rw [h0 P,h0 Q]; rfl

theorem jointPoint_top (P Q : Point C) {u v : Nat}
    (hu : u<2^256) (hv : v<2^256) : jointPoint P Q u v 257=.infinity :=
  jointPoint_topB P Q hu hv

/-- The shared double followed by the peer digit and then generator digit is one Horner step. -/
theorem jointPoint_step (hC : Law C) {P Q : Point C}
    (hP : onCurve C P=true) (hQ : onCurve C Q=true) (u v j : Nat) :
    add (add (add (jointPoint P Q u v (j+1)) (jointPoint P Q u v (j+1)))
      (FastNaf.point C Q 5 v j)) (FastNaf.point C P 7 u j)=jointPoint P Q u v j := by
  rw [jointPoint,hC.joint_double hP hQ]
  rw [hC.joint_add (hC.onCurve_mul hP _) (hC.onCurve_mul hQ _)
    (FastNaf.onCurve_point hC hP 7 u j) (FastNaf.onCurve_point hC hQ 5 v j)]
  rw [FastNaf.add_step hC hP,FastNaf.add_step hC hQ]
  rfl

end VG.Proof.Weierstrass
