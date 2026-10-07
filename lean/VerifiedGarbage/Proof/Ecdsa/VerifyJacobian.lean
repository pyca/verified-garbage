import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Weierstrass.JacAdd

/-! Verification can compare a Jacobian X against the square of its Z coordinate. -/
namespace VG.Proof.Ecdsa
open Spec.Weierstrass Spec.EcKey Spec.Ecdsa VG.Proof.Weierstrass VG.Proof.Ecdh

theorem verify_eq_jacobian {C : Curve} (hC : Law C)
    {bs : List Byte} (hlen : bs.length=2*C.len+1) {b0 : Byte} (hb0 : bs.head?=some b0)
    {x y : Nat} (hxv : ofBytes ((bs.drop 1).take C.len)=x) (hyv : ofBytes (bs.drop (C.len+1))=y)
    {P : Point C} (hP : ∀ h : Valid C b0 x y,P=.affine ⟨x,h.2.1⟩ ⟨y,h.2.2.1⟩)
    {e r s : Nat} {sig : List Byte} (hr : ofBytes (sig.take C.len)=r) (hs : ofBytes (sig.drop C.len)=s)
    {u v : Nat} (hu : u<C.n) (hv : v<C.n)
    (hue : Fin.ofNat C.n u=Fin.ofNat C.n e*Fin.ofNat C.n s^(C.n-2))
    (hve : Fin.ofNat C.n v=Fin.ofNat C.n r*Fin.ofNat C.n s^(C.n-2))
    {X Y Z : Fe C} (hR : InvJ C X Y Z (add (mul u (G C)) (mul v P)))
    {xo : Nat} (hxo : xo<C.p) (hx : Fin.ofNat C.p xo=X*(Z*Z)^(C.p-2)) :
    verify C bs e sig=decide (Valid C b0 x y ∧ (1≤r ∧ r<C.n) ∧ (1≤s ∧ s<C.n) ∧
      Z*Z≠0 ∧ Fin.ofNat C.n xo=Fin.ofNat C.n r) := by
  by_cases hz : Z=0
  · have hinf := (hR.z_zero_iff hC).mp hz
    have rep : Rep C 0 1 0 (add (mul u (G C)) (mul v P)) := by
      rw [hinf]
      exact rep_infinity' hC
    have out := verify_eq hC hlen hb0 hxv hyv hP hr hs hu hv hue hve rep
      (Nat.pos_of_ne_zero (NeZero.ne C.p)) (by simp only [Fin.ofNat_zero,Lean.Grind.Semiring.zero_mul])
    simpa only [hz,Lean.Grind.Semiring.zero_mul,ne_eq,not_true_eq_false,false_and,and_false,decide_false] using out
  · have rep : ∃ Y',Rep C X Y' (Z*Z) (add (mul u (G C)) (mul v P)) := by
      generalize he : add (mul u (G C)) (mul v P)=Q at hR ⊢
      cases Q with
      | infinity => exact False.elim (hz ((hR.z_zero_iff hC).mpr rfl))
      | affine x y => exact ⟨y*(Z*Z),hC.mul_ne_zero hz hz,(hR.affine_coords hC).1,rfl⟩
    obtain ⟨Y',hrep⟩ := rep
    exact verify_eq hC hlen hb0 hxv hyv hP hr hs hu hv hue hve hrep hxo hx

end VG.Proof.Ecdsa
