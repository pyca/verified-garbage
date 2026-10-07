import VerifiedGarbage.Proof.Ecdh.Exchange
import VerifiedGarbage.Proof.Weierstrass.JacSecret

/-! ECDH uses only the affine x-coordinate and the infinity test. -/
namespace VG.Proof.Ecdh
open Spec.Weierstrass Spec.EcKey VG.Proof.Weierstrass VG.Proof.EcKey

def XOnly (C : Curve) (X Z : Fe C) (P : Point C) : Prop :=
  (Z=0 ↔ P=.infinity) ∧ ∀ x y,P=.affine x y → x=X*Z^(C.p-2)

theorem xOnly_of_jac {C : Curve} (hC : Law C) {X Y Z : Fe C} {P : Point C}
    (hJ : InvJ C X Y Z P) : XOnly C X (Z*Z) P := by
  refine ⟨hJ.square_z_zero_iff hC,?_⟩
  intro x y he
  subst P
  exact hJ.x_eq_square_z hC

theorem exchange_xOnly {C : Curve} {d : Nat} {bs : List Byte}
    (hlen : bs.length=2*C.len+1) {b0 : Byte} (hb0 : bs.head?=some b0)
    {x y : Nat} (hxv : ofBytes ((bs.drop 1).take C.len)=x)
    (hyv : ofBytes (bs.drop (C.len+1))=y) {P : Point C}
    (hP : ∀ h : Valid C b0 x y,P=.affine ⟨x,h.2.1⟩ ⟨y,h.2.2.1⟩)
    {X Z : Fe C} (hR : d<C.n → XOnly C X Z (mul d P))
    {xo : Nat} (hxo : xo<C.p) (hxoX : Fin.ofNat C.p xo=X*Z^(C.p-2)) :
    Spec.Ecdh.exchange C d bs=
      if (1≤d ∧ d<C.n) ∧ Valid C b0 x y ∧ Z≠0 then some (toBytes C.len xo) else none := by
  unfold Spec.Ecdh.exchange
  rw [decode_eq hlen hb0 hxv hyv]
  by_cases hd : 1≤d ∧ d<C.n
  · by_cases hV : Valid C b0 x y
    · simp only [hd,hV,and_self,ite_true,dite_true,true_and]
      rw [← hP hV]
      have hr := hR hd.2
      by_cases hZ : Z=0
      · rw [hr.1.mp hZ]
        simp only [ne_eq,hZ,not_true_eq_false,ite_false]
      · simp only [ne_eq,hZ,not_false_eq_true,ite_true]
        generalize hQ : mul d P=Q at hr
        cases Q with
        | infinity => exact absurd (hr.1.mpr rfl) hZ
        | affine a b => rw [fe_eq hxo ((hr.2 a b rfl).trans hxoX.symm)]
    · simp only [hd,hV,and_self,ite_true,dite_false,false_and,and_false,ite_false]
  · simp only [hd,false_and,ite_false]

end VG.Proof.Ecdh
