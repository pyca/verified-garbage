import VerifiedGarbage.Proof.P256.VerifySparse.Arithmetic
import VerifiedGarbage.Spec.P256

/-! Quotient estimate shared by the fixed small P-256 linear combinations. -/
namespace VG.Proof.P256.Linear
open VG
abbrev p := Spec.P256.p
abbrev radix := 2^256

theorem p_value : p=115792089210356248762697446949407573530086143415290314195533631308867097853951 := rfl
theorem radix_value : radix=115792089237316195423570985008687907853269984665640564039457584007913129639936 := rfl

/-- One high-word estimate leaves at most one prime to add back. The signed
case includes `4a-b`; the nonnegative cases include `12a+9(p-b)`. -/
theorem quotient_bounds (n : Int) (hlo : -(p:Int)≤n) (hhi : n<21*(p:Int)) :
    0≤n/(radix:Int)+1 ∧ n/(radix:Int)+1≤21 ∧
    -(p:Int)≤n-(n/(radix:Int)+1)*(p:Int) ∧
    n-(n/(radix:Int)+1)*(p:Int)<(p:Int) := by
  rw [p_value] at hlo hhi ⊢
  rw [radix_value]
  omega

/-- The final sign-mask add-back is the unique canonical residue. -/
theorem corrected_mod (n : Int) (hlo : -(p:Int)≤n) (hhi : n<21*(p:Int)) :
    let d:=n-(n/(radix:Int)+1)*(p:Int)
    (if d<0 then d+(p:Int) else d)=n%(p:Int) := by
  dsimp only
  obtain ⟨_,_,hd0,hd1⟩ := quotient_bounds n hlo hhi
  by_cases hz : n-(n/(radix:Int)+1)*(p:Int)<0
  · rw [ite_eq_left hz]
    simp only [p_value,radix_value] at hlo hhi hd0 hd1 hz ⊢
    omega
  · rw [ite_eq_right hz]
    simp only [p_value,radix_value] at hlo hhi hd0 hd1 hz ⊢
    omega

end VG.Proof.P256.Linear
