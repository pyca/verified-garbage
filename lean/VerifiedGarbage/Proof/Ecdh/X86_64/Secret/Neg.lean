import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.NegFields
import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.SelectFields
import VerifiedGarbage.Proof.Weierstrass.JacAdd

/-! Conditional Y negation preserves the selected cached powers and reflects the point. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open Spec.Weierstrass

theorem SecretLay.neg_apart_selected {K : WinCfg} {size : Nat} (hL : SecretLay K size) :
    ∀ i<5,K.E.x+32*i≠K.neg := by
  have hh := hL.nodup
  simp only [localWrites,winOther,List.cons_append,List.nil_append,List.nodup_cons,
    List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or] at hh
  rw [hL.exy,hL.exz] at hh
  intro i hi
  omega

theorem negEnv_readonly {C : Curve} (K : WinCfg) (E : Nat → Fe C) (k j : Nat)
    {x : Nat} (hx : x≠K.E.y) (hn : x≠K.neg) : negEnv K E k j x=E x := by
  simp only [negEnv,Function.update_of_ne hx,Function.update_of_ne hn]

theorem negEnv_point {K : WinCfg} {C : Curve} {size k j : Nat} {E : Nat → Fe C}
    (hL : SecretLay K size) {P : Point C} (hJ : InvJ C (E K.E.x) (E K.E.y) (E K.E.z) P) :
    InvJ C (negEnv K E k j K.E.x) (negEnv K E k j K.E.y) (negEnv K E k j K.E.z)
      (if combWin 5 k j<16 then negPt P else P) := by
  have hx : K.E.x≠K.E.y := by rw [hL.exy]; omega
  have hz : K.E.z≠K.E.y := by rw [hL.exy,hL.exz]; omega
  have hnx := hL.neg_apart_selected 0 (by decide)
  have hnz := hL.neg_apart_selected 2 (by decide)
  simp only [Nat.mul_zero,Nat.add_zero] at hnx
  simp only [Nat.reduceMul,←hL.exz] at hnz
  rw [negEnv_readonly K E k j hx hnx,negEnv_readonly K E k j hz hnz]
  simp only [negEnv,Function.update_self]
  split
  · exact hJ.negY
  · exact hJ

theorem negEnv_cache {K : WinCfg} {C : Curve} {size k j : Nat} {E : Nat → Fe C}
    (hL : SecretLay K size)
    (h2 : E (K.E.x+96)=E K.E.z*E K.E.z)
    (h3 : E (K.E.x+128)=E (K.E.x+96)*E K.E.z) :
    negEnv K E k j (K.E.x+96)=negEnv K E k j K.E.z*negEnv K E k j K.E.z ∧
    negEnv K E k j (K.E.x+128)=negEnv K E k j (K.E.x+96)*negEnv K E k j K.E.z := by
  have hnz := hL.neg_apart_selected 2 (by decide)
  have hn2 := hL.neg_apart_selected 3 (by decide)
  have hn3 := hL.neg_apart_selected 4 (by decide)
  simp only [Nat.reduceMul,←hL.exz] at hnz hn2 hn3
  rw [negEnv_readonly K E k j (by rw [hL.exy]; omega) hn2,
    negEnv_readonly K E k j (by rw [hL.exy,hL.exz]; omega) hnz,
    negEnv_readonly K E k j (by rw [hL.exy]; omega) hn3]
  exact ⟨h2,h3⟩

end VG.Proof.Ecdh.X86_64.Secret
