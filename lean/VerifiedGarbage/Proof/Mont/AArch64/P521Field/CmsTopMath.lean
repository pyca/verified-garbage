module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsChainMath
import VerifiedGarbage.Proof.Framework.Omega

/-! Complementing the canonical top nine bits and adding their small product. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Ed25519.Word64

theorem cms_top_complement (x : Word) (hx : x.toNat<512) : (x^^^511).toNat=511-x.toNat := by
  have he : x=(x.setWidth 9).setWidth 64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth]
    omega_arith
  have hm : (511 : Word)=(BitVec.allOnes 9).setWidth 64 := rfl
  rw [he,hm,←BitVec.setWidth_xor,BitVec.xor_allOnes]
  simp only [BitVec.toNat_setWidth,BitVec.toNat_not]
  omega_arith

theorem cms_top_add_math (a x : Word) (c : Bool) (ha : a.toNat<16384) (hx : x.toNat<512) :
    (addCarry a (9*(x^^^511)) c).toNat=a.toNat+9*(511-x.toNat)+c.toNat := by
  have hm : ((9 : Word)*(x^^^511)).toNat=9*(511-x.toNat) := by
    rw [BitVec.toNat_mul,show (9 : Word).toNat=9 from rfl,cms_top_complement x hx]
    exact Nat.mod_eq_of_lt (by omega_arith)
  have hc : carryOut a (9*(x^^^511)) c=false := by
    simp only [carryOut,hm,decide_eq_false_iff_not]
    have h := Bool.toNat_le c
    omega_arith
  have he := addCarry_value a (9*(x^^^511)) c
  rw [hm,hc] at he
  simpa only [Bool.toNat_false,Nat.mul_zero,Nat.add_zero] using he

end VG.Proof.Mont.AArch64.P521Field
