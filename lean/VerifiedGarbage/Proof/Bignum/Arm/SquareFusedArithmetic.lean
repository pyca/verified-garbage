module

public import VerifiedGarbage.Proof.Bignum.Arm.ShiftLeftStep
public import VerifiedGarbage.Proof.Bignum.Arm.AddCarry

/-! Doubling a two-word cross-product pair and accumulating its diagonal. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm

theorem fused_double_value (lo hi : BitVec 32) :
    (lo+lo).toNat + 2^32 *
        (hi+hi+(if decide (2^32≤lo.toNat+lo.toNat) then 1 else 0 : BitVec 32)).toNat +
      2^64*(hi >>> 31).toNat = 2*(lo.toNat+2^32*hi.toNat) := by
  let c : BitVec 32 := if decide (2^32≤lo.toNat+lo.toNat) then 1 else 0
  have hc : c.toNat≤1 := by unfold c;split <;> decide
  have hl := add_carry lo lo
  have hh := shiftLeft_word hi c hc
  by_cases h : 2^32≤lo.toNat+lo.toNat
  · simp only [c,h,decide_true,↓reduceIte,show (1:BitVec 32).toNat=1 by rfl] at hl hh ⊢
    omega
  · simp only [c,h,decide_false,Bool.false_eq_true,↓reduceIte,show (0:BitVec 32).toNat=0 by rfl] at hl hh ⊢
    omega

theorem fused_finish_value (lo hi dh top : BitVec 32) (ht : top.toNat≤1) :
    lo.toNat+2^32*(hi+dh).toNat+
        2^64*(top+0+(if decide (2^32≤hi.toNat+dh.toNat) then 1 else 0 : BitVec 32)).toNat =
      lo.toNat+2^32*hi.toNat+2^32*dh.toNat+2^64*top.toNat := by
  have ha := add_carry hi dh
  have hc := adc_zero top (decide (2^32≤hi.toNat+dh.toNat)) (by omega)
  by_cases h : 2^32≤hi.toNat+dh.toNat
  · simp only [h,decide_true,↓reduceIte] at ha hc ⊢
    omega
  · simp only [h,decide_false,Bool.false_eq_true,↓reduceIte] at ha hc ⊢
    omega

end VG.Proof.Bignum.Arm
