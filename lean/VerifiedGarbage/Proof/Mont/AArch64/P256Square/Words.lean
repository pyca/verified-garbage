import VerifiedGarbage.Proof.Mont.AArch64.P256Square.Arithmetic
import VerifiedGarbage.Proof.Mont.AArch64.Csub

/-! Word-level identities for the shift/subtract P-256 reduction. -/
namespace VG.Proof.Mont.AArch64.P256Square
open VG.Proof.Ed25519.Word64

/-- The two half-word shifts are the low and high words of `u · 2³²`. -/
theorem shifts (u : BitVec 64) :
    u.toNat * 2 ^ 32 = (u <<< 32).toNat + B * (u >>> 32).toNat := by
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, B]
  have hu := u.isLt
  have h := Nat.mod_add_div u.toNat (2 ^ 32)
  have hm := Nat.mod_lt u.toNat (by decide : 0 < 2 ^ 32)
  omega

/-- The second subtraction cannot borrow: `u >> 32` is strictly below positive `u`. -/
theorem high_no_borrow (u : BitVec 64) :
    carryOut u (~~~(u >>> 32)) (carryOut u (~~~(u <<< 32)) true) = true := by
  have hh := sub_borrow u (u >>> 32) (carryOut u (~~~(u <<< 32)) true)
  have ht := (addCarry u (~~~(u >>> 32)) (carryOut u (~~~(u <<< 32)) true)).isLt
  have hhi : (u >>> 32).toNat = u.toNat / 2 ^ 32 := by
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hb := Bool.toNat_le (!(carryOut u (~~~(u <<< 32)) true))
  by_cases hz : u = 0
  · subst hz; decide
  · have hpos : 0 < u.toNat := by
      have hn : u.toNat ≠ 0 := fun h => hz (BitVec.eq_of_toNat_eq h)
      omega
    have hlt : u.toNat / 2 ^ 32 < u.toNat := Nat.div_lt_self hpos (by decide)
    cases h : carryOut u (~~~(u >>> 32)) (carryOut u (~~~(u <<< 32)) true) with
    | false =>
      rw [h, Bool.not_false, Bool.toNat_true, Nat.mul_one, hhi] at hh
      omega
    | true => rfl

/-- The subtraction pair forms the upper two words of `u (p+1)/B`. -/
theorem subtract_pair (u : BitVec 64) :
    let lo := u <<< 32
    let hi := u >>> 32
    let d0 := addCarry u (~~~lo) true
    let d1 := addCarry u (~~~hi) (carryOut u (~~~lo) true)
    u.toNat * ((p+1)/B) = lo.toNat + B*hi.toNat + 2^128*d0.toNat + 2^192*d1.toNat := by
  have h0 := sub_borrow u (u <<< 32) true
  have h1 := sub_borrow u (u >>> 32) (carryOut u (~~~(u <<< 32)) true)
  rw [high_no_borrow] at h1
  simp only [Bool.not_true, Bool.toNat_false, Nat.add_zero, Nat.mul_zero] at h0 h1
  exact reduction_words (shifts u) h0 h1

/-- A four-word carry chain, with its final carry retained. -/
def add4 (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) × Bool :=
  let c0 := carryOut a0 b0 false
  let c1 := carryOut a1 b1 c0
  let c2 := carryOut a2 b2 c1
  ((addCarry a0 b0 false, addCarry a1 b1 c0, addCarry a2 b2 c1,
    addCarry a3 b3 c2), carryOut a3 b3 c2)

def value4 (a : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) : Nat :=
  val4 a.1 a.2.1 a.2.2.1 a.2.2.2

theorem add4_value (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    value4 (add4 a0 a1 a2 a3 b0 b1 b2 b3).1 + R * (add4 a0 a1 a2 a3 b0 b1 b2 b3).2.toNat =
      val4 a0 a1 a2 a3 + val4 b0 b1 b2 b3 := by
  have h0 := addCarry_value a0 b0 false
  have h1 := addCarry_value a1 b1 (carryOut a0 b0 false)
  have h2 := addCarry_value a2 b2 (carryOut a1 b1 (carryOut a0 b0 false))
  have h3 := addCarry_value a3 b3 (carryOut a2 b2 (carryOut a1 b1 (carryOut a0 b0 false)))
  simp only [add4,value4,val4,R,Bool.toNat_false] at *
  omega

def reduceWords (u v w x : BitVec 64) : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 :=
  let lo := u <<< 32
  let hi := u >>> 32
  let d0 := addCarry u (~~~lo) true
  let d1 := addCarry u (~~~hi) (carryOut u (~~~lo) true)
  (add4 v w x d1 lo hi d0 0).1

/-- The four-word reduction implements `(t + low(t)·p)/2⁶⁴` exactly. -/
theorem reduceWords_value (u v w x : BitVec 64) :
    B * value4 (reduceWords u v w x) = val4 u v w x + u.toNat * p := by
  let lo := u <<< 32
  let hi := u >>> 32
  let d0 := addCarry u (~~~lo) true
  let d1 := addCarry u (~~~hi) (carryOut u (~~~lo) true)
  let q := v.toNat + B*w.toNat + 2^128*x.toNat
  have he := add4_value v w x d1 lo hi d0 0
  have hs := subtract_pair u
  change u.toNat * ((p+1)/B) = lo.toNat + B*hi.toNat + 2^128*d0.toNat + 2^192*d1.toNat at hs
  have hq : val4 u v w x = u.toNat + B*q := by
    simp only [val4,q,B,Nat.mul_add,←Nat.mul_assoc]
    omega
  have hr := reduction_round (val4_lt u v w x) u.isLt hq (rfl : q+u.toNat*((p+1)/B)=_)
  have he' : value4 (reduceWords u v w x) + R*(add4 v w x d1 lo hi d0 0).2.toNat =
      q + u.toNat*((p+1)/B) := by
    change value4 (add4 v w x d1 lo hi d0 0).1 + R*(add4 v w x d1 lo hi d0 0).2.toNat = _
    rw [he]
    simp only [val4, B, q]
    rw [show (0 : BitVec 64).toNat = 0 from rfl]
    simp only [B] at hs
    omega
  have hv : value4 (reduceWords u v w x) = q + u.toNat*((p+1)/B) := by
    have hb := Bool.toNat_le (add4 v w x d1 lo hi d0 0).2
    simp only [R] at hr he'
    omega
  rw [hv]
  exact hr.1

end VG.Proof.Mont.AArch64.P256Square
