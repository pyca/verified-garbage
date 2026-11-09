module

public import VerifiedGarbage.Proof.Ed25519.Word64
public import VerifiedGarbage.Impl.Weierstrass.AArch64.NafPrep
public import VerifiedGarbage.Proof.Ed25519.AArch64.Step
public import VerifiedGarbage.Proof.Weierstrass.Naf5
import VerifiedGarbage.Proof.Mont.AArch64.Csub
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Weierstrass.Words
public import VerifiedGarbage.Proof.Weierstrass.PointContract

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64 VG.Proof.Mont.AArch64
open VG.Proof.Ed25519 VG.Proof.Ed25519.AArch64

abbrev nafVal5 (a b c d e : BitVec 64) : Nat :=
  a.toNat+2^64*b.toNat+2^128*c.toNat+2^192*d.toNat+2^256*e.toNat

theorem nafVal5_lt (a b c d e : BitVec 64) : nafVal5 a b c d e<2^320 := by
  have := a.isLt; have := b.isLt; have := c.isLt; have := d.isLt; have := e.isLt
  dsimp only [nafVal5]
  omega_arith

theorem nafVal5_inj {a b c d e f g h i j : BitVec 64}
    (hv : nafVal5 a b c d e=nafVal5 f g h i j) :
    a=f ∧ b=g ∧ c=h ∧ d=i ∧ e=j := by
  have := a.isLt; have := b.isLt; have := c.isLt; have := d.isLt; have := e.isLt
  have := f.isLt; have := g.isLt; have := h.isLt; have := i.isLt; have := j.isLt
  dsimp only [nafVal5] at hv
  refine ⟨?_,?_,?_,?_,?_⟩ <;> apply BitVec.eq_of_toNat_eq <;> omega_arith

def nafSub5 (a b c d e x mask : BitVec 64) : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 :=
  let c0 := Word64.carryOut a (~~~x) true
  let c1 := Word64.carryOut b (~~~mask) c0
  let c2 := Word64.carryOut c (~~~mask) c1
  let c3 := Word64.carryOut d (~~~mask) c2
  (Word64.addCarry a (~~~x) true,Word64.addCarry b (~~~mask) c0,
   Word64.addCarry c (~~~mask) c1,Word64.addCarry d (~~~mask) c2,
   Word64.addCarry e (~~~mask) c3)

theorem nafSub5_value (a b c d e x mask : BitVec 64) :
    let out := nafSub5 a b c d e x mask
    (nafVal5 out.1 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2 +
      nafVal5 x mask mask mask mask)%2^320 = nafVal5 a b c d e := by
  have h0 := sub_borrow a x true
  have h1 := sub_borrow b mask (Word64.carryOut a (~~~x) true)
  have h2 := sub_borrow c mask (Word64.carryOut b (~~~mask) (Word64.carryOut a (~~~x) true))
  have h3 := sub_borrow d mask (Word64.carryOut c (~~~mask)
    (Word64.carryOut b (~~~mask) (Word64.carryOut a (~~~x) true)))
  have h4 := sub_borrow e mask (Word64.carryOut d (~~~mask) (Word64.carryOut c (~~~mask)
    (Word64.carryOut b (~~~mask) (Word64.carryOut a (~~~x) true))))
  have hb := nafVal5_lt a b c d e
  simp only [Bool.not_true,Bool.toNat_false,Nat.add_zero] at h0
  dsimp only [nafSub5,nafVal5] at hb ⊢
  omega_arith

theorem nafWord_toNat (k j : Nat) :
    (BitVec.ofInt 64 (Naf5.digit k j)).toNat =
      if Naf5.negative k j then 2^64-Naf5.magnitude k j else Naf5.magnitude k j := by
  have hb := Naf5.magnitude_le k j
  simp only [Naf5.digit,BitVec.toNat_ofInt]
  cases hn : Naf5.negative k j
  · simp only [Bool.false_eq_true,ite_false]
    change ((Naf5.magnitude k j:Int)%18446744073709551616).toNat=_
    omega_arith
  · have hp := Naf5.negative_magnitude_pos k j hn
    simp only [ite_true]
    change ((-(Naf5.magnitude k j:Int))%18446744073709551616).toNat=_
    omega_arith

theorem nafSign_toNat (k j : Nat) :
    (0#64-(BitVec.ofInt 64 (Naf5.digit k j)>>>63)).toNat =
      if Naf5.negative k j then 2^64-1 else 0 := by
  have hb := Naf5.magnitude_le k j
  have hp := Naf5.negative_magnitude_pos k j
  simp only [BitVec.toNat_sub,BitVec.toNat_zero,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,nafWord_toNat]
  cases hn : Naf5.negative k j
  · simp only [Bool.false_eq_true,ite_false]; omega_arith
  · have hp := hp hn
    simp only [ite_true]; omega_arith

/-- Five adjacent extract-right instructions implement a whole-number shift. -/
theorem nafShift5_value (a b c d e : BitVec 64) :
    nafVal5 ((b++a).extractLsb' 1 64) ((c++b).extractLsb' 1 64)
      ((d++c).extractLsb' 1 64) ((e++d).extractLsb' 1 64) (e>>>1) = nafVal5 a b c d e/2 := by
  have extr (hi lo : BitVec 64) : ((hi++lo).extractLsb' 1 64).toNat = lo.toNat/2+2^63*(hi.toNat%2) := by
    rw [BitVec.extractLsb'_toNat,BitVec.toNat_append,←Nat.shiftLeft_add_eq_or_of_lt lo.isLt,
      Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow]
    have := hi.isLt; have := lo.isLt
    omega_arith
  simp only [nafVal5,extr,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  omega_arith

end VG.Proof.Weierstrass.AArch64
