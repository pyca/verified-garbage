module

import VerifiedGarbage.Proof.Bignum.Arm.CombDigitBit
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Bignum.Arm.CombDigitLoad

/-! One tooth appends one bit at its fixed place in the comb digit. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombDigit
open VG VG.Arm VG.Proof.X25519.Arm

abbrev clobbers : List Reg := [.r2,.r9,.r10,.r11,.r12]

def value (bs : List Byte) (N k : Nat) : Nat :=
  if k<N then ((bs.getD (bs.length-1-k/8) 0).toNat / 2^(k%8)) % 2 else 0

theorem value_lt (bs : List Byte) (N k : Nat) : value bs N k < 2 := by
  unfold value
  split
  · exact Nat.mod_lt _ (by decide)
  · omega

private theorem appendBit {a b j : Nat} (ha : a<2^j) (hb : b<2) (hj : j<5) :
    BitVec.ofNat 32 a ||| (BitVec.ofNat 32 b <<< j) = BitVec.ofNat 32 (a+2^j*b) := by
  have pow : 2^j≤16 := Nat.pow_le_pow_right (by decide) (by omega : j≤4)
  have product : 2^j*b≤16 := calc
    2^j*b ≤ 2^j*1 := Nat.mul_le_mul_left _ (by omega)
    _ ≤ 16 := by simpa only [Nat.mul_one] using pow
  have aa : a<2^32 := by omega
  have sum : a+2^j*b<2^32 := by omega
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or,BitVec.toNat_shiftLeft,BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt aa,Nat.mod_eq_of_lt (by omega : b<2^32)]
  have shift : b<<<j<2^32 := by rw [Nat.shiftLeft_eq,Nat.mul_comm]; omega
  rw [Nat.mod_eq_of_lt shift,Nat.mod_eq_of_lt sum]
  rw [Nat.or_comm,←Nat.shiftLeft_add_eq_or_of_lt ha,Nat.shiftLeft_eq]
  rw [Nat.mul_comm b (2^j),Nat.add_comm]

theorem tooth_ok (s : State) {src : BitVec 32} {bs : List Byte} {k N d a j : Nat}
    (source : Source src bs s) (widthBound : N≤8*bs.length) (size : bs.length<2^32)
    (indexFit : k<2^31) (widthFit : N<2^31) (_nextFit : k+d<2^32)
    (digitBound : a<2^j) (tooth : j<5)
    (ptr : s.gpr .r4=src) (length : s.gpr .r5=BitVec.ofNat 32 bs.length)
    (index : s.gpr .r9=BitVec.ofNat 32 k) (width : s.gpr .r8=BitVec.ofNat 32 N)
    (stride : s.gpr .r7=BitVec.ofNat 32 d) (digit : s.gpr .r10=BitVec.ofNat 32 a) :
    WP isa (VG.Impl.Bignum.Arm.CombDigit.tooth j) s fun t =>
      t.gpr .r9=BitVec.ofNat 32 (k+d) ∧
      t.gpr .r10=BitVec.ofNat 32 (a+2^j*value bs N k) ∧
      t.mem=s.mem ∧ Rest clobbers s t := by
  unfold VG.Impl.Bignum.Arm.CombDigit.tooth
  rw [WP.seq_iff]
  refine WP.mono (bit_ok s source widthBound size indexFit widthFit ptr length index width) ?_
  rintro u ⟨bit,memU,restU⟩
  have result : u.gpr .r11=BitVec.ofNat 32 (value bs N k) := by
    rw [bit]
    congr 1
    unfold value
    split
    · rw [←List.getElem_eq_getD 0]
    · rfl
  have old : u.gpr .r10=BitVec.ofNat 32 a := (restU.gpr .r10 (by decide)).trans digit
  have operand : (if j=0 then Op2.reg .r11 else .shifted .r11 .lsl j).eval u =
      some (u.gpr .r11<<<j) := by
    by_cases h : j=0
    · subst j; simp [Op2.eval]
    · simp only [ite_eq_right h,Op2.eval]
      rw [ite_eq_left (by omega : 1≤j ∧ j≤31)]
  refine wp_dp operand fun v one => ?_
  refine wp_dp (op2_reg _ _) fun t two => WP.block_nil ?_
  refine ⟨?_,?_,two.mem.trans (one.mem.trans memU),?_⟩
  · rw [two.gpr]
    change v.gpr .r9+v.gpr .r7=_
    rw [one.other .r9 (by decide),one.other .r7 (by decide),restU.gpr .r9 (by decide),
      restU.gpr .r7 (by decide),index,stride,←BitVec.ofNat_add]
  · rw [two.other .r10 (by decide),one.gpr]
    change u.gpr .r10 ||| (u.gpr .r11<<<j)=_
    rw [old,result,appendBit digitBound (value_lt _ _ _) tooth]
  · exact ((restU.mono (by decide)).trans (one.rest (by decide))).trans
      (two.rest (by decide))

end VG.Proof.Bignum.Arm.CombDigit
