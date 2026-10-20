module

public import VerifiedGarbage.Proof.Bignum.Arm.CombDigit
public import VerifiedGarbage.Proof.Rsa.FixedBaseComb
import VerifiedGarbage.Proof.Ffdh.CombBitBytes

/-! The gathered five-byte bits are the reviewed comb's exponent columns. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombDigit
open VG VG.Arm

theorem value_eq_bit (bs : List Byte) (N k : Nat) (size : N≤8*bs.length)
    (bound : Spec.Rsa.os2ip bs<2^N) :
    value bs N k=VG.Proof.Rsa.FixedBaseComb.bit (Spec.Rsa.os2ip bs) k := by
  unfold value VG.Proof.Rsa.FixedBaseComb.bit
  by_cases inside : k<N
  · rw [ite_eq_left inside]
    rw [←List.getElem_eq_getD 0]
    exact (VG.Proof.Ffdh.CombBitBytes.os2ip_bit bs k (by omega)).symm
  · rw [ite_eq_right inside]
    have limit : Spec.Rsa.os2ip bs<2^k :=
      Nat.lt_of_lt_of_le bound (Nat.pow_le_pow_right (by decide) (by omega))
    rw [Nat.div_eq_of_lt limit]

theorem prefixValue_eq_digit (bs : List Byte) (N i : Nat) (size : N≤8*bs.length)
    (bound : Spec.Rsa.os2ip bs<2^N) :
    prefixValue bs N i (Spec.Rsa.FixedBaseComb.rows N) 5=
      VG.Proof.Rsa.FixedBaseComb.digit N (Spec.Rsa.os2ip bs) i := by
  simp only [prefixValue,value_eq_bit bs N _ size bound,VG.Proof.Rsa.FixedBaseComb.digit,
    Nat.pow_zero,Nat.pow_one,show 2^2=4 from rfl,show 2^3=8 from rfl,show 2^4=16 from rfl,
    Nat.zero_mul,Nat.add_zero,Nat.one_mul,Nat.zero_add]

theorem code_digit_ok (s : State) {src : BitVec 32} {bs : List Byte} {N i : Nat}
    (source : Source src bs s) (widthBound : N≤8*bs.length) (size : bs.length<2^32)
    (positions : i+5*Spec.Rsa.FixedBaseComb.rows N<2^31) (widthFit : N<2^31)
    (bound : Spec.Rsa.os2ip bs<2^N)
    (ptr : s.gpr .r4=src) (length : s.gpr .r5=BitVec.ofNat 32 bs.length)
    (row : s.gpr .r6=BitVec.ofNat 32 i)
    (stride : s.gpr .r7=BitVec.ofNat 32 (Spec.Rsa.FixedBaseComb.rows N))
    (width : s.gpr .r8=BitVec.ofNat 32 N) :
    WP isa VG.Impl.Bignum.Arm.CombDigit.code s fun t =>
      t.gpr .r11=BitVec.ofNat 32 (VG.Proof.Rsa.FixedBaseComb.digit N (Spec.Rsa.os2ip bs) i) ∧
      (t.gpr .r11).toNat<32 ∧ t.mem=s.mem ∧ VG.Proof.X25519.Arm.Rest clobbers s t := by
  simpa only [prefixValue_eq_digit bs N i widthBound bound] using
    code_ok s source widthBound size positions widthFit ptr length row stride width

end VG.Proof.Bignum.Arm.CombDigit
