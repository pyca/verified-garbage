module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.ProductMath
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionArithmetic
import VerifiedGarbage.Proof.Framework.Omega

/-! Small shifts have the same word carries as multiplication by powers of two. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64

theorem cms_shift_low (x : Word) (k : Nat) : x<<<k=BitVec.ofNat 64 (2^k)*x := by
  rw [BitVec.shiftLeft_eq_mul_twoPow,BitVec.mul_comm]
  have he : BitVec.twoPow 64 k=BitVec.ofNat 64 (2^k) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_twoPow,BitVec.toNat_ofNat]
  rw [he]

theorem cms_shift_extract (n m : Word) (k : Nat) (hk : k=1 ∨ k=2 ∨ k=3) :
    (n++m).extractLsb' (64-k) 64=
      addCarry (BitVec.ofNat 64 (2^k)*n) (mulHi (BitVec.ofNat 64 (2^k)) m) false := by
  rcases hk with rfl|rfl|rfl <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [VG.Proof.Mont.AArch64.P521Square.extract_toNat,addCarry,mulHi,
      BitVec.toNat_add,BitVec.toNat_mul,BitVec.toNat_ofNat,Nat.reducePow,Nat.reduceSub,
      Nat.reduceMod,Bool.toNat_false,Nat.add_zero]
  all_goals
    have hn := n.isLt
    have hm := m.isLt
    omega_arith

theorem cms_shift_carry (n m : Word) (k : Nat) (hk : k=1 ∨ k=2 ∨ k=3) :
    carryOut (BitVec.ofNat 64 (2^k)*n) (mulHi (BitVec.ofNat 64 (2^k)) m) false=false := by
  rcases hk with rfl|rfl|rfl <;>
    simp only [carryOut,mulHi,BitVec.toNat_mul,BitVec.toNat_ofNat,Nat.reducePow,Nat.reduceMod,
      Bool.toNat_false,Nat.add_zero,decide_eq_false_iff_not]
  all_goals
    have hn := n.isLt
    have hm := m.isLt
    omega_arith

end VG.Proof.Mont.AArch64.P521Field
