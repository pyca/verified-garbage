module

public import VerifiedGarbage.Proof.Bignum.Words

/-! Append a contiguous block of exponent bytes without padding. -/

@[expose] public section
namespace VG.Proof.Bignum.CrtWindowFive
open VG VG.Proof.Bignum

theorem pre_append_drop (bs : List Byte) (i n : Nat) (h : i+n ≤ bs.length) :
    pre bs i * 256 ^ n + pre (bs.drop i) n = pre bs (i+n) := by
  induction n with
  | zero => simp only [Nat.pow_zero,Nat.mul_one,pre_zero,Nat.add_zero]
  | succ n ih =>
    rw [← Nat.add_assoc] at h ⊢
    rw [pre_succ (bs.drop i) (by simp only [List.length_drop]; omega),
      pre_succ bs (by omega),← ih (by omega),Nat.pow_succ]
    simp only [List.getElem_drop]
    grind

end VG.Proof.Bignum.CrtWindowFive
