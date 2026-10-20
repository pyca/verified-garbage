module

public import VerifiedGarbage.Proof.Mont.X86.ContextFrame
import VerifiedGarbage.Proof.Bignum.Math

/-! # Arithmetic facts obtained from a runtime Montgomery context -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont

theorem Context.odd {n size m : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) : m % 2 = 1 := by
  have hi := h.inverse
  have hmod : (m * w32 s.mem base 0 + 1) % 2 = 0 := by omega
  have hm : m % 2 = 0 ∨ m % 2 = 1 := by omega
  rcases hm with hm | hm
  · rw [Nat.add_mod, Nat.mul_mod, hm] at hmod
    simp at hmod
  · exact hm

theorem Context.coprime {n size m : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) : Nat.Coprime (2 ^ (64 * n)) m :=
  VG.Proof.Bignum.coprime_pow2 h.odd _

/-- The right-to-left exponentiation step consumes one bit. -/
theorem exponent_step_value (y b e : Nat) :
    (if e % 2 = 1 then y * b else y) * (b * b) ^ (e / 2) = y * b ^ e := by
  have he : e = e % 2 + 2 * (e / 2) := by omega
  have hp : b * b = b ^ 2 := by simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
  rw [hp, ← Nat.pow_mul]
  have hpowe : b ^ e = b ^ (e % 2) * b ^ (2 * (e / 2)) := by
    rw [← Nat.pow_add]
    exact congrArg (b ^ ·) he
  rw [hpowe]
  have hm : e % 2 = 0 ∨ e % 2 = 1 := by omega
  rcases hm with hm | hm
  · rw [hm]; simp
  · rw [hm]; simp only [ite_true, Nat.pow_one, Nat.mul_assoc]

end VG.Proof.Mont.X86.Dynamic
