module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.Gcd64Body
import VerifiedGarbage.Proof.RsaKeyGen.X86.Gcd64Loop

/-! # A complete native 64-bit GCD from any odd second operand -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Gcd64
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Gcd64

theorem code_ok {s : State} {base : Addr} {size count : Nat}
    (W : Ws s base size 2 count) (space : 15 ≤ count) (odd : num s.mem base 2 1 % 2 = 1) :
    WP isa code s fun t => Ws t base size 2 count ∧ Keep base 2 arrays slots s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t ∧
      num t.mem base 2 1 = Nat.gcd (num s.mem base 2 0) (num s.mem base 2 1) := by
  have aBound : num s.mem base 2 0 < 2 ^ 64 := val32_lt ..
  have bBound : num s.mem base 2 1 < 2 ^ 64 := val32_lt ..
  have bPositive : 0 < num s.mem base 2 1 := by omega
  have product : num s.mem base 2 0 * num s.mem base 2 1 < 2 ^ 128 := by
    have first := Nat.mul_lt_mul_of_pos_right aBound bPositive
    have second := Nat.mul_lt_mul_of_pos_left bBound (Nat.two_pow_pos 64)
    have H := Nat.lt_trans first second
    rw [show 2 ^ 64 * 2 ^ 64 = (2 : Nat) ^ 128 by rw [← Nat.pow_add]] at H
    exact H
  refine WP.mono (code_iter W space) fun t T => ?_
  have value := T.value
  rw [VG.Proof.RsaKeyGen.gcdIter_eq 128 _ _ odd product] at value
  exact ⟨T.workspace, T.frame, T.rest, congrArg Prod.snd value⟩

end VG.Proof.RsaKeyGen.X86.Gcd64
