module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.Trial
public import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.RsaKeyGen.Trial16

/-! The native trial reducer uses the existing radix-2^16 arithmetic. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86

def trialWord (digit acc inverse divisor : BitVec 32) : BitVec 32 :=
  ((((digit + acc) * inverse) &&& 65535) * divisor + (digit + acc)) >>> 16

theorem trial_reduce (s : State) :
    WP isa (.block Impl.Dsa.X86.Generation.trialReduce) s fun t =>
      t.gpr .eax = trialWord (s.gpr .eax) (s.gpr .edi) (s.gpr .esi) (s.gpr .ebx) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ecx, .edx] s t := by
  unfold Impl.Dsa.X86.Generation.trialReduce
  refine wp_addS rfl fun s₁ U₁ _ => wp_movS rfl fun s₂ U₂ _ =>
    wp_mul fun s₃ M₃ => wp_logicS (Or.inl rfl) rfl fun s₅ U₅ => wp_mul fun s₆ M₆ =>
    wp_addS rfl fun s₇ U₇ _ => wp_shr (by decide) fun t U₈ _ => WP.block_nil ?_
  refine ⟨?_, by rw [U₈.mem, U₇.mem, M₆.mem, U₅.mem, M₃.mem, U₂.mem, U₁.mem],
    ((((((U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))).trans
      (M₃.keeps.mono (by decide))).trans
      (U₅.keeps.mono (by decide))).trans (M₆.keeps.mono (by decide))).trans
      (U₇.keeps.mono (by decide))).trans (U₈.keeps.mono (by decide))⟩
  rw [U₈.gpr, U₇.gpr, M₆.eax, U₅.gpr, M₃.eax,
    U₂.other .eax (by decide), U₁.gpr,
    U₂.other .esi (by decide), U₁.other .esi (by decide),
    U₅.other .ebx (by decide),
    M₃.other .ebx (by decide) (by decide), U₂.other .ebx (by decide), U₁.other .ebx (by decide),
    M₆.other .ecx (by decide) (by decide), U₅.other .ecx (by decide),
    M₃.other .ecx (by decide) (by decide), U₂.gpr, U₁.gpr]
  rfl

theorem trial_word_value {digit acc inverse divisor : BitVec 32}
    (hd : digit.toNat < 2 ^ 16) (ha : acc.toNat < 2 * divisor.toNat)
    (hs : 3 ≤ divisor.toNat ∧ divisor.toNat < 8162) :
    (trialWord digit acc inverse divisor).toNat =
      (digit.toNat + acc.toNat +
        (digit.toNat + acc.toNat) * inverse.toNat % 2 ^ 16 * divisor.toNat) / 2 ^ 16 := by
  have hx : (digit + acc).toNat = digit.toNat + acc.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hq : (((digit + acc) * inverse) &&& 65535).toNat =
      (digit.toNat + acc.toNat) * inverse.toNat % 2 ^ 16 := by
    rw [BitVec.toNat_and, show (65535 : BitVec 32).toNat = 2 ^ 16 - 1 by rfl,
      Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_mul, hx,
      Nat.mod_mod_of_dvd _ (by decide)]
  have qbound := Nat.mod_lt ((digit.toNat + acc.toNat) * inverse.toNat) (Nat.two_pow_pos 16)
  have prodBound : (digit.toNat + acc.toNat) * inverse.toNat % 2 ^ 16 * divisor.toNat <
      2 ^ 16 * 8162 := Nat.mul_lt_mul'' qbound hs.2
  unfold trialWord
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_add,
    BitVec.toNat_mul, hq, Nat.mod_eq_of_lt (by omega), hx,
    Nat.mod_eq_of_lt (by omega), Nat.add_comm]

theorem trial_word_reduces {digit acc inverse divisor : BitVec 32}
    (hd : digit.toNat < 2 ^ 16) (ha : acc.toNat < 2 * divisor.toNat)
    (hs : 3 ≤ divisor.toNat ∧ divisor.toNat < 8162)
    (hi : (divisor.toNat * inverse.toNat + 1) % 2 ^ 16 = 0) :
    (trialWord digit acc inverse divisor).toNat < 2 * divisor.toNat ∧
      (trialWord digit acc inverse divisor).toNat * 2 ^ 16 % divisor.toNat =
        (digit.toNat + acc.toNat) % divisor.toNat := by
  rw [trial_word_value hd ha hs]
  have hx : digit.toNat + acc.toNat < divisor.toNat * 2 ^ 16 := by
    have := Nat.mul_le_mul_right (2 ^ 16) hs.1
    omega
  exact (VG.Proof.RsaKeyGen.redc16_math hi hx).2

end VG.Proof.Dsa.X86.Generation
