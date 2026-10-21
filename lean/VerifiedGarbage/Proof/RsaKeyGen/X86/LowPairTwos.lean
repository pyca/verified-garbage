module

public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.RsaKeyGen.X86.LowPairWord
import VerifiedGarbage.Proof.RsaKeyGen.X86.LowPairFirst
import VerifiedGarbage.Proof.Mont.Digits64
import VerifiedGarbage.Proof.RsaKeyGen.MrWindow
import VerifiedGarbage.Proof.Rsa.RecoverMath
public import VerifiedGarbage.Impl.RsaKeyGen.X86.LowPair
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # The native pair scan finds the word containing the exponent's lowest set bit -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.LowPair
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.LowPair

theorem scan_twos {s : State} {base : Addr} {size src count N : Nat} (scratch : Scr s base size)
    (fit : src + 8 * count ≤ size) (value : val32 s.mem base src (2 * count) = N) (positive : 0 < N) :
    WP isa (scan src count) s fun t =>
      (t.gpr .esi ++ t.gpr .ebx).toNat = N / 2 ^ (64 * ((Spec.Rsa.splitTwos N).1 / 64)) % 2 ^ 64 ∧
      t.mem = s.mem ∧ Keeps [.eax, .ecx, .edx, .ebx, .esi] s t := by
  obtain ⟨factor, odd⟩ := VG.Proof.Rsa.splitTwos_spec positive
  rw [Nat.mul_comm] at factor
  let a := (Spec.Rsa.splitTwos N).1
  obtain ⟨zero, bit, lower⟩ := VG.Proof.RsaKeyGen.lowWord_bits factor odd
  have bound : a < 64 * count := by
    have small : N < 2 ^ (64 * count) := by
      rw [← value, ← wordsVal_eq_val32]
      exact wordsVal_lt _ _ _ _
    by_cases h : a < 64 * count
    · exact h
    · have pow := Nat.pow_le_pow_right (n := 2) (by decide) (show 64 * count ≤ a by omega)
      have mul := Nat.le_mul_of_pos_left (2 ^ a) (show 0 < (Spec.Rsa.splitTwos N).2 by omega)
      rw [← factor] at mul
      omega
  have digit {j : Nat} (index : j < count) :
      (word s.mem base (src + 8 * j)).toNat = N / 2 ^ (64 * j) % 2 ^ 64 := by
    rw [word_digit64 _ _ _ _ _ index, wordsVal_eq_val32, value]
  have below (j : Nat) (_ : 0 ≤ j) (hj : j < a / 64) :
      pairAt s.mem base (src + 8 * j) = (0#32, 0#32) := by
    apply (pairAt_zero_iff _ _ _).mpr
    apply BitVec.eq_of_toNat_eq
    rw [digit (by omega), zero j hj]
    rfl
  have hit : pairAt s.mem base (src + 8 * (a / 64)) ≠ (0#32, 0#32) := by
    intro h
    have empty := congrArg BitVec.toNat ((pairAt_zero_iff _ _ _).mp h)
    rw [digit (by omega)] at empty
    have notZero : N / 2 ^ (64 * (a / 64)) % 2 ^ 64 ≠ 0 := by
      intro h
      rw [h, Nat.zero_testBit] at bit
      contradiction
    exact notZero empty
  refine WP.mono (scan_ok scratch fit) fun t ⟨V, M, K⟩ => ?_
  rw [first_hit s.mem base src 0 count (a / 64) (by omega) (by omega) below hit] at V
  have pair := congrArg (fun p : BitVec 32 × BitVec 32 => p.2 ++ p.1) V
  dsimp only [Prod.fst, Prod.snd] at pair
  rw [pairAt_word] at pair
  exact ⟨by rw [pair, digit (by omega)], M, K⟩

end VG.Proof.RsaKeyGen.X86.LowPair
