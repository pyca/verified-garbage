module

public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.Proof.RsaKeyGen.X86.LowPairScan
public import VerifiedGarbage.Impl.RsaKeyGen.X86.LowPair
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words

import VerifiedGarbage.Proof.RsaKeyGen.X86.LowPairFirst
import VerifiedGarbage.Proof.RsaKeyGen.MrWindow
import VerifiedGarbage.Proof.Rsa.RecoverMath
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.RsaKeyGen.X86.LowPairStep
import VerifiedGarbage.Proof.Bignum.Words
/-! # The native pair scan finds the word containing the exponent's lowest set bit -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/LowPairWord.lean`, which only this module imported.
section

/-! # Native halves read by the masked scan form the original 64-bit word -/

section
namespace VG.Proof.RsaKeyGen.X86.LowPair
open VG VG.Proof.Mont

theorem pairAt_word (m : Mem) (base : Addr) (src : Nat) :
    (pairAt m base src).2 ++ (pairAt m base src).1 = word m base src := by
  rw [word, VG.Proof.Rc2.Word32.read64_pair, VG.Offset.add_add]
  rfl

theorem pairAt_zero_iff (m : Mem) (base : Addr) (src : Nat) :
    pairAt m base src = (0#32, 0#32) ↔ word m base src = 0#64 := by
  constructor
  · intro h
    rw [← pairAt_word, h]
    rfl
  · intro h
    have value := congrArg BitVec.toNat h
    rw [word_eq_w32] at value
    change w32 m base src + 2 ^ 32 * w32 m base (src + 4) = 0 at value
    have low : w32 m base src = 0 := by omega
    have high : w32 m base (src + 4) = 0 := by omega
    exact Prod.ext (BitVec.eq_of_toNat_eq low) (BitVec.eq_of_toNat_eq high)

end VG.Proof.RsaKeyGen.X86.LowPair
end

end

-- Formerly `VerifiedGarbage/Proof/Mont/Digits64.lean`, which only this module imported.
section

/-! # A native paired word is a base-2⁶⁴ digit of its integer -/

section
namespace VG.Proof.Mont
open VG

theorem word_digit64 (m : Mem) (base : Addr) (src n index : Nat) (bound : index < n) :
    (word m base (src + 8 * index)).toNat = wordsVal m base src n / 2 ^ (64 * index) % 2 ^ 64 := by
  have bridge : ∀ k, wordsVal m base src k = VG.Proof.Bignum.wv m base src k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [wordsVal_succ_top, VG.Proof.Bignum.wv, ih]
  rw [bridge]
  exact VG.Proof.Bignum.word_of_wv m base src n bound

end VG.Proof.Mont
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.LowPair
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.LowPair

/-- The first nonzero pair of `count` pairs whose value is `N > 0` is the
64-bit word holding `N`'s lowest set bit. -/
theorem first_twos {m : Mem} {base : Addr} {src count N : Nat}
    (value : val32 m base src (2 * count) = N) (positive : 0 < N) :
    ((first m base src (0#32, 0#32) 0 count).2 ++ (first m base src (0#32, 0#32) 0 count).1).toNat =
      N / 2 ^ (64 * ((Spec.Rsa.splitTwos N).1 / 64)) % 2 ^ 64 := by
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
      (word m base (src + 8 * j)).toNat = N / 2 ^ (64 * j) % 2 ^ 64 := by
    rw [word_digit64 _ _ _ _ _ index, wordsVal_eq_val32, value]
  have below (j : Nat) (_ : 0 ≤ j) (hj : j < a / 64) :
      pairAt m base (src + 8 * j) = (0#32, 0#32) := by
    apply (pairAt_zero_iff _ _ _).mpr
    apply BitVec.eq_of_toNat_eq
    rw [digit (by omega), zero j hj]
    rfl
  have hit : pairAt m base (src + 8 * (a / 64)) ≠ (0#32, 0#32) := by
    intro h
    have empty := congrArg BitVec.toNat ((pairAt_zero_iff _ _ _).mp h)
    rw [digit (by omega)] at empty
    have notZero : N / 2 ^ (64 * (a / 64)) % 2 ^ 64 ≠ 0 := by
      intro h
      rw [h, Nat.zero_testBit] at bit
      contradiction
    exact notZero empty
  rw [first_hit m base src 0 count (a / 64) (by omega) (by omega) below hit, pairAt_word, digit (by omega)]

theorem scan_twos {s : State} {base : Addr} {size src count N : Nat} (scratch : Scr s base size)
    (fit : src + 8 * count ≤ size) (value : val32 s.mem base src (2 * count) = N) (positive : 0 < N) :
    WP isa (scan src count) s fun t =>
      (t.gpr .esi ++ t.gpr .ebx).toNat = N / 2 ^ (64 * ((Spec.Rsa.splitTwos N).1 / 64)) % 2 ^ 64 ∧
      t.mem = s.mem ∧ Keeps [.eax, .ecx, .edx, .ebx, .esi] s t := by
  refine WP.mono (scan_ok scratch fit) fun t ⟨V, M, K⟩ => ?_
  have pair := congrArg (fun p : BitVec 32 × BitVec 32 => p.2 ++ p.1) V
  dsimp only at pair
  exact ⟨by rw [pair]; exact first_twos value positive, M, K⟩

end VG.Proof.RsaKeyGen.X86.LowPair
