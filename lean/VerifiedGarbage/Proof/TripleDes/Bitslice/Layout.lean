module

public import VerifiedGarbage.Proof.TripleDes.Bitslice.LayoutLit
public import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Facts about where bitsliced DES keeps each bit

Each fact is about a few small numbers, proved by evaluation.
-/

@[expose] public section

namespace VG.Proof.TripleDes.Bitslice

open VG.Spec.TripleDes VG.Impl.TripleDes.Bitslice

theorem ipWord_lt : ∀ t < 64, ipWord t < 64 := by lit_decide

theorem lWord_lt : ∀ q < 32, lWord q < 64 := by lit_decide
theorem rWord_lt : ∀ q < 32, rWord q < 64 := by lit_decide

theorem inBit_lt : ∀ j < 8, ∀ i < 6, inBit j i < 48 := by decide

theorem eBit_lt : ∀ j < 8, ∀ i < 6, eBit (inBit j i) < 32 := by lit_decide

theorem outBit_lt : ∀ j < 8, ∀ i < 4, outBit j i < 32 := by lit_decide

/-- P sends S-box `j`'s output bit `i` to bit `outBit j i` of `f`. -/
theorem outBit_spec : ∀ j < 8, ∀ i < 4, 32 - p.getD (31 - outBit j i) 1 = 4 * (7 - j) + i := by
  lit_decide

/-- FP undoes IP: bit `i` of a block, after FP, is in the word of its IP position. -/
theorem fp_ipWord : ∀ i < 64, ipWord (64 - fp.getD (63 - i) 1) = i ^^^ 56 := by lit_decide

theorem fp_bounds : ∀ i < 64, 1 ≤ fp.getD (63 - i) 1 ∧ fp.getD (63 - i) 1 ≤ 64 := by decide +kernel
end VG.Proof.TripleDes.Bitslice
