module

public import VerifiedGarbage.Impl.Bignum.X86.InputCompare
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Bignum.X86.PublicLayout
import VerifiedGarbage.Proof.Mont.X86.WordOps

/-! # The representative comparison returns a mask without secret branches -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.Impl.Bignum.X86.PublicContext VG.Proof.Mont VG.Proof.Mont.X86

theorem inputCompare_ok {s : State} {base : Addr} {bytes n : Nat}
    (hs : Scr s base bytes) (hn : 0 < n) (hz : size n ≤ bytes) :
    WP isa (inputCompare n) s fun t =>
      t.gpr .ecx = (if wordsVal s.mem base (slot n 6) n < wordsVal s.mem base (slot n 0) n
        then BitVec.allOnes 32 else 0) ∧
      Outside base (slot n 1) (8 * n) s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have b0 := slot_bound (n := n) (i := 0) (by decide)
  have b1 := slot_bound (n := n) (i := 1) (by decide)
  have b6 := slot_bound (n := n) (i := 6) (by decide)
  have s01 := slot_le (n := n) (i := 0) (j := 1) (by decide)
  have s16 := slot_le (n := n) (i := 1) (j := 6) (by decide)
  simp only [stride] at b0 b1 b6 s01 s16
  unfold inputCompare
  refine WP.mono (chainSubW_ok hs (k := 2 * n) (by omega) (by omega) (by omega)
    (by omega) (.inl (by omega)) (.inr (by omega))) fun t ⟨O, ⟨c, M, V⟩, K⟩ => ?_
  refine ⟨?_, by simpa only [show 4 * (2 * n) = 8 * n by omega] using O, K⟩
  rw [wordsVal_eq_val32, wordsVal_eq_val32, M]
  have ht := val32_lt t.mem base (slot n 1) (2 * n)
  have hb := val32_lt s.mem base (slot n 0) (2 * n)
  cases c <;> simp only [cmask, Bool.false_eq_true, ite_false, ite_true,
    Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at *
  · rw [ite_eq_right (by omega)]
  · rw [ite_eq_left (by omega)]

end VG.Proof.Bignum.X86.PublicContext
