module

public import VerifiedGarbage.Impl.Bignum.X86.CheckedPrimePower
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Proof.Bignum.X86.PreparePrime
public import VerifiedGarbage.Proof.Mont.X86.ExponentBody
import VerifiedGarbage.Proof.Bignum.X86.PrimeMask
import VerifiedGarbage.Proof.Bignum.X86.PrimePower
import VerifiedGarbage.Proof.Mont.X86.ContextLayout

/-! # A total factor exponentiation for arbitrary imported secret factors -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86.Dynamic VG.Proof.Mont.X86.Dynamic VG.Proof.Ecdsa.X86

def safePrime (m : Nat) : Nat := if 1 < m ∧ m % 2 = 1 then m else 3

theorem checkedPrimePower_ok {s : State} {base : Addr} {bytes n : Nat}
    (hs : Scr s base bytes) (hn : 0 < n) (hn32 : 128 * n < 2 ^ 32) (hz : contextBytes n ≤ bytes) :
    WP isa (checkedPrimePower n) s fun t =>
      Context n (safePrime (wordsVal s.mem base (slot n 0) n)) base bytes t ∧
      wordsVal t.mem base (slot n 6) n =
        wordsVal s.mem base (slot n 5) n ^ wordsVal s.mem base (slot n 8) n %
          safePrime (wordsVal s.mem base (slot n 0) n) ∧
      Outs base (primeSetupRanges n ++ exponentRanges n (2 * n)) s.mem t.mem ∧
      Keeps powerClob s t := by
  unfold checkedPrimePower
  refine WP.seq (WP.mono (primeMask_ok hs hn hz) fun u ⟨Mask, O, K⟩ => ?_)
  have preserve (i : Nat) (hi : i = 0 ∨ i = 5 ∨ i = 8) :
      wordsVal u.mem base (slot n i) n = wordsVal s.mem base (slot n i) n := by
    have sep := slot_sep (n := n) (i := i) (j := 7) (by omega)
    have bound := slot_bound (n := n) (i := i) (by omega)
    rw [wordsVal_eq_val32, wordsVal_eq_val32]
    exact O.val32 (by unfold stride at sep; omega) (by unfold stride at bound; have := hs.nowrap; omega)
  refine WP.mono (primePower_ok (hs.of_keeps K (by decide)) hn hn32 hz (preserve 0 (.inl rfl))
    (decide (1 < wordsVal s.mem base (slot n 0) n ∧ wordsVal s.mem base (slot n 0) n % 2 = 1))
    (by simpa only [mask32, decide_eq_true_eq] using Mask) (fun H => of_decide_eq_true H))
    fun t ⟨C, V, Ot, Kt⟩ => ?_
  refine ⟨?_, ?_, (Outs.of_outside O (by simp [primeSetupRanges])).trans Ot, (K.mono (by decide)).trans Kt⟩
  · simpa only [decide_eq_true_eq, safePrime] using C
  · rw [preserve 5 (.inr (.inl rfl)), preserve 8 (.inr (.inr rfl))] at V
    simpa only [decide_eq_true_eq, safePrime] using V

end VG.Proof.Bignum.X86
