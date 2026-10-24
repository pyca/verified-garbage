module

public import VerifiedGarbage.Impl.Dsa.X86.Minus
public import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Mont.X86.ContextFrame
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Dsa.X86.CoreFrame
import VerifiedGarbage.Proof.Mont.X86.WordConst
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Impl.Mont.X86.Context
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # Exact non-underflowing subtraction from the loaded modulus -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86

theorem modulusMinus_ok {s : State} {base : Addr} {size n m amount : Nat}
    (hs : Scr s base size) (hn0 : 0 < n) (hz : contextBytes n ≤ size)
    (hv : wordsVal s.mem base (slot n 0) n = m) (ha : amount ≤ m) :
    WP isa (modulusMinus n amount) s fun t =>
      wordsVal t.mem base (slot n 6) n = m - amount ∧
      Outside base 0 (contextBytes n) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have hm : m < 2 ^ (64 * n) := by rw [← hv]; exact wordsVal_lt _ _ _ _
  have bounds (j : Nat) (hj : j < 9) : slot n j + 8 * n ≤ size := by
    have := slot_bound (n := n) hj
    have := hz
    simp only [stride] at *
    omega_arith
  have sep60 := slot_sep (n := n) (i := 6) (j := 0) (by decide)
  have sep67 := slot_sep (n := n) (i := 6) (j := 7) (by decide)
  have sep70 := slot_sep (n := n) (i := 7) (j := 0) (by decide)
  simp only [stride] at sep60 sep67 sep70
  unfold modulusMinus
  refine WP.seq (WP.mono (setConstW_ok hs (k := 2 * n) (o := slot n 7) (x := amount) (by omega_arith)
    (by have := bounds 7 (by decide); omega_arith)
    (by rw [show 32 * (2 * n) = 64 * n by omega_arith]; exact Nat.lt_of_le_of_lt ha hm)) fun u ⟨Vu, Ku, Ou⟩ => ?_)
  rw [show 4 * (2 * n) = 8 * n by omega_arith] at Ou
  rw [← wordsVal_eq_val32] at Vu
  have Hu := hs.of_keeps Ku (by decide)
  have Mu : wordsVal u.mem base (slot n 0) n = m :=
    (Ou.wordsVal (by omega_arith) (by have := hs.nowrap; have := bounds 0 (by decide); omega_arith)).trans hv
  obtain ⟨k, hk⟩ : ∃ k, 2 * n = k + 1 := ⟨2 * n - 1, by omega_arith⟩
  rw [hk]
  refine WP.mono (chainSubW_ok Hu (k := k + 1) (by omega_arith) (by have := bounds 6 (by decide); omega_arith)
    (by have := bounds 0 (by decide); omega_arith) (by have := bounds 7 (by decide); omega_arith)
    (by omega_arith) (by omega_arith)) fun t ⟨Ot, ⟨c, _, Vt⟩, Kt⟩ => ?_
  have Ol : Outside base (slot n 6) (8 * n) u.mem t.mem := by
    simpa only [show 4 * (k + 1) = 8 * n by omega_arith] using Ot
  refine ⟨?_, (slotOutside_whole Ou (by decide)).trans (slotOutside_whole Ol (by decide)),
    (Ku.mono (by decide)).trans (Kt.mono (by decide))⟩
  rw [wordsVal_eq_val32, hk] at Mu Vu ⊢
  rw [Mu, Vu] at Vt
  have lt := val32_lt t.mem base (slot n 6) (k + 1)
  cases c <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at Vt <;> omega_arith

end VG.Proof.Dsa.X86
