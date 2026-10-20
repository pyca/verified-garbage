module
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Factor
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Spec.Rsa
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Dsa.X86.Generation.FactorMath
import VerifiedGarbage.Proof.Dsa.X86.Generation.FactorStep

/-! # Strip exactly the factors of two in a positive even exponent -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation
open VG.Spec.Rsa

structure FactorInv (s : State) (base : Addr) (n size original count left : Nat) (t : State) : Prop where
  scratch : Scr t base size
  positive : 0 < left
  even : left % 2 = 0
  value : val32 t.mem base (slot n 8) (2 * n) = left
  counter : ∃ i, t.gpr .ebx = BitVec.ofNat 32 (count + i) ∧
    i + (splitTwos left).1 = (splitTwos original).1
  oddPart : (splitTwos left).2 = (splitTwos original).2
  mem : Outside base (slot n 8) (8 * n) s.mem t.mem
  keeps : Keeps [.eax, .ebx, .edx] s t

theorem factorLoop_ok {s : State} {base : Addr} {size n count original : Nat}
    (S : Scr s base size) (hn : 0 < n) (room : slot n 8 + 8 * n ≤ size)
    (pos : 0 < original) (even : original % 2 = 0)
    (value : val32 s.mem base (slot n 8) (2 * n) = original)
    (bx : s.gpr .ebx = BitVec.ofNat 32 count) :
    WP isa (.loop (factorStep n) .e) s fun t =>
      t.gpr .ebx = BitVec.ofNat 32 (count + (splitTwos original).1) ∧
      val32 t.mem base (slot n 8) (2 * n) = (splitTwos original).2 ∧
      Outside base (slot n 8) (8 * n) s.mem t.mem ∧ Keeps [.eax, .ebx, .edx] s t := by
  refine WP.loop (M := isa) (FactorInv s base n size original count) ?_ original s
    ⟨S, pos, even, value, ⟨0, by simpa only [Nat.add_zero] using bx, by omega⟩,
      rfl, Outside.refl _ _ _ _, Keeps.refl _ _⟩
  intro left t I
  obtain ⟨i, counter, total⟩ := I.counter
  obtain ⟨pos', twos, odd⟩ := factor_step I.positive I.even
  refine WP.mono (factorStep_ok I.scratch hn room counter) fun u ⟨bu, vu, zu, Ou, Ku⟩ => ?_
  rw [I.value] at vu
  by_cases more : (left / 2) % 2 = 0
  · refine .inr ⟨by simp only [eval, zu, vu, more, decide_true], left / 2, by have := I.positive; omega, ?_⟩
    exact ⟨I.scratch.of_keeps Ku (by decide), pos', more, vu,
      ⟨i + 1, by simpa only [Nat.add_assoc] using bu, by omega⟩,
      odd.symm.trans I.oddPart, I.mem.trans Ou, I.keeps.trans Ku⟩
  · have terminal : (left / 2) % 2 = 1 := by omega
    obtain ⟨ct, cv⟩ := factor_terminal terminal
    have resultCount : i + 1 = (splitTwos original).1 := by omega
    refine .inl ⟨by simp only [eval, zu, vu, more, decide_false], ?_⟩
    exact ⟨by rw [bu, Nat.add_assoc, resultCount], vu.trans (cv.symm.trans (odd.symm.trans I.oddPart)),
      I.mem.trans Ou, I.keeps.trans Ku⟩
end VG.Proof.Dsa.X86.Generation
