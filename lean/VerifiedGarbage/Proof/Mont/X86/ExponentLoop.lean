module
public import VerifiedGarbage.Proof.Mont.X86.ExponentBody
public import VerifiedGarbage.Proof.Mont.X86.PowerStep

import VerifiedGarbage.Proof.Mont.X86.ExponentStep
import VerifiedGarbage.Proof.Mont.X86.ContextMath
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Mont.X86.Row

/-! # Terminating secret-exponent loop -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont
open VG.Proof.Mont.X86

structure ExponentInv (n size m expWords target steps i : Nat) (base : Addr) (s t : State) : Prop where
  context : Context n m base size t
  counter : t.gpr .esi = BitVec.ofNat 32 (steps - i)
  bound : val32 t.mem base (slot n 8) expWords < 2 ^ (steps - i)
  value : ∃ y b,
    wordsVal t.mem base (slot n 6) n = y * 2 ^ (64 * n) % m ∧
    wordsVal t.mem base (slot n 5) n = b * 2 ^ (64 * n) % m ∧
    (y * b ^ val32 t.mem base (slot n 8) expWords) % m = target
  mem : Outs base (exponentRanges n expWords) s.mem t.mem
  keeps : Keeps powerClob s t

theorem exponentLoop_ok {n size m expWords a : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) (he : 1 < expWords) (hen : expWords ≤ 2 * n)
    (hy : wordsVal s.mem base (slot n 6) n = 2 ^ (64 * n) % m)
    (hb : wordsVal s.mem base (slot n 5) n = a * 2 ^ (64 * n) % m)
    (hk32 : 32 * expWords < 2 ^ 32) (hc : s.gpr .esi = BitVec.ofNat 32 (32 * expWords)) :
    WP isa (.loop (exponentStep n expWords) .ne) s
      (ExponentInv n size m expWords (a ^ val32 s.mem base (slot n 8) expWords % m)
        (32 * expWords) (32 * expWords) base s) := by
  let steps := 32 * expWords
  let target := a ^ val32 s.mem base (slot n 8) expWords % m
  have hspos : 0 < steps := by dsimp [steps]; omega
  have init : ExponentInv n size m expWords target steps 0 base s s := by
    refine ⟨h, ?_, ?_, ⟨1, a, ?_, hb, ?_⟩, Outs.refl _ _ _, Keeps.refl _ _⟩
    · simpa only [Nat.sub_zero] using hc
    · simpa only [Nat.sub_zero] using val32_lt s.mem base (slot n 8) expWords
    · simpa only [Nat.one_mul] using hy
    · simp only [Nat.one_mul]; rfl
  refine WP.loop (M := isa)
    (fun k t => ∃ i, k = steps - i ∧ i < steps ∧ ExponentInv n size m expWords target steps i base s t)
    ?_ steps s ⟨0, rfl, hspos, init⟩
  rintro k t ⟨i, rfl, hi, I⟩
  obtain ⟨y, b, Y, B, V⟩ := I.value
  refine WP.mono (exponentStep_ok I.context he hen Y B (by omega) (by dsimp [steps] at *; omega) I.counter)
    fun u ⟨count, zf, C, Y', B', E', O, K⟩ => ?_
  have next : ExponentInv n size m expWords target steps (i + 1) base s u := by
    refine ⟨C, ?_, ?_, ⟨_, _, Y', B', ?_⟩, I.mem.trans O, I.keeps.trans K⟩
    · rw [count, show steps - i - 1 = steps - (i + 1) by omega]
    · rw [E']
      have hp : 2 ^ (steps - i) = 2 ^ (steps - (i + 1)) * 2 := by
        rw [show steps - i = steps - (i + 1) + 1 by omega, Nat.pow_succ]
      have bound := I.bound
      rw [hp] at bound
      omega
    · rw [E', exponent_step_value]
      exact V
  by_cases hdone : i + 1 = steps
  · refine .inl ⟨?_, ?_⟩
    · have eq : steps - i = 1 := by omega
      simp only [eval, zf, eq, decide_true, Option.map_some, Bool.not_true]
    · change ExponentInv n size m expWords target steps steps base s u
      rw [hdone] at next
      exact next
  · refine .inr ⟨?_, steps - (i + 1), by omega, i + 1, rfl, by omega, next⟩
    have ne : steps - i ≠ 1 := by omega
    simp only [eval, zf, decide_eq_false ne, Option.map_some, Bool.not_false]

theorem ExponentInv.finished {n size m expWords target steps : Nat} {base : Addr} {s t : State}
    (I : ExponentInv n size m expWords target steps steps base s t) :
    wordsVal t.mem base (slot n 6) n = target * 2 ^ (64 * n) % m := by
  have bound := I.bound
  simp only [Nat.sub_self, Nat.pow_zero] at bound
  have ez : val32 t.mem base (slot n 8) expWords = 0 := by omega
  obtain ⟨y, b, Y, _, V⟩ := I.value
  rw [ez, Nat.pow_zero, Nat.mul_one] at V
  rw [Y, Nat.mul_mod y, V, Nat.mul_mod_mod]

end VG.Proof.Mont.X86.Dynamic
