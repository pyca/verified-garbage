module
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorSearchMemory
public import VerifiedGarbage.Impl.Dsa.X86.Generation.TapeLoop
import VerifiedGarbage.Proof.Dsa.X86.Generation.TapeControl
import VerifiedGarbage.Proof.Dsa.X86.Generation.TapeTake

/-! # Public generator tape position and complete-chunk availability -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

structure GeneratorSearchPublic where
  plan : GeneratorSearchPlan
  used : Nat
  bound : used ≤ plan.tape.length

def GeneratorSearchBefore (len : Nat) (p : GeneratorSearchPublic) (s : State) : Prop :=
  (∃ W, GeneratorSearchMemory p.plan W s ∧ W 20 = BitVec.ofNat 32 p.used) ∧ p.plan.core.len = len

def GeneratorSearchPublic.exhausted (p : GeneratorSearchPublic) : Bool :=
  decide (p.plan.tape.length - p.used < p.plan.core.len)

def GeneratorSearchChecked (len : Nat) (p : GeneratorSearchPublic) (s : State) : Prop :=
  GeneratorSearchBefore len p s ∧ s.cf = some p.exhausted

def GeneratorSearchAvailable (len : Nat) (p : GeneratorSearchPublic) (s : State) : Prop :=
  GeneratorSearchBefore len p s ∧ p.used + p.plan.core.len ≤ p.plan.tape.length

def GeneratorSearchTaken (len : Nat) (p : GeneratorSearchPublic) (s : State) : Prop :=
  (∃ W, GeneratorSearchMemory p.plan W s ∧ W 20 = BitVec.ofNat 32 (p.used + p.plan.core.len) ∧
    W 21 = p.plan.tapePtr + BitVec.ofNat 32 p.used) ∧
    p.plan.core.len = len ∧ p.used + p.plan.core.len ≤ p.plan.tape.length

theorem generatorSearch_check {len : Nat} {p : GeneratorSearchPublic} {s : State}
    (H : GeneratorSearchBefore len p s) :
    WP isa (.block (chunkCheck generatorTape len)) s (GeneratorSearchChecked len p) := by
  obtain ⟨⟨W, R, used⟩, width⟩ := H
  refine WP.mono (chunkCheck_ok R.layout R.representation generatorTape (by decide) (by decide)
    p.bound p.plan.tapeFits (by have := p.plan.core.lenMax; omega) used
    ((R.fixed 12 (by decide) (by decide)).trans p.plan.savedTotal)) fun t ⟨cf, mem, K⟩ => ?_
  exact ⟨⟨⟨W, R.congr mem K (by decide), used⟩, width⟩, by simpa only [GeneratorSearchPublic.exhausted, width] using cf⟩

theorem generatorSearch_available {len : Nat} {p : GeneratorSearchPublic} {s : State}
    (H : GeneratorSearchChecked len p s) (cf : eval .b s = some false) : GeneratorSearchAvailable len p s := by
  have h : p.exhausted = false := Option.some.inj (H.2.symm.trans cf)
  have := of_decide_eq_false h
  exact ⟨H.1, by have := p.bound; omega⟩

theorem generatorSearch_take {len : Nat} {p : GeneratorSearchPublic} {s : State}
    (H : GeneratorSearchAvailable len p s) :
    WP isa (.block (tapeTake generatorTape len)) s (GeneratorSearchTaken len p) := by
  obtain ⟨⟨⟨W, R, used⟩, width⟩, room⟩ := H
  refine WP.mono (tapeTake_ok R.layout R.representation generatorTape len (by decide) (by decide) (by decide) used)
    fun t ⟨_, Wt, O, K⟩ => ?_
  have Rt := R.control Wt (by
    intro i _ hx
    have n20 : i ≠ 20 := by intro eq; subst i; simp at hx
    have n21 : i ≠ 21 := by intro eq; subst i; simp at hx
    change frameUpdate (frameUpdate W 21 (W 11 + BitVec.ofNat 32 p.used)) 20 (BitVec.ofNat 32 (p.used + len)) i = W i
    simp only [frameUpdate, ite_eq_right n20, ite_eq_right n21]) O (Nat.le_refl _) K (by decide)
  refine ⟨⟨_, Rt, ?_, ?_⟩, width, room⟩
  · simp only [generatorTape, frameUpdate, ite_true, width]
  · change W 11 + BitVec.ofNat 32 p.used = _
    rw [R.fixed 11 (by decide) (by decide), p.plan.savedTape]
end VG.Proof.Dsa.X86.Generation
