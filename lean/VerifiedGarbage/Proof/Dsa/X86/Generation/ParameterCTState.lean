module
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass.Point
public import Aesop.BuiltinRules
public import Mathlib.Tactic.Attr.Core
public import VerifiedGarbage.Impl.Dsa.X86.Generation.TapeLoop
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchContext
import VerifiedGarbage.Proof.Dsa.X86.Generation.ParameterStable
import VerifiedGarbage.Proof.Dsa.X86.Generation.TapeControl
import VerifiedGarbage.Proof.Dsa.X86.Generation.TapeTake

/-! # The public outer-search state records independent seed and witness positions -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

structure ParameterPublic where
  plan : SearchContextPlan
  seedUsed : Nat
  used : Nat
  seedBound : seedUsed ≤ plan.seeds.bytes.length
  bound : used ≤ plan.witnesses.bytes.length

def ParameterBefore (plen qlen : Nat) (p : ParameterPublic) (s : State) : Prop :=
  (∃ W, SearchContext p.plan W s ∧ W 10 = BitVec.ofNat 32 p.seedUsed ∧ W 16 = BitVec.ofNat 32 p.used) ∧
    p.plan.geometry.pLen = plen ∧ p.plan.geometry.qLen = qlen

def ParameterPublic.exhausted (p : ParameterPublic) : Bool :=
  decide (p.plan.seeds.bytes.length - p.seedUsed < p.plan.geometry.qLen)

def ParameterChecked (plen qlen : Nat) (p : ParameterPublic) (s : State) : Prop :=
  ParameterBefore plen qlen p s ∧ s.cf = some p.exhausted

def ParameterAvailable (plen qlen : Nat) (p : ParameterPublic) (s : State) : Prop :=
  ParameterBefore plen qlen p s ∧ p.seedUsed + p.plan.geometry.qLen ≤ p.plan.seeds.bytes.length

def ParameterTaken (plen qlen : Nat) (p : ParameterPublic) (s : State) : Prop :=
  (∃ W, SearchContext p.plan W s ∧ W 10 = BitVec.ofNat 32 (p.seedUsed + p.plan.geometry.qLen) ∧
    W 16 = BitVec.ofNat 32 p.used ∧ W 1 = p.plan.seeds.pointer + BitVec.ofNat 32 p.seedUsed) ∧
    p.plan.geometry.pLen = plen ∧ p.plan.geometry.qLen = qlen ∧
    p.seedUsed + p.plan.geometry.qLen ≤ p.plan.seeds.bytes.length

theorem parameter_check {plen qlen : Nat} {p : ParameterPublic} {s : State}
    (H : ParameterBefore plen qlen p s) :
    WP isa (.block (chunkCheck seedTape qlen)) s (ParameterChecked plen qlen p) := by
  obtain ⟨⟨W, R, seedUsed, used⟩, pl, ql⟩ := H
  refine WP.mono (chunkCheck_ok R.arena.frame R.representation seedTape (by decide) (by decide)
    p.seedBound p.plan.seeds.size (by have := p.plan.geometry.qWidth; omega) seedUsed
    ((R.fixed 9 (by decide) (by decide)).trans p.plan.seedLength)) fun t ⟨cf, mem, K⟩ => ?_
  exact ⟨⟨⟨W, R.congr mem K (by decide), seedUsed, used⟩, pl, ql⟩,
    by simpa only [ParameterPublic.exhausted, ql] using cf⟩

theorem parameter_available {plen qlen : Nat} {p : ParameterPublic} {s : State}
    (H : ParameterChecked plen qlen p s) (cf : eval .b s = some false) : ParameterAvailable plen qlen p s := by
  have h : p.exhausted = false := Option.some.inj (H.2.symm.trans cf)
  have := of_decide_eq_false h
  exact ⟨H.1, by have := p.seedBound; omega⟩

theorem parameter_take {plen qlen : Nat} {p : ParameterPublic} {s : State}
    (H : ParameterAvailable plen qlen p s) :
    WP isa (.block (tapeTake seedTape qlen)) s (ParameterTaken plen qlen p) := by
  obtain ⟨⟨⟨W, R, seedUsed, used⟩, pl, ql⟩, room⟩ := H
  refine WP.mono (tapeTake_ok R.arena.frame R.representation seedTape qlen (by decide) (by decide) (by decide) seedUsed)
    fun t ⟨_, Wt, O, K⟩ => ?_
  have Rt := R.frame Wt (by
    intro i _ hx
    have n10 : i ≠ 10 := by intro eq; subst i; exact hx (by decide)
    have n1 : i ≠ 1 := by intro eq; subst i; exact hx (by decide)
    change frameUpdate (frameUpdate W 1 (W 8 + BitVec.ofNat 32 p.seedUsed)) 10 (BitVec.ofNat 32 (p.seedUsed + qlen)) i = W i
    simp only [frameUpdate, ite_eq_right n10, ite_eq_right n1]) (parameter_frame O (Nat.le_refl _)) K (by decide)
  refine ⟨⟨_, Rt, ?_, used, ?_⟩, pl, ql, room⟩
  · simp only [seedTape, frameUpdate, ite_true, ql]
  · change W 8 + BitVec.ofNat 32 p.seedUsed = _
    rw [R.fixed 8 (by decide) (by decide), p.plan.seedPointer]
end VG.Proof.Dsa.X86.Generation
