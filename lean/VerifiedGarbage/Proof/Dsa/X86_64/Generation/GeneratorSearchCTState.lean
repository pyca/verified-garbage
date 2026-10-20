module
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.TapeLoop
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorSearchMemory

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorInvariant
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ChunkTake
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ChunkCheck

/-! # Public cursor and exact chunk state of the generator search -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.Generation VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64

structure GeneratorSearchPublic where
  plan : GeneratorSearchPlan
  used : Nat
  bound : used ≤ plan.tape.length

def GeneratorSearchBefore (len : Nat) (p : GeneratorSearchPublic) (s : State) : Prop :=
  (∃ W, GeneratorSearchMemory p.plan W s ∧ W 20 = BitVec.ofNat 64 p.used) ∧ p.plan.core.len = len

def GeneratorSearchPublic.exhausted (p : GeneratorSearchPublic) : Bool :=
  decide (p.plan.tape.length - p.used < p.plan.core.len)

def GeneratorSearchChecked (len : Nat) (p : GeneratorSearchPublic) (s : State) : Prop :=
  GeneratorSearchBefore len p s ∧ isa.eval .b s = some p.exhausted

def GeneratorSearchAvailable (len : Nat) (p : GeneratorSearchPublic) (s : State) : Prop :=
  GeneratorSearchBefore len p s ∧ p.used + p.plan.core.len ≤ p.plan.tape.length

def GeneratorSearchTaken (len : Nat) (p : GeneratorSearchPublic) (s : State) : Prop :=
  (∃ W, GeneratorSearchMemory p.plan W s ∧
    W 20 = BitVec.ofNat 64 (p.used + p.plan.core.len) ∧ W 21 = off p.plan.tapePtr p.used) ∧
    p.plan.core.len = len ∧ p.used + p.plan.core.len ≤ p.plan.tape.length

theorem generatorSearch_check {len : Nat} {p : GeneratorSearchPublic} {s : State}
    (h : GeneratorSearchBefore len p s) :
    WP isa (.block (chunkCheck generatorTape len)) s (GeneratorSearchChecked len p) := by
  obtain ⟨⟨W, hm, hu⟩, he⟩ := h
  obtain ⟨V, R⟩ := hm.rep
  have hl : len < 2 ^ 31 := by rcases p.plan.core.width with hh | hh | hh <;> omega
  refine WP.mono (chunkCheck_ok hm.layout R generatorTape (by decide) (by decide)
    hl hu hm.tapeLength p.bound p.plan.tapeFits) fun t ⟨hc, hmem, hk⟩ => ?_
  exact ⟨⟨⟨W, generatorMemory_congr hm hmem hk, hu⟩, he⟩,
    by simp only [eval, hc, GeneratorSearchPublic.exhausted, he]⟩

theorem generatorSearch_available {len : Nat} {p : GeneratorSearchPublic} {s : State}
    (h : GeneratorSearchChecked len p s) (hb : isa.eval .b s = some false) :
    GeneratorSearchAvailable len p s := by
  have he : p.exhausted = false := Option.some.inj (h.2.symm.trans hb)
  have hn := of_decide_eq_false he
  exact ⟨h.1, by have hb := p.bound; omega⟩

theorem generatorSearch_take {len : Nat} {p : GeneratorSearchPublic} {s : State}
    (h : GeneratorSearchAvailable len p s) :
    WP isa (.block (tapeTake generatorTape len)) s (GeneratorSearchTaken len p) := by
  obtain ⟨⟨⟨W, hm, hu⟩, he⟩, room⟩ := h
  obtain ⟨V, R⟩ := hm.rep
  have hl : len < 2 ^ 31 := by rcases p.plan.core.width with hh | hh | hh <;> omega
  refine WP.mono (chunkTake_ok hm.layout R generatorTape (by decide) (by decide)
    (by decide) (by decide) (by decide) hl hu) fun t ⟨Lt, Rt, ft, kt⟩ => ?_
  have ff : Frame p.plan.core.changed s.mem t.mem := ft.mono (by
    intro r hr; rcases List.mem_singleton.mp hr with rfl; simp [GeneratorPlan.changed])
  have ht := hm.frame Lt ⟨V, Rt⟩ (by
    intro k hk
    simp only [generatorSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
    ff kt.2.1 kt.2.2
  refine ⟨⟨_, ht, ?_, ?_⟩, he, room⟩
  · simp only [generatorTape, upd, ↓reduceIte, he]
  · simp [generatorTape, upd, hm.tapeBase]

end VG.Proof.Dsa.X86_64.Generation
