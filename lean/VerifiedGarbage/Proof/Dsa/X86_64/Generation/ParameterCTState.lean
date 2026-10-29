module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedAttemptCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ParameterInvariant
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ChunkTake
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ChunkCheck
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSlice
import Mathlib.Algebra.Group.Nat.Defs

/-! # Public seed and witness cursors for the complete parameter search -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.Generation VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64

structure ParameterPublic where
  context : GenerationContext
  seedUsed : Nat
  seedBound : seedUsed ≤ context.seeds.bytes.length
  randUsed : Nat
  randBound : randUsed ≤ context.rand.bytes.length
  ws : List Region
  wr : List Region
  header : PrimeHeaderLayout context.geo.B wr

def ParameterBefore (n pLen qLen : Nat) (p : ParameterPublic) (s : State) : Prop :=
  (∃ W, GenerationMemory p.context W s ∧ W 10 = BitVec.ofNat 64 p.seedUsed ∧ W 16 = BitVec.ofNat 64 p.randUsed) ∧
  FrV n p.context.geo.F p.ws s ∧ s.wr = p.wr ∧ p.context.geo.pLen = pLen ∧ p.context.geo.qLen = qLen

def ParameterPublic.exhausted (p : ParameterPublic) : Bool :=
  decide (p.context.seeds.bytes.length - p.seedUsed < p.context.geo.qLen)

def ParameterChecked (n pLen qLen : Nat) (p : ParameterPublic) (s : State) : Prop :=
  ParameterBefore n pLen qLen p s ∧ isa.eval .b s = some p.exhausted

def ParameterAvailable (n pLen qLen : Nat) (p : ParameterPublic) (s : State) : Prop :=
  ParameterBefore n pLen qLen p s ∧ p.seedUsed + p.context.geo.qLen ≤ p.context.seeds.bytes.length

def ParameterPublic.seed (p : ParameterPublic)
    (room : p.seedUsed + p.context.geo.qLen ≤ p.context.seeds.bytes.length) : SeedPublic where
  context := p.context
  seed := p.context.seeds.slice p.seedUsed p.context.geo.qLen room
  length := by
    change ((p.context.seeds.bytes.drop p.seedUsed).take p.context.geo.qLen).length = _
    simp only [List.length_take, List.length_drop]; omega
  used := p.randUsed
  seedCursor := BitVec.ofNat 64 (p.seedUsed + p.context.geo.qLen)
  bound := p.randBound
  ws := p.ws
  wr := p.wr
  header := p.header

def ParameterTaken (n pLen qLen : Nat) (p : ParameterPublic) (s : State) : Prop :=
  ∃ room, SeedAttemptBefore n pLen qLen (p.seed room) s

theorem parameter_check {n pLen qLen : Nat} {p : ParameterPublic} {s : State}
    (h : ParameterBefore n pLen qLen p s) :
    WP isa (.block (chunkCheck seedTape qLen)) s (ParameterChecked n pLen qLen p) := by
  obtain ⟨⟨W, hm, h10, h16⟩, hf, hw, hp, hq⟩ := h
  obtain ⟨V, R⟩ := hm.rep
  have hl : qLen < 2 ^ 31 := by rcases p.context.geo.qWidth with hh | hh <;> omega
  have total := (hm.slots 9 (by simp [generationSlots])).trans p.context.seedsLengthSlot
  refine WP.mono (chunkCheck_ok hm.layout R seedTape (by decide) (by decide)
    hl h10 total p.seedBound p.context.seeds.size) fun t ⟨hc, hmem, hk⟩ => ?_
  exact ⟨⟨⟨W, hm.congr2 hmem hk, h10, h16⟩,
    hf.congr (hk.gpr (by decide)) hk.2.2, hk.2.2.trans hw, hp, hq⟩,
    by simp only [eval, hc, ParameterPublic.exhausted, hq]⟩

theorem parameter_available {n pLen qLen : Nat} {p : ParameterPublic} {s : State}
    (h : ParameterChecked n pLen qLen p s) (hb : isa.eval .b s = some false) :
    ParameterAvailable n pLen qLen p s := by
  have hn := of_decide_eq_false (Option.some.inj (h.2.symm.trans hb))
  exact ⟨h.1, by have := p.seedBound; omega⟩

theorem parameter_take {n pLen qLen : Nat} {p : ParameterPublic} {s : State}
    (h : ParameterAvailable n pLen qLen p s) :
    WP isa (.block (tapeTake seedTape qLen)) s (ParameterTaken n pLen qLen p) := by
  obtain ⟨⟨⟨W, hm, h10, h16⟩, hf, hw, hp, hq⟩, room⟩ := h
  subst qLen
  obtain ⟨V, R⟩ := hm.rep
  have hl : p.context.geo.qLen < 2 ^ 31 := by rcases p.context.geo.qWidth with hh | hh <;> omega
  refine WP.mono (chunkTake_ok hm.layout R seedTape (by decide) (by decide)
    (by decide) (by decide) (by decide) hl h10) fun t ⟨Lt, Rt, ft, kt⟩ => ?_
  have ht := hm.frame Lt ⟨V, Rt⟩ (by
    intro k hk
    simp only [generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
    (p.context.frame_single ft) kt.2.1 kt.2.2
  refine ⟨room, ⟨⟨_, ht, ?_, ?_, ?_⟩, ht.seeds.slice room,
    hf.congr (kt.gpr (by decide)) kt.2.2, kt.2.2.trans hw, rfl⟩, hp⟩
  · have base := (hm.slots 8 (by simp [generationSlots])).trans p.context.seedsSlot
    simp [seedTape, upd, ParameterPublic.seed, GenerationTape.slice, base]
  · simpa [seedTape, upd, ParameterPublic.seed] using h16
  · simp [seedTape, upd, ParameterPublic.seed]

end VG.Proof.Dsa.X86_64.Generation
