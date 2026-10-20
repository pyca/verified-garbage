module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedAttemptCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ParameterInvariant
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ChunkTake
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ChunkCheck
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextFrame
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextSlice

/-! # Public seed and witness cursors for the complete parameter search -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.Generation VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64

structure ParameterPublic where
  context : GenerationContext
  seedUsed : Nat
  seedBound : seedUsed ≤ context.seeds.bytes.length
  randUsed : Nat
  randBound : randUsed ≤ context.rand.bytes.length

def ParameterBefore (pLen qLen : Nat) (p : ParameterPublic) (s : State) : Prop :=
  (∃ W, GenerationMemory p.context W s ∧ W 10 = BitVec.ofNat 64 p.seedUsed ∧ W 16 = BitVec.ofNat 64 p.randUsed) ∧
  p.context.geo.pLen = pLen ∧ p.context.geo.qLen = qLen

def ParameterPublic.exhausted (p : ParameterPublic) : Bool :=
  decide (p.context.seeds.bytes.length - p.seedUsed < p.context.geo.qLen)

def ParameterChecked (pLen qLen : Nat) (p : ParameterPublic) (s : State) : Prop :=
  ParameterBefore pLen qLen p s ∧ isa.eval (.nonzero .x .x0) s = some p.exhausted

def ParameterAvailable (pLen qLen : Nat) (p : ParameterPublic) (s : State) : Prop :=
  ParameterBefore pLen qLen p s ∧ p.seedUsed + p.context.geo.qLen ≤ p.context.seeds.bytes.length

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

def ParameterTaken (pLen qLen : Nat) (p : ParameterPublic) (s : State) : Prop :=
  ∃ room, SeedAttemptBefore pLen qLen (p.seed room) s

theorem parameter_check {pLen qLen : Nat} {p : ParameterPublic} {s : State}
    (h : ParameterBefore pLen qLen p s) :
    WP isa (.block (chunkCheck seedTape qLen)) s (ParameterChecked pLen qLen p) := by
  obtain ⟨⟨W, hm, h10, h16⟩, hp, hq⟩ := h
  obtain ⟨V, R⟩ := hm.rep
  have hl : qLen < 65536 := by rcases p.context.geo.qWidth with hh | hh <;> omega
  have total := (hm.slots 9 (by simp [generationSlots])).trans p.context.seedsLengthSlot
  refine WP.mono (chunkCheck_frame_ok hm.layout R seedTape (by decide) (by decide)
    hl h10 total p.seedBound p.context.seeds.size) fun t ⟨hc, hmem, hk⟩ => ?_
  exact ⟨⟨⟨W, hm.congr2 hmem (hk.mono (by decide)), h10, h16⟩,
    hp, hq⟩,
    by
      simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hc, ParameterPublic.exhausted, hq]
      by_cases room : qLen ≤ p.context.seeds.bytes.length - p.seedUsed
      · simp only [ite_eq_left room, decide_eq_false (show ¬ p.context.seeds.bytes.length - p.seedUsed < qLen by omega)]; rfl
      · simp only [ite_eq_right room, decide_eq_true (show p.context.seeds.bytes.length - p.seedUsed < qLen by omega)]; rfl⟩

theorem parameter_available {pLen qLen : Nat} {p : ParameterPublic} {s : State}
    (h : ParameterChecked pLen qLen p s) (hb : isa.eval (.nonzero .x .x0) s = some false) :
    ParameterAvailable pLen qLen p s := by
  have hn := of_decide_eq_false (Option.some.inj (h.2.symm.trans hb))
  exact ⟨h.1, by have := p.seedBound; omega⟩

theorem parameter_take {pLen qLen : Nat} {p : ParameterPublic} {s : State}
    (h : ParameterAvailable pLen qLen p s) :
    WP isa (.block (tapeTake seedTape qLen)) s (ParameterTaken pLen qLen p) := by
  obtain ⟨⟨⟨W, hm, h10, h16⟩, hp, hq⟩, room⟩ := h
  subst qLen
  obtain ⟨V, R⟩ := hm.rep
  have hl : p.context.geo.qLen < 65536 := by rcases p.context.geo.qWidth with hh | hh <;> omega
  refine WP.mono (chunkTake_ok hm.layout R seedTape (by decide) (by decide)
    (by decide) (by decide) (by decide) hl h10) fun t ⟨Lt, Rt, ft, kt⟩ => ?_
  have ht := hm.frame Lt ⟨V, Rt⟩ (by
    intro k hk
    simp only [generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
    (p.context.frame_single ft) kt.rd kt.wr
  refine ⟨room, ⟨⟨_, ht, ?_, ?_, ?_⟩, ht.seeds.slice room,
    rfl⟩, hp⟩
  · have base := (hm.slots 8 (by simp [generationSlots])).trans p.context.seedsSlot
    simp [seedTape, upd, ParameterPublic.seed, GenerationTape.slice, base]
  · simpa [seedTape, upd, ParameterPublic.seed] using h16
  · simp [seedTape, upd, ParameterPublic.seed]

end VG.Proof.Dsa.AArch64.Generation
