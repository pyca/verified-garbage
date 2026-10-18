module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedSubgroup
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SubgroupCT
import VerifiedGarbage.Proof.Framework.Omega

/-! # Public seed-attempt inputs exclude unused frame words -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

structure SeedPublic where
  context : GenerationContext
  seed : GenerationTape context.geo
  length : seed.bytes.length = context.geo.qLen
  used : Nat
  seedCursor : BitVec 64
  bound : used ≤ context.rand.bytes.length
  ws : List Region
  wr : List Region
  header : PrimeHeaderLayout context.geo.B wr

def SeedPublic.subgroup (p : SeedPublic) : SubgroupPublic where
  plan := p.context.geo.subgroupPlan p.context.rand p.seed p.length
    (upd p.context.saved 0 (off p.context.geo.B q))
    (by simpa [upd] using p.context.baseSlot) (by simp [upd])
    (by simpa [upd] using p.context.randSlot) (by simpa [upd] using p.context.randLengthSlot)
  used := p.used
  ws := p.ws
  wr := p.wr
  header := by
    change PrimeHeaderLayout (p.context.saved 5) p.wr
    rw [p.context.baseSlot]
    exact p.header

def SeedBefore (n qLen : Nat) (p : SeedPublic) (s : State) : Prop :=
  (∃ W, GenerationMemory p.context W s ∧ W 1 = p.seed.ptr ∧ W 16 = BitVec.ofNat 64 p.used ∧ W 10 = p.seedCursor) ∧
  GenerationTapeMemory p.seed s ∧ FrV n p.context.geo.F p.ws s ∧ s.wr = p.wr ∧ p.context.geo.qLen = qLen

def SeedPrepared (n qLen : Nat) (p : SeedPublic) (s : State) : Prop :=
  (∃ W, GenerationMemory p.context W s ∧ W 0 = off p.context.geo.B q ∧
    W 27 = p.seed.ptr ∧ W 16 = BitVec.ofNat 64 p.used ∧ W 10 = p.seedCursor) ∧
  GenerationTapeMemory p.seed s ∧ FrV n p.context.geo.F p.ws s ∧ s.wr = p.wr ∧ p.context.geo.qLen = qLen

theorem seedPrepared_subgroup {n qLen : Nat} {p : SeedPublic} {s : State}
    (h : SeedPrepared n qLen p s) : SubgroupSized n qLen p.subgroup s := by
  obtain ⟨⟨W, hm, h0, h27, h16, _⟩, seed, hf, hw, he⟩ := h
  have matchWords : ∀ i ∈ [0, 5, 13, 15], W i = p.subgroup.plan.W i := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact h0
    · exact hm.slots 5 (by simp [generationSlots])
    · exact hm.slots 13 (by simp [generationSlots])
    · exact hm.slots 15 (by simp [generationSlots])
  have state := hm.subgroupState p.seed p.length seed h0 h27 h16 p.bound
  exact ⟨⟨W, matchWords, state, hf, hw⟩, he⟩

theorem seedArguments_ready {n qLen : Nat} {p : SeedPublic} {s : State}
    (h : SeedBefore n qLen p s) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.seedArguments qLen)) s (SeedPrepared n qLen p) := by
  obtain ⟨⟨W, hm, h1, h16, h10⟩, seed, hf, hw, he⟩ := h
  have hb := (hm.slots 5 (by simp [generationSlots])).trans p.context.baseSlot
  have step := prepareSeed_ok hm
  rw [he] at step
  refine WP.mono step fun t ⟨ht, ff, hk⟩ => ?_
  exact ⟨⟨seedWords W qLen, ht,
    by simp [seedWords, upd, hb], by simp [seedWords, upd, h1], by simpa [seedWords, upd] using h16, by simpa [seedWords, upd] using h10⟩,
    seed.frame ff hk.2.1 hk.2.2, hf.congr (hk.gpr (by decide)) hk.2.2, hk.2.2.trans hw, he⟩

end VG.Proof.Dsa.X86_64.Generation
