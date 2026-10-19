module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedSubgroup
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SubgroupCT
import VerifiedGarbage.Proof.Framework.Omega

/-! # Public seed-attempt inputs exclude unused frame words -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

structure SeedPublic where
  context : GenerationContext
  seed : GenerationTape context.geo
  length : seed.bytes.length = context.geo.qLen
  used : Nat
  seedCursor : BitVec 64
  bound : used ≤ context.rand.bytes.length

def SeedPublic.subgroup (p : SeedPublic) : SubgroupPublic where
  plan := p.context.geo.subgroupPlan p.context.rand p.seed p.length
    (upd p.context.saved 0 (VG.Proof.Bignum.off p.context.geo.B q))
    (by simpa [upd] using p.context.baseSlot) (by simp [upd])
    (by simpa [upd] using p.context.randSlot) (by simpa [upd] using p.context.randLengthSlot)
  used := p.used
def SeedBefore (qLen : Nat) (p : SeedPublic) (s : State) : Prop :=
  (∃ W, GenerationMemory p.context W s ∧ W 1 = p.seed.ptr ∧ W 16 = BitVec.ofNat 64 p.used ∧ W 10 = p.seedCursor) ∧
  GenerationTapeMemory p.seed s ∧ p.context.geo.qLen = qLen

def SeedPrepared (qLen : Nat) (p : SeedPublic) (s : State) : Prop :=
  (∃ W, GenerationMemory p.context W s ∧ W 0 = VG.Proof.Bignum.off p.context.geo.B q ∧
    W 25 = p.seed.ptr ∧ W 16 = BitVec.ofNat 64 p.used ∧ W 10 = p.seedCursor) ∧
  GenerationTapeMemory p.seed s ∧ p.context.geo.qLen = qLen

theorem seedPrepared_subgroup {qLen : Nat} {p : SeedPublic} {s : State}
    (h : SeedPrepared qLen p s) : SubgroupSized qLen p.subgroup s := by
  obtain ⟨⟨W, hm, h0, h25, h16, _⟩, seed, he⟩ := h
  have matchWords : ∀ i ∈ [0, 5, 14, 15], W i = p.subgroup.plan.W i := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact h0
    · exact hm.slots 5 (by simp [generationSlots])
    · exact hm.slots 14 (by simp [generationSlots])
    · exact hm.slots 15 (by simp [generationSlots])
  have state := hm.subgroupState p.seed p.length seed h0 h25 h16 p.bound
  exact ⟨⟨W, matchWords, state⟩, he⟩

theorem seedArguments_ready {qLen : Nat} {p : SeedPublic} {s : State}
    (h : SeedBefore qLen p s) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.seedArguments qLen)) s (SeedPrepared qLen p) := by
  obtain ⟨⟨W, hm, h1, h16, h10⟩, seed, he⟩ := h
  have hb := (hm.slots 5 (by simp [generationSlots])).trans p.context.baseSlot
  have step := prepareSeed_ok hm
  rw [he] at step
  refine WP.mono step fun t ⟨ht, ff, hk⟩ => ?_
  exact ⟨⟨seedWords W qLen, ht,
    by simp [seedWords, upd, hb], by simp [seedWords, upd, h1], by simpa [seedWords, upd] using h16, by simpa [seedWords, upd] using h10⟩,
    seed.frame ff hk.rd hk.wr, he⟩

end VG.Proof.Dsa.AArch64.Generation
