module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextSearch
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextFrame
import VerifiedGarbage.Proof.Framework.Omega

/-! # Lift the bounded prime search back to the persistent generation state -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

theorem GenerationMemory.search_frame {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (seed : GenerationTape p.geo) (hlen : seed.bytes.length = p.geo.qLen)
    (h1 : W 1 = seed.ptr) {m m' : Mem}
    (hf : Frame (searchWrites (h.searchPlan seed hlen h1).attempt (h.searchPlan seed hlen h1).C) m m') :
    Frame p.changed m m' := by
  have h5 := (h.slots 5 (by simp [generationSlots])).trans p.baseSlot
  have writes : searchWrites (h.searchPlan seed hlen h1).attempt (h.searchPlan seed hlen h1).C =
      p.geo.part VG.Impl.Dsa.Generation.Layout.control 24 :: ⟨p.geo.F, frameBytes⟩ :: p.geo.pWork := by
    dsimp only [searchWrites, GenerationMemory.searchPlan, GenerationGeometry.searchPlan,
      PPrimalityPlan.changed, PPrimalityPlan.testWrites, PConstructPlan.changed,
      HashPlan.changed, GenerationGeometry.primalityPlan, GenerationGeometry.constructPlan,
      GenerationGeometry.hashPlan, searchWords, upd]
    rw [h5]
    rfl
  rw [writes] at hf
  apply GenerationContext.frame_parts hf
  have pn : p.geo.pLen ≤ 384 := by rcases p.geo.width with hh | hh | hh <;> omega
  have qn : p.geo.qLen ≤ 32 := by rcases p.geo.qWidth with hh | hh <;> omega
  have part (d n : Nat) (hd : d ≤ domainCheck) (hn : n ≤ arithmeticBytes) :
      ∃ out ∈ p.changed, Region.Sub (p.geo.part d n) out :=
    ⟨⟨p.geo.B, usedBytes p.geo.pLen⟩, by simp [GenerationContext.changed],
      p.geo.part_sub (p.geo.small_bound hd hn)⟩
  intro r hr
  simp only [GenerationGeometry.pWork, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact part VG.Impl.Dsa.Generation.Layout.control 24 (by decide) (by decide)
  · exact ⟨⟨p.geo.F, frameBytes⟩, by simp [GenerationContext.changed], fun _ h => h⟩
  · exact part shaped p.geo.pLen (by decide) (by unfold arithmeticBytes; omega)
  · exact part hashes ((p.geo.count + 1) * p.geo.qLen) (by decide)
      (by have := p.geo.hashSizes.2.1; unfold arithmeticBytes; omega)
  · exact part wrappedSeed p.geo.qLen (by decide) (by unfold arithmeticBytes; omega)
  · exact part VG.Impl.Dsa.Generation.Layout.hash oRsa (by decide) (by decide)
  · exact ⟨below p.geo.F 16, by simp [GenerationContext.changed], below_sub (by decide) (by decide)⟩
  · exact part arithmetic arithmeticBytes (by decide) (by rfl)
  · exact part VG.Impl.Dsa.Generation.Layout.p p.geo.pLen (by decide) (by unfold arithmeticBytes; omega)
  · exact part exponent p.geo.pLen (by decide) (by unfold arithmeticBytes; omega)
  · exact part arithmetic arithmeticBytes (by decide) (by rfl)
  · exact part witness p.geo.pLen (by decide) (by unfold arithmeticBytes; omega)
  · exact ⟨⟨p.geo.F, frameBytes⟩, by simp [GenerationContext.changed], fun _ h => h⟩

end VG.Proof.Dsa.AArch64.Generation
