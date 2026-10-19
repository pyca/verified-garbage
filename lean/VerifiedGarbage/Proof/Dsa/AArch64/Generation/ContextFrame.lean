module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextSubgroup
import VerifiedGarbage.Proof.Framework.Omega

/-! # Lift phase footprints to the full native parameter-search workspace -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

theorem GenerationContext.frame_parts {p : GenerationContext} {rs : List Region} {m m' : Mem}
    (hf : Frame rs m m')
    (cover : ∀ r ∈ rs, ∃ q ∈ p.changed, Region.Sub r q) : Frame p.changed m m' := by
  intro a ha
  apply hf a
  intro r hr hc
  obtain ⟨q, hq, sub⟩ := cover r hr
  exact ha q hq (sub a hc)

theorem GenerationContext.frame_single {p : GenerationContext} {m m' : Mem}
    (hf : Frame [⟨p.geo.F, frameBytes⟩] m m') : Frame p.changed m m' :=
  hf.mono (by intro r hr; rcases List.mem_singleton.mp hr with rfl; simp [changed])

theorem GenerationMemory.subgroup_frame {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (seed : GenerationTape p.geo) (hlen : seed.bytes.length = p.geo.qLen)
    (h0 : W 0 = VG.Proof.Bignum.off p.geo.B q) {m m' : Mem}
    (hf : Frame (h.subgroupPlan seed hlen h0).changed m m') : Frame p.changed m m' := by
  apply GenerationContext.frame_parts hf
  change ∀ r ∈ [⟨VG.Proof.Bignum.off p.geo.B q, p.geo.qLen⟩, ⟨p.geo.hash, oRsa⟩, retR p.geo.F] ++
    [⟨VG.Proof.Bignum.off p.geo.B arithmetic, arithmeticBytes⟩, ⟨VG.Proof.Bignum.off p.geo.B witness, p.geo.qLen⟩] ++
    [⟨p.geo.F, frameBytes⟩], ∃ out ∈ p.changed, Region.Sub r out
  have qn : p.geo.qLen ≤ 32 := by rcases p.geo.qWidth with hh | hh <;> omega
  have part (d n : Nat) (hd : d ≤ domainCheck) (hn : n ≤ arithmeticBytes) :
      ∃ out ∈ p.changed, Region.Sub (p.geo.part d n) out :=
    ⟨⟨p.geo.B, usedBytes p.geo.pLen⟩, by simp [GenerationContext.changed],
      p.geo.part_sub (p.geo.small_bound hd hn)⟩
  intro r hr
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact part q p.geo.qLen (by decide) (by unfold arithmeticBytes; omega)
  · exact part VG.Impl.Dsa.Generation.Layout.hash oRsa (by decide) (by decide)
  · exact ⟨below p.geo.F 16, by simp [GenerationContext.changed], below_sub (by decide) (by decide)⟩
  · exact part arithmetic arithmeticBytes (by decide) (by rfl)
  · exact part witness p.geo.qLen (by decide) (by unfold arithmeticBytes; omega)
  · exact ⟨⟨p.geo.F, frameBytes⟩, by simp [GenerationContext.changed], fun _ h => h⟩

end VG.Proof.Dsa.AArch64.Generation
