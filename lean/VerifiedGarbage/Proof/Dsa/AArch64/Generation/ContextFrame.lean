module

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeometryWork
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Context
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeometryPrime
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SubgroupState
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.TaintBatch

/-! ### `Dsa.AArch64.Generation.ContextSubgroup`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.Generation.GeometrySubgroup`, which this module and modules that import it used -/

section

/-! # Concrete q-phase layout inside the shared generation arena -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

def GenerationGeometry.subgroupPlan (p : GenerationGeometry) (rand seed : GenerationTape p)
    (seedLength : seed.bytes.length = p.qLen) (W : Nat → BitVec 64)
    (h5 : W 5 = p.B) (h0 : W 0 = VG.Proof.Bignum.off p.B q)
    (h14 : W 14 = rand.ptr) (h15 : W 15 = BitVec.ofNat 64 rand.bytes.length) : SubgroupPlan := by
  have ha : arithmetic + arithmeticBytes ≤ usedBytes p.pLen := by
    rcases p.width with h | h | h <;> rw [h] <;> decide
  have hh : VG.Impl.Dsa.Generation.Layout.hash + oRsa ≤ usedBytes p.pLen := by
    rcases p.width with h | h | h <;> rw [h] <;> decide
  have hq : q + p.qLen ≤ usedBytes p.pLen := by
    rcases p.lengths with ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> rw [h1,h2] <;> decide
  have hw : witness + p.qLen ≤ usedBytes p.pLen := by
    rcases p.lengths with ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> rw [h1,h2] <;> decide
  have hqa : (p.part q p.qLen).Disjoint (p.part arithmetic arithmeticBytes) :=
    p.parts_disjoint hq ha (by left; rcases p.qWidth with h | h <;> rw [h] <;> decide)
  have hqh : (p.part q p.qLen).Disjoint (p.part VG.Impl.Dsa.Generation.Layout.hash oRsa) :=
    p.parts_disjoint hq hh (Or.inr (by decide))
  have hqw : (p.part q p.qLen).Disjoint (p.part witness p.qLen) :=
    p.parts_disjoint hq hw (by left; rcases p.qWidth with h | h <;> rw [h] <;> decide)
  have hs : Region.Sub ⟨W 5, domainCheck⟩ ⟨p.B, usedBytes p.pLen⟩ := by
    rw [h5]; exact Region.sub_prefix (by unfold usedBytes; omega_using [])
  exact {
    prime := p.qPrime rand seed.bytes
    F := p.F
    hash := p.hash
    seedPtr := seed.ptr
    output := VG.Proof.Bignum.off p.B q
    seed := seed.bytes
    W := W
    width := p.qWidth
    words := rfl
    size := rfl
    draw := rfl
    checks := rfl
    seedLength := seedLength
    modulus := rfl
    base := by change W 5 + _ = _; rw [h5]; rfl
    outputPtr := by change W 5 + _ = _; rw [h5]
    outputSlot := h0
    witnessPtr := by change W 5 + _ = _; rw [h5]; rfl
    tapePtr := h14
    tapeLength := h15
    frameHeaders := p.frame_headers
    frameOutside := p.frame_outside
    outputOutside := by
      change ∀ i < p.qLen, arithmeticBytes ≤ ofs (VG.Proof.Bignum.off p.B arithmetic) (VG.Proof.Bignum.off (VG.Proof.Bignum.off p.B q) i)
      intro i hi
      exact out_scr hqa (Offset.contains_base _ (by omega_using [hi]) (by rcases p.qWidth with h | h <;> omega_using [hi, h]))
    outputFrame := (p.frame_part hq).symm
    outputScratch := hqh.symm
    tapeHash := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact rand.part hq
      · exact rand.part hh
      · exact rand.stack.sub_right (below_sub (by decide) (by decide))
    framePrime := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact p.frame_part ha
      · exact p.frame_part hw
      · exact p.frame_below
    hashPrime := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact p.parts_disjoint hh ha (Or.inl (by decide))
      · exact p.parts_disjoint hh hw (Or.inl (by decide))
      · exact (p.stack_part hh).symm
    outputPrime := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hqa
      · exact hqw
      · exact (p.stack_part hq).symm
    geometry := {
      stackSize := p.stackSize
      arenaBound := by have := p.arenaBound; rw [h5]; unfold usedBytes at this; omega_using [this]
      tapeBound := rand.bound
      tapeArena := rand.arena.sub_right hs
      tapeFrame := rand.frame
      tapeStack := rand.stack
      arenaFrame := (p.frameArena.sub_right hs).symm
      arenaStack := (p.stackArena.sub_right hs).symm
      hashTest := by
        change ∀ r ∈ [(⟨VG.Proof.Bignum.off (W 5) arithmetic, arithmeticBytes⟩ : Region),
          ⟨VG.Proof.Bignum.off (W 5) witness, 8 * p.qLen / 8⟩,
          below p.F 272], (⟨p.hash, oRsa⟩ : Region).Disjoint r
        rw [h5, Nat.mul_div_cancel_left _ (by decide)]
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact p.parts_disjoint hh ha (Or.inl (by decide))
        · exact p.parts_disjoint hh hw (Or.inl (by decide))
        · exact (p.stack_part hh).symm } }

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # The persistent search state supplies every precondition of the q phase -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

def GenerationMemory.subgroupPlan {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (seed : GenerationTape p.geo) (hlen : seed.bytes.length = p.geo.qLen)
    (h0 : W 0 = VG.Proof.Bignum.off p.geo.B q) : SubgroupPlan :=
  p.geo.subgroupPlan p.rand seed hlen W
    ((h.slots 5 (by simp [generationSlots])).trans p.baseSlot) h0
    ((h.slots 14 (by simp [generationSlots])).trans p.randSlot)
    ((h.slots 15 (by simp [generationSlots])).trans p.randLengthSlot)

theorem GenerationMemory.subgroupState {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (seed : GenerationTape p.geo) (hlen : seed.bytes.length = p.geo.qLen)
    (hseed : GenerationTapeMemory seed s) (h0 : W 0 = VG.Proof.Bignum.off p.geo.B q)
    (h25 : W 25 = seed.ptr) {used : Nat} (h16 : W 16 = BitVec.ofNat 64 used)
    (hu : used ≤ p.rand.bytes.length) : SubgroupState (h.subgroupPlan seed hlen h0) used s := by
  have qn : p.geo.qLen ≤ 32 := by rcases p.geo.qWidth with hh | hh <;> omega_using [hh]
  have ha := p.geo.small_bound (d := arithmetic) (n := arithmeticBytes) (by decide) (by rfl)
  have hh := p.geo.small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)
  have hq := p.geo.small_bound (d := q) (n := p.geo.qLen) (by decide) (by unfold arithmeticBytes; omega_using [qn])
  have hw := p.geo.small_bound (d := witness) (n := p.geo.qLen) (by decide) (by unfold arithmeticBytes; omega_using [qn])
  refine {
    layout := h.layout
    rep := h.rep
    label := ?_
    seed := ?_
    scratch := h.scratch.sub (n := arithmeticBytes) ha (by decide)
    tape := h.rand.source ha
    outputWrite := ?_
    witnessWrite := ?_
    usedSlot := h16
    usedBound := hu
    arena := (by
      have hb := (h.slots 5 (by simp [generationSlots])).trans p.baseSlot
      have := h.scratch.sub (o := 0) (n := domainCheck) (by unfold usedBytes; omega_using []) (by decide)
      simp only [VG.Proof.Bignum.off, BitVec.add_zero] at this
      change Scr s (W 5) domainCheck
      rw [hb]; exact this)
    tapeCover := h.rand.cover }
  · change LabAt s p.geo.F p.geo.hash W seed.ptr p.geo.qLen
    refine ⟨h25, (h.slots 26 (by simp [generationSlots])).trans p.hashLenSlot, by omega_using [qn], ?_, ?_, ?_, ?_⟩
    · simpa only [hlen] using hseed.cover
    · simpa only [hlen, GenerationGeometry.part, GenerationGeometry.hash] using seed.part hh
    · simpa only [hlen] using seed.frame
    · simpa only [hlen] using (seed.stack.sub_right (below_sub (a := 16) (by decide) (by decide))).symm
  · change Spec.Rsa.bytesAt s.mem seed.ptr p.geo.qLen = seed.bytes
    rw [← hlen]
    exact hseed.bytes
  · change ∀ i < p.geo.qLen, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off p.geo.B q) i) 1
    intro i hi
    rw [VG.Proof.Bignum.off_off]
    exact h.scratch.region (by omega_using [hq, hi]) (by decide)
  · change ∀ i < p.geo.qLen, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off p.geo.B witness) i) 1
    intro i hi
    rw [VG.Proof.Bignum.off_off]
    exact h.scratch.region (by omega_using [hw, hi]) (by decide)

end VG.Proof.Dsa.AArch64.Generation

end

end

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
    [⟨VG.Proof.Bignum.off p.geo.B arithmetic, arithmeticBytes⟩, ⟨VG.Proof.Bignum.off p.geo.B witness, p.geo.qLen⟩,
      below p.geo.F 272] ++
    [⟨p.geo.F, frameBytes⟩], ∃ out ∈ p.changed, Region.Sub r out
  have qn : p.geo.qLen ≤ 32 := by rcases p.geo.qWidth with hh | hh <;> omega_using [hh]
  have part (d n : Nat) (hd : d ≤ domainCheck) (hn : n ≤ arithmeticBytes) :
      ∃ out ∈ p.changed, Region.Sub (p.geo.part d n) out :=
    ⟨⟨p.geo.B, usedBytes p.geo.pLen⟩, by simp [GenerationContext.changed],
      p.geo.part_sub (p.geo.small_bound hd hn)⟩
  intro r hr
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact part q p.geo.qLen (by decide) (by unfold arithmeticBytes; omega_using [qn])
  · exact part VG.Impl.Dsa.Generation.Layout.hash oRsa (by decide) (by decide)
  · exact ⟨below p.geo.F 272, by simp [GenerationContext.changed], below_sub (by decide) (by decide)⟩
  · exact part arithmetic arithmeticBytes (by decide) (by rfl)
  · exact part witness p.geo.qLen (by decide) (by unfold arithmeticBytes; omega_using [qn])
  · exact ⟨below p.geo.F 272, by simp [GenerationContext.changed], fun _ h => h⟩
  · exact ⟨⟨p.geo.F, frameBytes⟩, by simp [GenerationContext.changed], fun _ h => h⟩

end VG.Proof.Dsa.AArch64.Generation
