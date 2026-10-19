module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeometryPrime
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SubgroupState
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.BufferSeparate
import VerifiedGarbage.Proof.Framework.Omega

/-! # Concrete q-phase layout inside the shared generation arena -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

def GenerationGeometry.subgroupPlan (p : GenerationGeometry) (rand seed : GenerationTape p)
    (seedLength : seed.bytes.length = p.qLen) (W : Nat → BitVec 64)
    (h5 : W 5 = p.B) (h0 : W 0 = off p.B q)
    (h13 : W 13 = rand.ptr) (h15 : W 15 = BitVec.ofNat 64 rand.bytes.length) : SubgroupPlan := by
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
  exact {
    prime := p.qPrime rand seed.bytes
    hash := p.hash
    seedPtr := seed.ptr
    output := off p.B q
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
    tapePtr := h13
    tapeLength := h15
    frameHeaders := p.frame_headers
    frameOutside := p.frame_outside
    outputOutside := by
      change ∀ i < p.qLen, arithmeticBytes ≤ ofs (off p.B arithmetic) (off (off p.B q) i)
      intro i hi
      exact out_scr hqa (Offset.contains_base _ (by omega) (by rcases p.qWidth with h | h <;> omega))
    outputFrame := (p.frame_part hq).symm
    outputHash := bufferSeparate_of_regions (len := p.qLen) (by rcases p.qWidth with h | h <;> omega) (p.frame_part hq).symm hqh
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
      · exact (p.stack_part hq).symm }

end VG.Proof.Dsa.X86_64.Generation
