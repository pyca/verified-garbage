module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeometryPrimality
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeometryWork
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchPlan
import VerifiedGarbage.Proof.Framework.Omega

/-! # Concrete bounded p-search controller and its unchanged seed and q -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

def GenerationGeometry.searchPlan (p : GenerationGeometry) (seed rand : GenerationTape p)
    (seedLength : seed.bytes.length = p.qLen) (W : Nat → BitVec 64) (offset : Nat)
    (carry : offset + p.count < 2 ^ 32)
    (h1 : W 1 = seed.ptr) (h3 : W 3 = VG.Proof.Bignum.off p.B wrappedSeed)
    (h4 : W 4 = VG.Proof.Bignum.off p.B hashes) (h2 : W 2 = BitVec.ofNat 64 offset)
    (h5 : W 5 = p.B) (h0 : W 0 = VG.Proof.Bignum.off p.B shaped)
    (h14 : W 14 = rand.ptr) (h15 : W 15 = BitVec.ofNat 64 rand.bytes.length) : SearchPlan := by
  let a := p.primalityPlan seed rand seedLength W offset carry h1 h3 h4 h2 h5 h0 h14 h15
  have writes : a.changed = p.pWork := by
    dsimp only [a, PPrimalityPlan.changed, PPrimalityPlan.testWrites, PConstructPlan.changed,
      HashPlan.changed, GenerationGeometry.primalityPlan, GenerationGeometry.constructPlan, GenerationGeometry.hashPlan]
    rw [h5]
    rfl
  have pn : p.pLen ≤ 384 := by rcases p.width with h | h | h <;> omega
  have qn : p.qLen ≤ 32 := by rcases p.qWidth with h | h <;> omega
  have hc := p.small_bound (d := VG.Impl.Dsa.Generation.Layout.control) (n := 24) (by decide) (by decide)
  have hq := p.small_bound (d := q) (n := p.qLen) (by decide) (by unfold arithmeticBytes; omega)
  have hh := p.small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)
  have hp := p.small_bound (d := VG.Impl.Dsa.Generation.Layout.p) (n := p.pLen) (by decide) (by unfold arithmeticBytes; omega)
  have he := p.small_bound (d := exponent) (n := p.pLen) (by decide) (by unfold arithmeticBytes; omega)
  refine {
    attempt := a
    C := VG.Proof.Bignum.off p.B VG.Impl.Dsa.Generation.Layout.control
    controlBase := ?_
    controlSeparate := ?_
    frameControl := p.frame_part hc
    hashControl := p.parts_disjoint hh hc (Or.inl (by decide))
    pControl := ?_
    exponentControl := ?_
    seedSeparate := ?_
    qSeparate := ?_
    tapeSeparate := ?_ }
  · change W 5 + _ = _
    rw [h5]
  · change ∀ r ∈ ⟨p.F, frameBytes⟩ :: a.changed,
      (p.part VG.Impl.Dsa.Generation.Layout.control 24).Disjoint r
    rw [writes]
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact (p.frame_part hc).symm
    · exact p.pWork_separate (Or.inl ⟨rfl, rfl⟩) r hr
  · change (⟨VG.Proof.Bignum.off (W 5) VG.Impl.Dsa.Generation.Layout.p, p.pLen⟩ : Region).Disjoint (p.part VG.Impl.Dsa.Generation.Layout.control 24)
    rw [h5]
    exact p.parts_disjoint hp hc (Or.inl (by unfold VG.Impl.Dsa.Generation.Layout.p VG.Impl.Dsa.Generation.Layout.control; omega))
  · change (⟨VG.Proof.Bignum.off (W 5) exponent, p.pLen⟩ : Region).Disjoint (p.part VG.Impl.Dsa.Generation.Layout.control 24)
    rw [h5]
    exact p.parts_disjoint he hc (Or.inl (by unfold exponent VG.Impl.Dsa.Generation.Layout.control; omega))
  · change ∀ r ∈ (p.part VG.Impl.Dsa.Generation.Layout.control 24) :: ⟨p.F, frameBytes⟩ :: a.changed,
      (⟨seed.ptr, p.qLen⟩ : Region).Disjoint r
    rw [writes, ← seedLength]
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact seed.part hc
    rcases List.mem_cons.mp hr with rfl | hr
    · exact seed.frame
    exact seed.pWork r hr
  · change ∀ r ∈ (p.part VG.Impl.Dsa.Generation.Layout.control 24) :: ⟨p.F, frameBytes⟩ :: a.changed,
      (⟨VG.Proof.Bignum.off (W 5) q, (Spec.Dsa.encodeBE p.qLen (Spec.Dsa.qCandidate (8 * p.qLen) seed.bytes)).length⟩ : Region).Disjoint r
    rw [writes, h5, VG.Proof.Dsa.encodeBE_length]
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact p.parts_disjoint hq hc (Or.inl (by unfold q VG.Impl.Dsa.Generation.Layout.control; omega))
    rcases List.mem_cons.mp hr with rfl | hr
    · exact (p.frame_part hq).symm
    exact p.pWork_separate (Or.inr ⟨rfl, rfl⟩) r hr
  · change ∀ r ∈ (p.part VG.Impl.Dsa.Generation.Layout.control 24) :: ⟨p.F, frameBytes⟩ :: a.changed,
      (⟨rand.ptr, rand.bytes.length⟩ : Region).Disjoint r
    rw [writes]
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact rand.part hc
    rcases List.mem_cons.mp hr with rfl | hr
    · exact rand.frame
    exact rand.pWork r hr

end VG.Proof.Dsa.AArch64.Generation
