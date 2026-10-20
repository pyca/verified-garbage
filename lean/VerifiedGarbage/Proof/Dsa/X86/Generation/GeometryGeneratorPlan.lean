module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryGenerator
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryTape
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorSearchPlan
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometrySeparate -- shake: keep (proof fields of exposed definitions)

/-! # Instantiate generator search over the caller's original immutable h tape -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout

def GenerationGeometry.generatorPlan (G : GenerationGeometry) (P : PrimeConfig) (T : GenerationTape G)
    (W : Nat → BitVec 32) (qValue : Nat)
    (base : P.base = off G.base arithmetic) (size : P.size = arithmeticBytes)
    (witnessPointer : P.witness = G.pointer witness)
    (parent : W 5 = G.parent) (tape : W 11 = T.pointer) (total : W 12 = BitVec.ofNat 32 T.bytes.length) : GeneratorSearchPlan := by
  have hi := P.lenMax
  have lo := P.lenMin
  have ar : arithmetic + arithmeticBytes ≤ usedBytes G.pLen := by unfold arithmetic arithmeticBytes usedBytes domainCheck; omega
  have er : exponent + P.len ≤ usedBytes G.pLen := by unfold exponent usedBytes domainCheck; omega
  have gr : g + P.len ≤ usedBytes G.pLen := by unfold g usedBytes domainCheck; omega
  have wr : witness + P.len ≤ usedBytes G.pLen := by unfold witness usedBytes domainCheck; omega
  have ast : arithmetic < usedBytes G.pLen := by unfold arithmeticBytes at ar; omega
  have es : exponent < usedBytes G.pLen := by omega
  have gs : g < usedBytes G.pLen := by omega
  have ws : witness < usedBytes G.pLen := by omega
  have ep : (generatorExponentPointer G.parent).setWidth 64 = off G.base exponent := G.pointer_addr es
  have gp : (generatorOutputPointer G.parent).setWidth 64 = off G.base g := G.pointer_addr gs
  refine ⟨P, G.frameBase, G.parent, W, T.bytes, T.pointer, qValue,
    generationGeneratorLayout G P base size witnessPointer, ?_, parent, tape, total, T.size, T.fit, ?_, ?_⟩
  · rw [base]
    exact G.pointer_addr ast
  · intro r hr
    simp only [generatorSearchWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [base, size]; exact T.part ar
    · rw [witnessPointer, G.pointer_addr ws]; exact T.part wr
    · exact T.frame
    · rw [gp]; exact T.part gr
  · intro r hr
    simp only [generatorSearchWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [ep, base, size]; exact G.parts_disjoint er ar (.inl (by unfold exponent arithmetic; omega))
    · rw [ep, witnessPointer, G.pointer_addr ws]; exact G.parts_disjoint er wr (.inl (by unfold exponent witness; omega))
    · rw [ep]; exact (G.frame_part er).symm
    · rw [ep, gp]; exact G.parts_disjoint er gr (.inl (by unfold exponent g; omega))
end VG.Proof.Dsa.X86.Generation
