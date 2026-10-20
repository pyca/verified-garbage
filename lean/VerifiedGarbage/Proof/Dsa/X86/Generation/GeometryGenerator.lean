module
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorLayout
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Geometry
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryBuffers
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometrySeparate

/-! # Generator buffers are disjoint from the prepared arithmetic context -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout

theorem generationGeneratorLayout (G : GenerationGeometry) (P : PrimeConfig)
    (base : P.base = off G.base arithmetic) (size : P.size = arithmeticBytes)
    (witnessPointer : P.witness = G.pointer witness) : GeneratorLayout P G.frameBase G.parent := by
  have hi := P.lenMax
  have lo := P.lenMin
  have ar : arithmetic + arithmeticBytes ≤ usedBytes G.pLen := by unfold arithmetic arithmeticBytes usedBytes domainCheck; omega
  have er : exponent + P.len ≤ usedBytes G.pLen := by unfold exponent usedBytes domainCheck; omega
  have gr : g + P.len ≤ usedBytes G.pLen := by unfold g usedBytes domainCheck; omega
  have wr : witness + P.len ≤ usedBytes G.pLen := by unfold witness usedBytes domainCheck; omega
  have es : exponent < usedBytes G.pLen := by omega
  have gs : g < usedBytes G.pLen := by omega
  have ws : witness < usedBytes G.pLen := by omega
  have ep : (generatorExponentPointer G.parent).setWidth 64 = off G.base exponent := G.pointer_addr es
  have gp : (generatorOutputPointer G.parent).setWidth 64 = off G.base g := G.pointer_addr gs
  refine ⟨?_, ?_, G.pointer_fit es er, ?_, ?_, G.pointer_fit gs gr, ?_, ?_⟩
  · rw [base, size]
    exact G.frame_part ar
  · rw [witnessPointer, G.pointer_addr ws]
    exact G.frame_part wr
  · rw [ep, base, size]
    exact G.parts_disjoint er ar (.inl (by unfold exponent arithmetic; omega))
  · rw [ep, witnessPointer, G.pointer_addr ws]
    exact G.parts_disjoint er wr (.inl (by unfold exponent witness; omega))
  · rw [gp, base, size]
    exact G.parts_disjoint gr ar (.inl (by unfold g arithmetic; omega))
  · rw [gp]
    exact G.frame_part gr
end VG.Proof.Dsa.X86.Generation
