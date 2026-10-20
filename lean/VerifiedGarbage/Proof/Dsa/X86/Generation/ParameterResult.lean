module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ParameterState
import Mathlib.Tactic.Attr.Core

/-! # The finite search result is the shared byte-level parameter-generation result -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86

theorem parameterRemaining_result (P : SearchContextPlan)
    (seeds : P.seeds.bytes.length % P.geometry.qLen = 0)
    (hs : P.hs.bytes.length % P.geometry.pLen = 0) :
    Spec.Dsa.generateParametersBytes P.geometry.pLen P.geometry.qLen
      P.seeds.bytes P.hs.bytes P.witnesses.bytes =
      (parameterRemaining P 0 0).map (Spec.Dsa.encodeParams P.geometry.pLen P.geometry.qLen) := by
  have sizes := P.geometry.lengths
  simp only [Spec.Dsa.generateParametersBytes, sizes, decide_true, Bool.not_true, seeds, hs]
  unfold parameterRemaining Spec.Dsa.generateParameters
  simp only [List.drop_zero]
  rcases sizes with ⟨p, q⟩ | ⟨p, q⟩ | ⟨p, q⟩ <;> rw [p, q] <;>
    simp [Spec.Dsa.subgroupBits, Option.map_eq_bind, Function.comp_def]
end VG.Proof.Dsa.X86.Generation
