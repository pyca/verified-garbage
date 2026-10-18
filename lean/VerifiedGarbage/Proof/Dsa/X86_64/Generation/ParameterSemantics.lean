module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ParameterInvariant
import VerifiedGarbage.Proof.Framework.Omega

/-! # One complete seed chunk advances the outer parameter-generation specification -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG

theorem GenerationContext.remaining_step (p : GenerationContext) (used randUsed : Nat)
    (room : used + p.geo.qLen ≤ p.seeds.bytes.length) :
    p.remaining used randUsed =
      match VG.Proof.Dsa.Generation.seedResult (8 * p.geo.pLen) (8 * p.geo.qLen)
        ((p.seeds.bytes.drop used).take p.geo.qLen)
        ((Spec.Dsa.generationChunks p.geo.pLen p.hs.bytes).map Spec.Dsa.decodeBE) (p.rand.bytes.drop randUsed) with
      | none => none
      | some (none, rest) => Spec.Dsa.generateParameters.attempt (8 * p.geo.pLen)
          ((Spec.Dsa.generationChunks p.geo.pLen p.hs.bytes).map Spec.Dsa.decodeBE) (8 * p.geo.qLen)
          (Spec.Dsa.generationChunks p.geo.qLen (p.seeds.bytes.drop (used + p.geo.qLen))) rest
      | some (some a, _) => some a := by
  have hw : 0 < p.geo.qLen := by rcases p.geo.qWidth with h | h <;> omega
  unfold remaining
  rw [VG.Proof.Dsa.Generation.generationChunks_step (bytes := p.seeds.bytes.drop used) hw
    (by simp only [List.length_drop]; omega)]
  rw [VG.Proof.Dsa.Generation.parameterAttempt_seedResult _ _ _ _ _ _ (by
    simp only [List.length_take, List.length_drop]
    rw [Nat.min_eq_left (by omega)])]
  simp only [List.drop_drop]
  rfl

end VG.Proof.Dsa.X86_64.Generation
