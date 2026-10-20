module

public import VerifiedGarbage.Spec.Dsa.Generate

/-! # The finite native search result matches the public byte adapter -/

@[expose] public section
namespace VG.Proof.Dsa.Generation
open VG

theorem generateParametersBytes_attempt {pLen qLen : Nat} (hl : Spec.Dsa.generationLengthsValid pLen qLen)
    (seeds hs witnesses : List Byte) (hslen : seeds.length % qLen = 0) (hhlen : hs.length % pLen = 0) :
    Spec.Dsa.generateParametersBytes pLen qLen seeds hs witnesses =
      (Spec.Dsa.generateParameters.attempt (8 * pLen)
        ((Spec.Dsa.generationChunks pLen hs).map Spec.Dsa.decodeBE) (8 * qLen)
        (Spec.Dsa.generationChunks qLen seeds) witnesses).map (Spec.Dsa.encodeParams pLen qLen) := by
  have sub : Spec.Dsa.subgroupBits (8 * pLen) = some (8 * qLen) := by
    rcases hl with h | h | h <;> simp [Spec.Dsa.subgroupBits, h.1, h.2]
  simp only [Spec.Dsa.generateParametersBytes, hl, decide_true, Bool.not_true, hslen, hhlen,
    bne_self_eq_false, Bool.false_or, Bool.false_eq_true, ite_false,
    Spec.Dsa.generateParameters, sub, bind, Option.bind]
  cases Spec.Dsa.generateParameters.attempt (8 * pLen)
    ((Spec.Dsa.generationChunks pLen hs).map Spec.Dsa.decodeBE) (8 * qLen)
    (Spec.Dsa.generationChunks qLen seeds) witnesses <;> rfl

end VG.Proof.Dsa.Generation
