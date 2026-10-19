module

public import VerifiedGarbage.Proof.Dsa.Derive
import VerifiedGarbage.Proof.Framework.Omega

/-! # The packed generated domain denotes exactly its mathematical parameters -/

@[expose] public section
namespace VG.Proof.Dsa.Generation
open VG VG.Proof.Dsa

theorem encodeParams_length (pLen qLen : Nat) (a : Spec.Dsa.Params) :
    (Spec.Dsa.encodeParams pLen qLen a).length = 2 * pLen + qLen := by
  simp only [Spec.Dsa.encodeParams, List.length_append, encodeBE_length]
  omega

theorem paramsBytes_encodeParams {pLen qLen : Nat} {a : Spec.Dsa.Params}
    (hp : a.p < 256 ^ pLen) (hq : a.q < 256 ^ qLen) (hg : a.g < 256 ^ pLen) :
    Spec.Dsa.paramsBytes pLen qLen (Spec.Dsa.encodeParams pLen qLen a) = a := by
  let pb := Spec.Dsa.encodeBE pLen a.p
  let qb := Spec.Dsa.encodeBE qLen a.q
  let gb := Spec.Dsa.encodeBE pLen a.g
  have lp : pb.length = pLen := encodeBE_length _ _
  have lq : qb.length = qLen := encodeBE_length _ _
  have lg : gb.length = pLen := encodeBE_length _ _
  have tp : ((pb ++ qb) ++ gb).take pLen = pb := by
    rw [List.append_assoc, ← lp, List.take_left]
  have tq : (((pb ++ qb) ++ gb).drop pLen).take qLen = qb := by
    rw [List.append_assoc, ← lp, List.drop_left, ← lq, List.take_left]
  have tg : (((pb ++ qb) ++ gb).drop (pLen + qLen)).take pLen = gb := by
    rw [← lp, ← lq, ← List.length_append, List.drop_left, lp, ← lg, List.take_length]
  rw [paramsBytes_eq]
  change (⟨Spec.Dsa.decodeBE (((pb ++ qb) ++ gb).take pLen),
    Spec.Dsa.decodeBE ((((pb ++ qb) ++ gb).drop pLen).take qLen),
    Spec.Dsa.decodeBE ((((pb ++ qb) ++ gb).drop (pLen + qLen)).take pLen)⟩ : Spec.Dsa.Params) = a
  rw [tp, tq, tg, decodeBE_encodeBE hp, decodeBE_encodeBE hq, decodeBE_encodeBE hg]


theorem check_encodedParams {pLen qLen : Nat} {a : Spec.Dsa.Params}
    (hl : Spec.Dsa.lengthsValid pLen qLen)
    (hp : a.p < 256 ^ pLen) (hq : a.q < 256 ^ qLen) (hg : a.g < 256 ^ pLen) :
    Spec.Dsa.checkParametersBytes pLen qLen (Spec.Dsa.encodeParams pLen qLen a) =
      decide (Spec.Dsa.parametersValid a) := by
  unfold Spec.Dsa.checkParametersBytes
  rw [encodeParams_length, paramsBytes_encodeParams hp hq hg]
  simp only [hl, decide_true, beq_self_eq_true, Bool.true_and]

end VG.Proof.Dsa.Generation
