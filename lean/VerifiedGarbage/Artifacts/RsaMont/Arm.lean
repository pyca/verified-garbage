module

public import VerifiedGarbage.Proof.Variants.RsaMont.Arm.Base
public import VerifiedGarbage.Proof.Variants.RsaMont.Arm.Umaal
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Shared callable ARMv7 Montgomery multiplication and squaring -/

@[expose] public section
namespace VG.Artifacts.RsaMont.Arm
open VG.Arm
open VG.Proof.Variants.RsaMont.Arm

def artifacts : List Artifact := [
  Spec.Rsa.Mont.mulApi.artifact target {
    notes := ["Baseline ARMv7: the public operand indices select the specialized Montgomery \
        square when they agree, and coarsely integrated operand scanning otherwise. A shared \
        callable body keeps the arithmetic outside its callers' instruction working sets. \
        The workspace pointer and procedure-call registers occupy a 40-byte stack frame."]
    code := Base.variant.mul
    stack := 40
    verified := Base.variant.verified },
  Spec.Rsa.Mont.mulApi.artifact target {
    suffix := "_umaal"
    notes := ["One shared callable UMAAL kernel handles both Montgomery products and squares. \
        Two-word pipelining fuses product and cancellation with independent carry chains, \
        preserving the 40-byte frame and the baseline's arithmetic and constant-time contracts."]
    code := Umaal.variant.mul
    stack := 40
    verified := Umaal.variant.verified
    features := ["umaal"] }]

end VG.Artifacts.RsaMont.Arm
