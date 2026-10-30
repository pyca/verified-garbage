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
    code := Base.variant.mul
    stack := 40
    verified := Base.variant.verified },
  Spec.Rsa.Mont.mulApi.artifact target {
    suffix := "_umaal"
    code := Umaal.variant.mul
    stack := 40
    verified := Umaal.variant.verified
    features := ["umaal"] }]

end VG.Artifacts.RsaMont.Arm
