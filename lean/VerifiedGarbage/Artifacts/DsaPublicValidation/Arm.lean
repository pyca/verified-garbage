module

public import VerifiedGarbage.Proof.Dsa.Arm.PublicValidationVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Dsa.Arm.PublicValidationCT

/-! # Public-key checks shared by ARMv7 DSA signing and verification -/

@[expose] public section
namespace VG.Artifacts.DsaPublicValidation.Arm

def helper (pLen qLen : Nat)
    (v : Verified Arm.target (Impl.Dsa.Arm.PublicValidation.body pLen qLen)
      (Spec.Dsa.PublicValidation.contract (Impl.Dsa.Arm.PublicValidation.layout pLen qLen) Arm.abi)) : Artifact :=
  (Spec.Dsa.PublicValidation.api (Impl.Dsa.Arm.PublicValidation.layout pLen qLen)).artifact Arm.target {
    notes := ["The domain and subgroup checks shared by signing and verification. \
      Callee-saved registers reside in workspace bytes 168–203, apart from the nested arithmetic helpers' saves."]
    code := Impl.Dsa.Arm.PublicValidation.body pLen qLen
    verified := v }

open Proof.Dsa.Arm.PublicValidation in
def artifacts : List Artifact := [
  helper 128 20 (verified 128 20 16 3),
  helper 256 20 (verified 256 20 32 3),
  helper 256 28 (verified 256 28 32 4),
  helper 256 32 (verified 256 32 32 4),
  helper 384 32 (verified 384 32 48 4)]

end VG.Artifacts.DsaPublicValidation.Arm
