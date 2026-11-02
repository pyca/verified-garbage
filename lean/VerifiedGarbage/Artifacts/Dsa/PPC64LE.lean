module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyVerified
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Verified
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.Verified
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Derive.Verified
public import VerifiedGarbage.Proof.Dsa.PPC64LE.RandomSign.Verified
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Generate.Verified
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Validate.Verified
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Prevalidated.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # DSA on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Dsa.PPC64LE

def artifacts : List Artifact := [
  Spec.Dsa.verifyApi.artifact PPC64LE.target {
    code := Impl.Dsa.PPC64LE.Verify.verify
    verified := Proof.Dsa.PPC64LE.verify_verified },
  Spec.Dsa.deriveKeyApi.artifact PPC64LE.target {
    code := Impl.Dsa.PPC64LE.Derive.derive
    verified := Proof.Dsa.PPC64LE.deriveKey_verified },
  Spec.Dsa.randomSignApi.artifact PPC64LE.target {
    stack := 304
    code := Impl.Dsa.PPC64LE.RandomSign.code
    verified := Proof.Dsa.PPC64LE.randomSign_verified },
  Spec.Dsa.generateKeyApi.artifact PPC64LE.target {
    stack := 304
    code := Impl.Dsa.PPC64LE.Generate.code
    verified := Proof.Dsa.PPC64LE.generate_verified },
  Spec.Dsa.validatePublicKeyApi.artifact PPC64LE.target {
    code := Impl.Dsa.PPC64LE.Prevalidated.validate
    verified := Proof.Dsa.PPC64LE.validate_verified },
  Spec.Dsa.verifyPrevalidatedApi.artifact PPC64LE.target {
    code := Impl.Dsa.PPC64LE.Prevalidated.verify
    verified := Proof.Dsa.PPC64LE.prevalidated_verified }]

end VG.Artifacts.Dsa.PPC64LE
