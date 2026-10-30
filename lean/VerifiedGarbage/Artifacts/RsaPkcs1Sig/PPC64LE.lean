module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.VerifyVerified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.RecoverVerified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.SignVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # PKCS #1 v1.5 signing, and verification and recovery with a precomputed RSA public key, on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.RsaPkcs1Sig.PPC64LE

def artifacts : List Artifact := [
  Spec.RsaPkcs1Sig.verifyPrecomputedApi.artifact PPC64LE.target {
    code := Impl.RsaPkcs1Sig.PPC64LE.Precomputed.code
    stack := 2224
    verified := Proof.RsaPkcs1Sig.PPC64LE.Ver.code_verified },
  Spec.RsaPkcs1Sig.recoverPrecomputedApi.artifact PPC64LE.target {
    code := Impl.RsaPkcs1Sig.PPC64LE.RecoverPrecomputed.code
    stack := 2224
    verified := Proof.RsaPkcs1Sig.PPC64LE.Rec.code_verified },
  Spec.RsaPkcs1Sig.signApi.artifact PPC64LE.target {
    code := Impl.RsaPkcs1Sig.PPC64LE.Sign.code
    stack := Proof.RsaPkcs1Sig.PPC64LE.Sign.stackBytes
    verified := Proof.RsaPkcs1Sig.PPC64LE.Sign.code_verified }]

end VG.Artifacts.RsaPkcs1Sig.PPC64LE
