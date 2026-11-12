module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.VerifyVerified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.RecoverVerified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.SignVerified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.SignP
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # RSASSA-PKCS1-v1_5 (RFC 8017) on PPC64LE -/

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
    verified := Proof.RsaPkcs1Sig.PPC64LE.Sign.code_verified },
  Spec.RsaPkcs1Sig.signPrecomputedApi.artifact PPC64LE.target {
    code := Impl.RsaPkcs1Sig.PPC64LE.Sign.codeP
    stack := Proof.RsaPkcs1Sig.PPC64LE.Sign.stackBytes
    verified := Proof.RsaPkcs1Sig.PPC64LE.Sign.codeP_verified }]

end VG.Artifacts.RsaPkcs1Sig.PPC64LE
