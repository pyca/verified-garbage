module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.EncVerified
public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # RSAES-PKCS1-v1_5 (RFC 8017) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.RsaPkcs1Enc.PPC64LE

def artifacts : List Artifact := [
  Spec.RsaPkcs1Enc.encryptPrecomputedApi.artifact PPC64LE.target {
    code := Impl.RsaPkcs1Enc.PPC64LE.Precomputed.code
    stack := 2224
    verified := Proof.RsaPkcs1Enc.PPC64LE.Enc.code_verified },
  Spec.RsaPkcs1Enc.decryptApi.artifact PPC64LE.target {
    code := Impl.RsaPkcs1Enc.PPC64LE.Decrypt.code
    stack := Proof.RsaPkcs1Enc.PPC64LE.Dec.stackBytes
    verified := Proof.RsaPkcs1Enc.PPC64LE.Dec.dec_verified }]

end VG.Artifacts.RsaPkcs1Enc.PPC64LE
