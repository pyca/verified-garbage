module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # RSAES-PKCS1-v1_5 (RFC 8017) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.RsaPkcs1Enc.PPC64LE

def artifacts : List Artifact := [
  Spec.RsaPkcs1Enc.decryptPrecomputedApi.artifact PPC64LE.target {
    code := Impl.RsaPkcs1Enc.PPC64LE.Fn.decryptPrecomputed
    verified := .scrubbed Proof.RsaPkcs1Enc.PPC64LE.Scrub.decryptPrecomputed_scrubbed },
  Spec.RsaPkcs1Enc.encryptRandomApi.artifact PPC64LE.target {
    code := Impl.RsaPkcs1Enc.PPC64LE.Fn.encryptRandom
    verified := .scrubbed Proof.RsaPkcs1Enc.PPC64LE.Scrub.encryptRandom_scrubbed }]

end VG.Artifacts.RsaPkcs1Enc.PPC64LE
