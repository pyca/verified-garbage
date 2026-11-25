module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.Scrub
public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.FrontScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Target

/-! # RSAES-PKCS1-v1_5 (RFC 8017) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.RsaPkcs1Enc.PPC64LE

def artifacts : List (Artifact PPC64LE.target) := [
  Spec.RsaPkcs1Enc.decryptPrecomputedApi.artifact PPC64LE.target {
    code := Impl.RsaPkcs1Enc.PPC64LE.Fn.decryptPrecomputed
    verified := Proof.RsaPkcs1Enc.PPC64LE.Front.front_scrubbed },
  Spec.RsaPkcs1Enc.encryptRandomApi.artifact PPC64LE.target {
    code := Impl.RsaPkcs1Enc.PPC64LE.Fn.encryptRandom
    verified := Proof.RsaPkcs1Enc.PPC64LE.Scrub.encryptRandom_scrubbed
    publicOutOk := Proof.RsaPkcs1Enc.PPC64LE.Scrub.encryptRandom_public }]

end VG.Artifacts.RsaPkcs1Enc.PPC64LE
