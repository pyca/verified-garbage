module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Contract
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Random
import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.Scrub
import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.FrontScrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # RSAES-PKCS1-v1_5 (RFC 8017) on PPC64LE -/

namespace VG.Artifacts.RsaPkcs1Enc.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.RsaPkcs1Enc.decryptPrecomputedApi.artifact PPC64LE.target {
    code := Impl.RsaPkcs1Enc.PPC64LE.Fn.decryptPrecomputed
    verified := Proof.RsaPkcs1Enc.PPC64LE.Front.front_scrubbed },
  Spec.RsaPkcs1Enc.encryptRandomApi.artifact PPC64LE.target {
    code := Impl.RsaPkcs1Enc.PPC64LE.Fn.encryptRandom
    verified := Proof.RsaPkcs1Enc.PPC64LE.Scrub.encryptRandom_scrubbed
    publicOutOk := Proof.RsaPkcs1Enc.PPC64LE.Scrub.encryptRandom_public }]

spec_apis artifacts

end VG.Artifacts.RsaPkcs1Enc.PPC64LE
