module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Contract
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Random
import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.Fn
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.PcVerified
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecPrecomputed
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.RndVerified
import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.PcBase
import VerifiedGarbage.Proof.RsaPkcs1Enc.Contract
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Impl.RsaPkcs1Enc.Arm.Precomputed
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Callees
import VerifiedGarbage.Proof.Rsa.Arm.PublicOfCrt
import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.PcVerified
import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecPrecomputed
import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.RndVerified
import VerifiedGarbage.Impl.RsaPkcs1Enc.Arm.Random
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecVerified
import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.Arm
import VerifiedGarbage.Impl.RsaPkcs1Enc.Arm.Front
import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.Front
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # RSAES-PKCS1-v1_5 (RFC 8017) on ARMv7 -/

namespace VG.Artifacts.RsaPkcs1Enc.Arm

open VG.Proof.Rsa.Arm (CrtImpl)

public def artifacts : List (Artifact Arm.target) :=
  VG.Proof.Variants.RsaPrivateCrt.Arm.variants.flatMap fun (v : CrtImpl) => [
    Spec.RsaPkcs1Enc.decryptPrecomputedApi.artifact Arm.target {
      suffix := v.suffix
      code := Impl.RsaPkcs1Enc.Arm.Fn.decryptPrecomputed (Proof.RsaPkcs1Enc.Arm.Front.bodyName v)
        (Proof.RsaPkcs1Enc.Arm.Dec.decryptCodeP v)
      verified := Proof.RsaPkcs1Enc.Arm.Front.front_scrubbed v },
    Spec.RsaPkcs1Enc.encryptRandomApi.artifact Arm.target {
      suffix := v.suffix
      code := Impl.RsaPkcs1Enc.Arm.Fn.encryptRandom ("vg_rsa_pkcs1_encrypt_precomputed" ++ v.suffix)
        (Impl.RsaPkcs1Enc.Arm.Precomputed.code (Proof.Rsa.Arm.pdOfCrt v).name (Proof.Rsa.Arm.pdOfCrt v).code)
      verified := Proof.RsaPkcs1Enc.Arm.Fn.encryptRandom ("vg_rsa_pkcs1_encrypt_precomputed" ++ v.suffix) v
      publicOutOk := Proof.RsaPkcs1Enc.Arm.Fn.encryptRandom_public ("vg_rsa_pkcs1_encrypt_precomputed" ++ v.suffix) v }]

spec_apis artifacts

end VG.Artifacts.RsaPkcs1Enc.Arm
