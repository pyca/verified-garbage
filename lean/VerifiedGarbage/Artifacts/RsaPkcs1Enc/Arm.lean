module

public meta import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.PcVerified
public meta import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecPrecomputed
public meta import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.RndVerified
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.PcBase
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Contract
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Random
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Impl.RsaPkcs1Enc.Arm.Precomputed
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Callees
public import VerifiedGarbage.Proof.Rsa.Arm.PublicOfCrt
import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.PcVerified
import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecPrecomputed
import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.RndVerified
public import VerifiedGarbage.Impl.RsaPkcs1Enc.Arm.Random
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecVerified
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.Arm

/-! # RSAES-PKCS1-v1_5 (RFC 8017) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.RsaPkcs1Enc.Arm

open VG.Proof.Rsa.Arm (CrtImpl)
open VG.Proof.RsaPkcs1Enc.Arm (decFns)

def artifacts : List Artifact :=
  VG.Proof.Variants.RsaPrivateCrt.Arm.variants.flatMap fun (v : CrtImpl) => [
    Spec.RsaPkcs1Enc.decryptApi.artifact Arm.target {
      suffix := v.suffix
      code := Proof.RsaPkcs1Enc.Arm.Dec.decryptCode v
      stack := 3592
      verified := (Proof.RsaPkcs1Enc.Arm.Dec.code_verified v) },
    Spec.RsaPkcs1Enc.decryptPrecomputedApi.artifact Arm.target {
      suffix := v.suffix
      code := Proof.RsaPkcs1Enc.Arm.Dec.decryptCodeP v
      stack := 3592
      verified := (Proof.RsaPkcs1Enc.Arm.Dec.decryptPrecomputed_verified v) },
    Spec.RsaPkcs1Enc.encryptRandomApi.artifact Arm.target {
      suffix := v.suffix
      code := Impl.RsaPkcs1Enc.Arm.Random.code ("vg_rsa_pkcs1_encrypt_precomputed" ++ v.suffix)
        (Impl.RsaPkcs1Enc.Arm.Precomputed.code (Proof.Rsa.Arm.pdOfCrt v).name (Proof.Rsa.Arm.pdOfCrt v).code)
      stack := 2312
      verified := (Proof.RsaPkcs1Enc.Arm.Rnd.code_verified ("vg_rsa_pkcs1_encrypt_precomputed" ++ v.suffix)
        (Proof.Rsa.Arm.pdOfCrt v)) }]

end VG.Artifacts.RsaPkcs1Enc.Arm
