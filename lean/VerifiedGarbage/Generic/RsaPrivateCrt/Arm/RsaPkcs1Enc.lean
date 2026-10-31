module

public meta import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.PcVerified
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.PcBase
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Precomputed
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Impl.RsaPkcs1Enc.Arm.Precomputed
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Callees
public import VerifiedGarbage.Proof.Rsa.Arm.PublicOfCrt
import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.PcVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecVerified

/-! # RSAES-PKCS1-v1_5 decryption with implicit rejection on ARMv7, for each implementation of the CRT -/

@[expose] public section

namespace VG.Generic.RsaPrivateCrt.Arm.RsaPkcs1Enc

open VG.Proof.Rsa.Arm (CrtImpl)
open VG.Proof.RsaPkcs1Enc.Arm (decFns)

def artifacts (v : CrtImpl) : List Artifact := [
  Spec.RsaPkcs1Enc.decryptApi.artifact Arm.target {
    suffix := v.suffix
    code := Proof.RsaPkcs1Enc.Arm.Dec.decryptCode v
    stack := 3584
    verified := (Proof.RsaPkcs1Enc.Arm.Dec.code_verified v)
    features := v.features },
  Spec.RsaPkcs1Enc.encryptPrecomputedApi.artifact Arm.target {
    suffix := v.suffix
    code := Impl.RsaPkcs1Enc.Arm.Precomputed.code (Proof.Rsa.Arm.pdOfCrt v).name
      (Proof.Rsa.Arm.pdOfCrt v).code
    stack := 1168
    verified := (Proof.RsaPkcs1Enc.Arm.Pc.code_verified (Proof.Rsa.Arm.pdOfCrt v))
    features := v.features }]

end VG.Generic.RsaPrivateCrt.Arm.RsaPkcs1Enc
