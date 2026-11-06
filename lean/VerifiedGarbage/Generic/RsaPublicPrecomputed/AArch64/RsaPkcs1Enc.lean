module

import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.PcVerified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callees
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.RsaPkcs1Enc.AArch64.Precomputed
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Contract
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.PcVerified
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Bytes
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCorrect
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncVerified
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.RndCT
public import VerifiedGarbage.Impl.RsaPkcs1Enc.AArch64.Random
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Random
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Bytes
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCorrect
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncVerified

/-! # PKCS #1 v1.5 encryption over precomputed RSA public variants on AArch64 -/

@[expose] public section

namespace VG.Generic.RsaPublicPrecomputed.AArch64.RsaPkcs1Enc

open VG.Proof.Rsa.AArch64 (PublicImpl)
open VG.Proof.RsaPkcs1Sig.AArch64 (pdOf)
open VG.Proof.RsaPkcs1Enc.AArch64.Enc
open VG.Proof.RsaPkcs1Enc.AArch64 (Rnd.encName Rnd.encCode Rnd.rndStack Rnd.code_verified Rnd.sat)

def artifacts (v : PublicImpl) : List Artifact := [
  Spec.RsaPkcs1Enc.encryptRandomApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.RsaPkcs1Enc.AArch64.Random.code (Rnd.encName (pdOf v)) (Rnd.encCode (pdOf v))
    stack := Rnd.rndStack (pdOf v).stack
    verified := Rnd.code_verified (pdOf v) Pc.sat Rnd.sat
    features := v.features }]

end VG.Generic.RsaPublicPrecomputed.AArch64.RsaPkcs1Enc
