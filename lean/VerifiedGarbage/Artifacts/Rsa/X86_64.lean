module

public import VerifiedGarbage.Proof.Rsa.X86_64.Instances
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.Bignum.X86_64.PrivPre.Verified
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
import VerifiedGarbage.Proof.Rsa.X86_64.IfmaLit

/-! # RSA (RFC 8017) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Rsa.X86_64

def artifacts : List Artifact := [
  Spec.Rsa.publicPrecomputeApi.artifact X86_64.target {
    code := Impl.Rsa.X86_64.Precompute.code Proof.Rsa.X86_64.CallMont.base.mm
    stack := 8
    verified := Proof.Rsa.X86_64.Instances.precompute_verified },
  Spec.Rsa.publicPrecomputeApi.artifact X86_64.target {
    suffix := "_adx"
    code := Impl.Rsa.X86_64.Precompute.code Proof.Rsa.X86_64.CallMont.adx.mm
      (Impl.Bignum.X86_64.R2Adx.choice Proof.Rsa.X86_64.CallMont.adx.mm)
    stack := 8
    verified := Proof.Rsa.X86_64.Instances.precomputeAdx_verified },
  Spec.Rsa.privatePrecomputeApi.artifact X86_64.target (X86_64.Scrub.withScrubAll {
    code := Impl.Rsa.X86_64.PrivPre.code Proof.Rsa.X86_64.CallMont.base.mm
    stack := 8
    verified := Proof.Bignum.X86_64.PrivPre.pp_verified } (Proof.Bignum.X86_64.PrivPre.pp_postOut 8)),
  Spec.Rsa.privatePrecomputeApi.artifact X86_64.target (X86_64.Scrub.withScrubAll {
    suffix := "_adx"
    code := Impl.Rsa.X86_64.PrivPre.code Proof.Rsa.X86_64.CallMont.adx.mm
    stack := 8
    verified := Proof.Bignum.X86_64.PrivPre.ppAdx_verified } (Proof.Bignum.X86_64.PrivPre.pp_postOut 8)),
  Spec.Rsa.crtValuesApi.artifact X86_64.target {
    code := Impl.Rsa.X86_64.Keys.CrtValues.code
    verified := Proof.Rsa.X86_64.Instances.crtValues_verified },
  Spec.Rsa.recoverPrimesDetApi.artifact X86_64.target {
    code := Impl.Rsa.X86_64.Keys.RecoverDet.code
    verified := Proof.Rsa.X86_64.Instances.recoverDet_verified },
  Spec.Rsa.checkKeyApi.artifact X86_64.target {
    code := Impl.Rsa.X86_64.CheckKey.code
    verified := Proof.Rsa.X86_64.Instances.checkKey_verified }]

end VG.Artifacts.Rsa.X86_64
