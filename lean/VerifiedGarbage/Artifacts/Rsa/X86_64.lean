module

public import VerifiedGarbage.Proof.Rsa.X86_64.Instances
public import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.PubVerified
public import VerifiedGarbage.Proof.Bignum.X86_64.FoldedBackend
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.PubLit
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
    verified := Proof.Rsa.X86_64.Instances.precomputeAdx_verified
    features := ["bmi2", "adx"] },
  Spec.Rsa.publicPrecomputedCheckedApi.artifact X86_64.target {
    code := Impl.Rsa.X86_64.Folded.checked Proof.Bignum.X86_64.Mont.base.mm
    verified := Proof.Bignum.X86_64.FoldedPublic.base_verified },
  Spec.Rsa.publicPrecomputedCheckedApi.artifact X86_64.target {
    suffix := "_adx"
    code := Impl.Rsa.X86_64.Folded.checked Proof.Bignum.X86_64.Mont.adxSquare.mm
    verified := Proof.Bignum.X86_64.FoldedPublic.adx_verified
    features := ["bmi2", "adx"] },
  Spec.Rsa.publicPrecomputedCheckedApi.artifact X86_64.target {
    suffix := "_ifma"
    code := Impl.Rsa.X86_64.PubIfma.checked Proof.Bignum.X86_64.Mont.adxSquare.mm
    verified := Proof.Bignum.X86_64.Ifma.Pub.ifma_verified
    features := ["avx", "avx512f", "avx512ifma", "avx512vl", "bmi2", "adx"] },
  Spec.Rsa.crtValuesApi.artifact X86_64.target {
    code := Impl.Rsa.X86_64.Keys.CrtValues.code
    verified := Proof.Rsa.X86_64.Instances.crtValues_verified },
  Spec.Rsa.recoverPrimesApi.artifact X86_64.target {
    code := Impl.Rsa.X86_64.Keys.Recover.Folded.code Proof.Rsa.X86_64.CallMont.base.mm
    stack := 8
    verified := Proof.Rsa.X86_64.RecoveryFolded.base_verified },
  Spec.Rsa.recoverPrimesApi.artifact X86_64.target {
    suffix := "_adx"
    code := Impl.Rsa.X86_64.Keys.Recover.Folded.code Proof.Rsa.X86_64.CallMont.adx.mm
    stack := 8
    verified := Proof.Rsa.X86_64.RecoveryFolded.adx_verified
    features := ["bmi2", "adx"] },
  Spec.Rsa.checkKeyApi.artifact X86_64.target {
    code := Impl.Rsa.X86_64.CheckKey.code
    verified := Proof.Rsa.X86_64.Instances.checkKey_verified },
  Spec.Rsa.checkCrtKeyApi.artifact X86_64.target {
    code := Impl.Rsa.X86_64.CheckCrtKey.code
    verified := Proof.Rsa.X86_64.Instances.checkCrtKey_verified }]

end VG.Artifacts.Rsa.X86_64
