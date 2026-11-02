module

public import VerifiedGarbage.Proof.Bignum.AArch64.SquareHelper
public import VerifiedGarbage.Proof.Rsa.AArch64.FoldedChecked
public import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBase
public import VerifiedGarbage.Proof.Rsa.AArch64.CvVerified
public import VerifiedGarbage.Proof.Rsa.AArch64.CkVerified
public import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyVerified
public import VerifiedGarbage.Proof.Rsa.AArch64.RpVerified
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
public import VerifiedGarbage.Proof.Bignum.AArch64.MulFixedCallMont
import Mathlib.Tactic.Finiteness.Attr
public import VerifiedGarbage.Proof.Framework.Registration

/-! # RSA (RFC 8017) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Rsa.AArch64

def artifacts : List Artifact := [
  Spec.Rsa.publicPrecomputeApi.artifact AArch64.target {
    code := Impl.Rsa.AArch64.Precompute.code Proof.Bignum.AArch64.Mont.base.mm
    verified := Proof.Bignum.AArch64.precompute_verified _ },
  Spec.Rsa.publicPrecomputedCheckedApi.artifact AArch64.target {
    code := Impl.Rsa.AArch64.Folded.checked Proof.Bignum.AArch64.Mont.productEight.mm
    verified := Proof.Rsa.AArch64.FoldedPublic.checked_verified _ },
  Spec.Rsa.crtValuesApi.artifact AArch64.target {
    code := Impl.Rsa.AArch64.Keys.CrtValues.code
    verified := Proof.Rsa.AArch64.cv_verified },
  Spec.Rsa.recoverPrimesApi.artifact AArch64.target {
    code := Impl.Rsa.AArch64.Recover.code Proof.Bignum.AArch64.Mont.calledProductEight.mm
    verified := Proof.Rsa.AArch64.rp_verified _ },
  Spec.Rsa.checkKeyApi.artifact AArch64.target {
    code := Impl.Rsa.AArch64.CheckKey.code
    verified := Proof.Rsa.AArch64.ck_verified },
  Spec.Rsa.checkCrtKeyApi.artifact AArch64.target {
    code := Impl.Rsa.AArch64.CheckCrtKey.code
    verified := Proof.Rsa.AArch64.ckc_verified }]

end VG.Artifacts.Rsa.AArch64
