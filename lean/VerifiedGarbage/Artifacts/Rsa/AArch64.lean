module

public import VerifiedGarbage.Proof.Rsa.AArch64.Instances
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

/-- The two repeated squares are shared by all RSA callers. -/
def squareHelper (slot : Spec.Rsa.MontSquare.Slot) : Artifact :=
  let M := match slot with
    | .r2 => Proof.Bignum.AArch64.Mont.blocked
    | .y => Proof.Bignum.AArch64.Mont.squareEight
  (Spec.Rsa.MontSquare.squareApi slot).artifact AArch64.target {
    code := M.mm slot.index slot.index slot.index
    verified := Proof.Bignum.AArch64.SquareHelper.verified M slot }

/-- Share the repeated five-square window body across all CRT callers. -/
def windowHelper : Artifact :=
  Spec.Rsa.MontWindow.windowApi.artifact AArch64.target {
    code := Proof.Bignum.AArch64.WindowFive.body.code
    verified := Proof.Bignum.AArch64.WindowShared.verified }

def artifacts : List Artifact := [squareHelper .r2, squareHelper .y, windowHelper,
  Spec.Rsa.publicPrecomputeApi.artifact AArch64.target {
    code := Impl.Rsa.AArch64.Precompute.code Proof.Bignum.AArch64.Mont.base.mm
    verified := Proof.Bignum.AArch64.precompute_verified _ },
  Spec.Rsa.publicPrecomputedCheckedApi.artifact AArch64.target {
    code := Impl.Rsa.AArch64.Folded.checked Proof.Bignum.AArch64.Mont.productEight.mm
    verified := Proof.Rsa.AArch64.FoldedPublic.checked_verified _ },
  Spec.Rsa.privateCrtApi.artifact AArch64.target {
    code := Proof.Bignum.AArch64.WindowFive.code
    verified := Proof.Bignum.AArch64.WindowFive.base_verified },
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
