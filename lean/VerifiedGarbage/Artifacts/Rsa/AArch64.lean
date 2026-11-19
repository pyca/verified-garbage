module

public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Rsa.AArch64.InvBatch
public import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBase
public import VerifiedGarbage.Proof.Rsa.AArch64.CvVerified
public import VerifiedGarbage.Proof.Rsa.AArch64.CkVerified
public import VerifiedGarbage.Proof.Rsa.AArch64.RdVerified
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
public import VerifiedGarbage.Proof.Bignum.AArch64.MulFixedCallMont
public import VerifiedGarbage.Proof.Bignum.AArch64.PrivPreVerified
import Mathlib.Tactic.Finiteness.Attr
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Rsa.AArch64.Scrub
public import VerifiedGarbage.TCB.AArch64.Print

/-! # RSA (RFC 8017) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Rsa.AArch64

def artifacts : List Artifact := [
  Spec.Rsa.publicPrecomputeApi.artifact AArch64.target (VG.AArch64.ScrubAll.scrubAllOf {
    code := Impl.Rsa.AArch64.Precompute.code Proof.Bignum.AArch64.Mont.base.mm
    verified := Proof.Bignum.AArch64.precompute_verified _ }
      ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
       [.v31],
       []⟩ (Proof.Rsa.AArch64.Scrub.publicPrecomputeOk _)),
  Spec.Rsa.privatePrecomputeApi.artifact AArch64.target (VG.AArch64.ScrubAll.scrubAllOf {
    code := Impl.Rsa.AArch64.PrivPre.code Proof.Bignum.AArch64.Mont.base.mm
    verified := Proof.Bignum.AArch64.PrivPre.privPre_verified _ }
      ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
       [.v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v31],
       []⟩ (Proof.Rsa.AArch64.Scrub.privatePrecomputeOk _)),
  Spec.Rsa.crtValuesApi.artifact AArch64.target (VG.AArch64.ScrubAll.scrubAllOf {
    code := Impl.Rsa.AArch64.Keys.CrtValues.code
    verified := Proof.Rsa.AArch64.cv_verified }
      ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
       [.v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26],
       []⟩ (Proof.Rsa.AArch64.Scrub.crtValuesOk _)),
  Spec.Rsa.recoverPrimesDetApi.artifact AArch64.target (VG.AArch64.ScrubAll.scrubAllOf {
    code := Impl.Rsa.AArch64.RecoverDet.code
    verified := Proof.Rsa.AArch64.Rd.rd_verified }
      ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
       [.v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26],
       []⟩ (Proof.Rsa.AArch64.Scrub.recoverPrimesDetOk _)),
  Spec.Rsa.checkKeyApi.artifact AArch64.target (VG.AArch64.ScrubAll.scrubAllOf {
    code := Impl.Rsa.AArch64.CheckKey.code
    verified := Proof.Rsa.AArch64.ck_verified }
      ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
       [],
       []⟩ (Proof.Rsa.AArch64.Scrub.checkKeyOk _))]

end VG.Artifacts.Rsa.AArch64
