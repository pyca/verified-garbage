module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cmac.TripleDesContract
import VerifiedGarbage.Impl.CmacTripleDes.Stream.AArch64
import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # TDEA-CMAC (3DES-CMAC, NIST SP 800-38B) on AArch64 -/

namespace VG.Artifacts.CmacTripleDes.AArch64

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Cmac.tdesStreamInitApi.artifact AArch64.target {
    code := Impl.CmacTripleDes.Stream.AArch64.Fn.init
    verified := Proof.CmacTripleDes.AArch64.Fn.init },
  Spec.Cmac.tdesAbsorbApi.artifact AArch64.target {
    code := Impl.CmacTripleDes.Stream.AArch64.Fn.absorb
    verified := Proof.CmacTripleDes.AArch64.Fn.absorb },
  Spec.Cmac.tdesFinishApi.artifact AArch64.target {
    code := Impl.CmacTripleDes.Stream.AArch64.Fn.finish
    verified := Proof.CmacTripleDes.AArch64.Fn.finish }]

spec_apis artifacts

end VG.Artifacts.CmacTripleDes.AArch64
