module

public import VerifiedGarbage.Impl.CmacTripleDes.Stream.AArch64
public import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Cmac.TripleDesContract
public import VerifiedGarbage.TCB.AArch64.Print

/-! # TDEA-CMAC (3DES-CMAC, NIST SP 800-38B) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.CmacTripleDes.AArch64

def artifacts : List Artifact := [
  Spec.Cmac.tdesStreamInitApi.artifact AArch64.target {
    code := Impl.CmacTripleDes.Stream.AArch64.Fn.init
    verified := Proof.CmacTripleDes.AArch64.Fn.init },
  Spec.Cmac.tdesAbsorbApi.artifact AArch64.target {
    code := Impl.CmacTripleDes.Stream.AArch64.Fn.absorb
    verified := Proof.CmacTripleDes.AArch64.Fn.absorb },
  Spec.Cmac.tdesFinishApi.artifact AArch64.target {
    code := Impl.CmacTripleDes.Stream.AArch64.Fn.finish
    verified := Proof.CmacTripleDes.AArch64.Fn.finish }]

end VG.Artifacts.CmacTripleDes.AArch64
