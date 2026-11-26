module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Blowfish.Cbc
import VerifiedGarbage.Impl.Blowfish.AArch64.Fn
import VerifiedGarbage.Proof.Blowfish.AArch64.CbcVerified
import VerifiedGarbage.Proof.Blowfish.AArch64.ModesResidue
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Blowfish-CBC on AArch64 -/

namespace VG.Artifacts.BlowfishCbc.AArch64

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Blowfish.cbcEncryptChainedApi.artifact AArch64.target {
    code := Impl.Blowfish.AArch64.Fn.cbcEncryptChained
    verified := Proof.Blowfish.AArch64.ModesResidue.cbcEncryptChainedCode_scrubbed },
  Spec.Blowfish.cbcDecryptChainedApi.artifact AArch64.target {
    code := Impl.Blowfish.AArch64.Fn.cbcDecryptChained
    verified := Proof.Blowfish.AArch64.ModesResidue.cbcDecryptChainedCode_scrubbed }]

spec_apis artifacts

end VG.Artifacts.BlowfishCbc.AArch64
