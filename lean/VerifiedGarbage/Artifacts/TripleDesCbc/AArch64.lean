module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.TripleDes.Cbc
import VerifiedGarbage.Impl.TripleDes.AArch64.Fn
import VerifiedGarbage.Proof.TripleDes.AArch64.CbcVerified
import VerifiedGarbage.Proof.TripleDes.AArch64.CbcTables
import VerifiedGarbage.Proof.TripleDes.AArch64.ModesResidue
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.AArch64.ShortCbc
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Triple DES-CBC on AArch64 -/

namespace VG.Artifacts.TripleDesCbc.AArch64

public def artifacts : List (Artifact AArch64.target) := [
  Spec.TripleDes.cbcEncryptChainedApi.artifact AArch64.target {
    code := Impl.TripleDes.AArch64.Fn.cbcEncryptChained
    verified := Proof.TripleDes.AArch64.ModesResidue.cbcEncryptChainedCode_scrubbed },
  Spec.TripleDes.cbcDecryptChainedApi.artifact AArch64.target {
    code := Impl.TripleDes.AArch64.Fn.cbcDecryptChained
    verified := Proof.TripleDes.AArch64.ModesResidue.cbcDecryptChainedCode_scrubbed }]

spec_apis artifacts

end VG.Artifacts.TripleDesCbc.AArch64
