module

public import VerifiedGarbage.Impl.TripleDes.AArch64.Fn
public import VerifiedGarbage.Proof.TripleDes.AArch64.CbcVerified
public import VerifiedGarbage.Proof.TripleDes.AArch64.CbcTables
public import VerifiedGarbage.Proof.TripleDes.AArch64.ModesResidue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.TripleDes.AArch64.ShortCbc
public import VerifiedGarbage.TCB.AArch64.Print

/-! # Triple DES-CBC on AArch64 -/

@[expose] public section

namespace VG.Artifacts.TripleDesCbc.AArch64

def artifacts : List Artifact := [
  Spec.TripleDes.cbcEncryptChainedApi.artifact AArch64.target {
    code := Impl.TripleDes.AArch64.Fn.cbcEncryptChained
    verified := Proof.TripleDes.AArch64.ModesResidue.cbcEncryptChainedCode_scrubbed },
  Spec.TripleDes.cbcDecryptChainedApi.artifact AArch64.target {
    code := Impl.TripleDes.AArch64.Fn.cbcDecryptChained
    verified := Proof.TripleDes.AArch64.ModesResidue.cbcDecryptChainedCode_scrubbed }]

end VG.Artifacts.TripleDesCbc.AArch64
