module

public import VerifiedGarbage.Proof.TripleDes.AArch64.CbcVerified
public import VerifiedGarbage.Proof.TripleDes.AArch64.CbcTables
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Triple DES-CBC artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.TripleDesCbc.AArch64

def artifacts : List Artifact := [
  Spec.TripleDes.cbcEncryptChainedApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 464 .x4 58 Impl.TripleDes.AArch64.TablesCbc.encrypt
    stack := 464
    verified := Proof.TripleDes.AArch64.TablesCbc.framed },
  Spec.TripleDes.cbcDecryptChainedApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1008 .x4 125 Impl.TripleDes.AArch64.cbcDecryptChained
    stack := 1008
    verified := Proof.TripleDes.AArch64.cbcDecryptChained_framed }]

end VG.Artifacts.TripleDesCbc.AArch64
