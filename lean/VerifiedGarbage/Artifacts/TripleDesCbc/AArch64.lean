module

public import VerifiedGarbage.Proof.TripleDes.AArch64.CbcVerified
public import VerifiedGarbage.Proof.TripleDes.AArch64.CbcTables
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.TripleDes.AArch64.ShortCbc
public import VerifiedGarbage.TCB.AArch64.Print

/-! # Triple DES-CBC on AArch64 -/

@[expose] public section

namespace VG.Artifacts.TripleDesCbc.AArch64

def artifacts : List Artifact := [
  Spec.TripleDes.cbcEncryptChainedApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 464 .x4 58 Impl.TripleDes.AArch64.TablesCbc.encrypt
    verified := Proof.TripleDes.AArch64.TablesCbc.framed },
  Spec.TripleDes.cbcDecryptChainedApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1120 .x4 140
      Impl.TripleDes.AArch64.Short.cbcDecryptChained
    verified := Proof.TripleDes.AArch64.Short.Cbc.cbcDecryptChained_framed }]

end VG.Artifacts.TripleDesCbc.AArch64
