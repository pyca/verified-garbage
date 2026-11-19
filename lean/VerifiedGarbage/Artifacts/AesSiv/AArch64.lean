module

public import VerifiedGarbage.Proof.AesSiv.AArch64.Frame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.AesCcm.Mac
public import VerifiedGarbage.Proof.AesSiv.AArch64.Call
public import VerifiedGarbage.Proof.AesSiv.AArch64.Finish
public import VerifiedGarbage.Proof.AesSiv.AArch64.FinishLong
public import VerifiedGarbage.Proof.AesSiv.AArch64.Open
public import VerifiedGarbage.Proof.AesSiv.AArch64.S2vAd
public import VerifiedGarbage.Proof.AesSiv.Ctr32
public import VerifiedGarbage.Proof.AesSiv.Key
public import VerifiedGarbage.Proof.Cmac.Dbl32
public import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.CmacAes.AArch64.UpdateCorrect
public import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT
public import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Gcm.Stream
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.AesCtr32.AArch64
public import VerifiedGarbage.Proof.Variants.CmacAesUpdate.AArch64

/-! # AES-SIV (RFC 5297) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.AesSiv.AArch64

open VG.Proof.AesSiv.AArch64

def artifacts : List Artifact :=
  (VG.Proof.Variants.AesCtr32.AArch64.variants.attach.flatMap
      fun (v : { v : Proof.Aes.AArch64.Ctr32Impl // v ∈ VG.Proof.Variants.AesCtr32.AArch64.variants }) => [
    Spec.Siv.initApi.artifact AArch64.target (initReg v.1 v.2)]) ++
  (VG.Proof.Variants.CmacAesUpdate.AArch64.variants.attach.flatMap
      fun (v : { v : Proof.CmacAes.AArch64.UpdateImpl // v ∈ VG.Proof.Variants.CmacAesUpdate.AArch64.variants }) => [
    Spec.Siv.encryptApi.artifact AArch64.target (encryptReg v.1 v.2),
    Spec.Siv.decryptApi.artifact AArch64.target (decryptReg v.1 v.2)])

end VG.Artifacts.AesSiv.AArch64
