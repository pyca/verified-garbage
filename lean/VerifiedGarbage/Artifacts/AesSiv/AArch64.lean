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

/-! # AES-SIV (RFC 5297) key setup on AArch64 -/

@[expose] public section

namespace VG.Artifacts.AesSiv.AArch64.AesCtr32

open VG.Proof.AesSiv.AArch64

def artifacts (v : Proof.Aes.AArch64.Ctr32Impl) : List Artifact := [
  Spec.Siv.initApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackScratch 2560 .x3
      (Impl.AesSiv.AArch64.init v.expand v.callee v.suffix)
    stack := 2560
    verified := init_framed v
    features := v.features }]

end VG.Artifacts.AesSiv.AArch64.AesCtr32

-- AES-SIV (RFC 5297) encryption and decryption on AArch64
namespace VG.Artifacts.AesSiv.AArch64.CmacAesUpdate

open VG.Proof.AesSiv.AArch64

def artifacts (v : Proof.CmacAes.AArch64.UpdateImpl) : List Artifact := [
  Spec.Siv.encryptApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackScratch 2576 .x7
      (Impl.AesSiv.AArch64.encrypt v.callee v.ctr.callee v.ctr.suffix)
    stack := 2576
    verified := Proof.AesSiv.encrypt_keyed (encrypt_framed v)
    features := v.features },
  Spec.Siv.decryptApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackScratch 2576 .x7
      (Impl.AesSiv.AArch64.decrypt v.callee v.ctr.callee v.ctr.suffix)
    stack := 2576
    verified := Proof.AesSiv.decrypt_keyed (decrypt_framed v)
    features := v.features }]

end VG.Artifacts.AesSiv.AArch64.CmacAesUpdate

namespace VG.Artifacts.AesSiv.AArch64

def artifacts : List Artifact :=
  (VG.Proof.Variants.AesCtr32.AArch64.variants.flatMap fun v => AesCtr32.artifacts v) ++
  (VG.Proof.Variants.CmacAesUpdate.AArch64.variants.flatMap fun v => CmacAesUpdate.artifacts v)

end VG.Artifacts.AesSiv.AArch64
