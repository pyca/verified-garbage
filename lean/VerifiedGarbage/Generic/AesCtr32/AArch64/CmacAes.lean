module

public import VerifiedGarbage.Proof.CmacAes.Stream.AArch64.Frame
public import VerifiedGarbage.Proof.Framework.Registration
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
public import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.CmacAes.AArch64.UpdateCorrect
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Gcm.Spec

/-! # AES-CMAC (NIST SP 800-38B) on AArch64 -/

@[expose] public section

namespace VG.Generic.AesCtr32.AArch64.CmacAes

open VG.Proof.CmacAes.AArch64

def artifacts (v : Proof.Aes.AArch64.Ctr32Impl) : List Artifact := [
  Spec.Cmac.aesInitApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackScratch 2304 .x3
      (Impl.CmacAes.Stream.AArch64.init v.expand v.callee v.suffix)
    stack := 2304
    verified := Proof.CmacAes.Stream.AArch64.init_framed v
    features := v.features },
  Spec.Cmac.aesFinishApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackScratch 2304 .x4
      (Impl.CmacAes.Stream.AArch64.finish v.callee v.suffix)
    stack := 2304
    verified := Proof.CmacAes.Stream.AArch64.finish_framed v
    features := v.features }]

end VG.Generic.AesCtr32.AArch64.CmacAes
