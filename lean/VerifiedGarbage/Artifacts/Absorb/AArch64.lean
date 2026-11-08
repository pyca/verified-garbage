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
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.CmacAesUpdate.AArch64

/-! # Streaming CMAC absorb on AArch64, for each CMAC update -/

@[expose] public section

namespace VG.Artifacts.Absorb.AArch64
def artifactsFor (v : Proof.CmacAes.AArch64.UpdateImpl) : List Artifact := [
  Spec.Cmac.aesAbsorbApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackScratch 2304 .x5
      (Impl.CmacAes.Stream.AArch64.absorb v.callee)
    stack := 2304
    verified := Proof.CmacAes.Stream.AArch64.absorb_framed v
    features := v.features }]
def artifacts : List Artifact :=
  VG.Proof.Variants.CmacAesUpdate.AArch64.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.Absorb.AArch64
