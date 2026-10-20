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

/-! Streaming absorb is emitted for every verified whole-block CMAC update
variant. Its buffering proof depends on the update contract, not on CTR. -/

@[expose] public section

namespace VG.Generic.CmacAesUpdate.AArch64.Absorb
def artifacts (v : Proof.CmacAes.AArch64.UpdateImpl) : List Artifact := [
  Spec.Cmac.aesAbsorbApi.artifact AArch64.target {
    suffix := v.suffix
    notes := ["This implementation chains blocks with `" ++ v.callee.name ++ "`."]
    code := Impl.StackScratch.AArch64.withStackScratch 2304 .x5
      (Impl.CmacAes.Stream.AArch64.absorb v.callee)
    stack := 2304
    verified := Proof.CmacAes.Stream.AArch64.absorb_framed v
    features := v.features }]
end VG.Generic.CmacAesUpdate.AArch64.Absorb
