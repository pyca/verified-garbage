module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Zeroize.Contract
import VerifiedGarbage.Proof.Zeroize.AArch64Wide
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Zeroization on AArch64 -/

namespace VG.Artifacts.Zeroize.AArch64
open VG.AArch64

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Zeroize.zeroizeApi.artifact target {
    code := Impl.Zeroize.AArch64.zeroizeWide
    verified := Proof.Zeroize.AArch64.wide_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Zeroize.AArch64
