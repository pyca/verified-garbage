module

public import VerifiedGarbage.Proof.Zeroize.AArch64Wide
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.TCB.AArch64.Target

/-! # Zeroization on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Zeroize.AArch64
open VG.AArch64

def artifacts : List (Artifact AArch64.target) := [
  Spec.Zeroize.zeroizeApi.artifact target {
    code := Impl.Zeroize.AArch64.zeroizeWide
    verified := Proof.Zeroize.AArch64.wide_scrubbed }]
end VG.Artifacts.Zeroize.AArch64
