module

public import VerifiedGarbage.Proof.Zeroize.AArch64Wide
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub

@[expose] public section

namespace VG.Artifacts.Zeroize.AArch64
open VG.AArch64

def artifacts : List Artifact := [
  Spec.Zeroize.zeroizeApi.artifact target {
    code := Impl.Zeroize.AArch64.zeroizeWide
    verified := Proof.Zeroize.AArch64.wideVerified }]
end VG.Artifacts.Zeroize.AArch64
