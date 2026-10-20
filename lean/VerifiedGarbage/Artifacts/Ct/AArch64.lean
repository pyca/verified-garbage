module

public import VerifiedGarbage.Proof.Ct.AArch64
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub

@[expose] public section

namespace VG.Artifacts.Ct.AArch64
open VG.AArch64

def artifacts : List Artifact := [
  Spec.Ct.eqApi.artifact target {
    code := Impl.Ct.AArch64.eq
    verified := Proof.Ct.AArch64.verified }]
end VG.Artifacts.Ct.AArch64
