module

public import VerifiedGarbage.Proof.Ct.X86_64
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegSetOrder
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Masked

@[expose] public section

namespace VG.Artifacts.Ct.X86_64
open VG.X86_64

def artifacts : List Artifact := [
  Spec.Ct.eqApi.artifact target {
    code := Impl.Ct.X86_64.eq
    verified := Proof.Ct.X86_64.verified }]
end VG.Artifacts.Ct.X86_64
