module

public import VerifiedGarbage.Proof.Zeroize.X86
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Zeroize.Common32
import VerifiedGarbage.Proof.Zeroize.Common32

@[expose] public section

namespace VG.Artifacts.Zeroize.X86
open VG.X86

def artifacts : List Artifact := [
  Spec.Zeroize.zeroizeApi.artifact target {
    code := Impl.Zeroize.X86.zeroize
    verified := Proof.Zeroize.X86.verified }]
end VG.Artifacts.Zeroize.X86
