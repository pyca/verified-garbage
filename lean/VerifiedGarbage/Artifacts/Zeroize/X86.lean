module

public import VerifiedGarbage.Proof.Zeroize.X86
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.Zeroize.X86
open VG.X86

def artifacts : List Artifact := [
  Spec.Zeroize.zeroizeApi.artifact target {
    code := Impl.Zeroize.X86.zeroize
    verified := Proof.Zeroize.X86.verified }]
end VG.Artifacts.Zeroize.X86
