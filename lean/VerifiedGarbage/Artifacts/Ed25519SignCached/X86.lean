module

public import VerifiedGarbage.Proof.Ed25519.X86.SignCached.Verified
import VerifiedGarbage.Impl.Mont.Mod
import VerifiedGarbage.Proof.MdStream.Spec
import VerifiedGarbage.Spec.Rc2
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.Ed25519SignCached.X86

def artifacts : List Artifact := [
  Spec.Ed25519.signCachedApi.artifact X86.target {
    notes := ["Includes SHA-512, scalar reduction, \
      base-point multiplication, and scalar multiply-add. Secret intermediate buffers are cleared before returning."]
    consts := Impl.Ed25519.X86.combConsts
    code := Impl.Ed25519.X86.SignCached.code
    stack := 280
    verified := Proof.Ed25519.X86.SignCached.signCached_verified }]

end VG.Artifacts.Ed25519SignCached.X86
