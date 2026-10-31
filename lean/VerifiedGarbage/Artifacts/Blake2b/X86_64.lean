module

public import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Verified
import VerifiedGarbage.Proof.Blake2.X86_64.Stream.CT
public import VerifiedGarbage.Proof.Framework.Registration

/-! # BLAKE2b (RFC 7693) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Blake2b.X86_64

def artifacts : List Artifact := [
  Spec.Blake2.initBApi.artifact X86_64.target {
    code := Impl.Blake2.X86_64.Stream.init Spec.Blake2.b
    verified := Proof.Blake2.X86_64.Stream.initB_verified }]

end VG.Artifacts.Blake2b.X86_64
