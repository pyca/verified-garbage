module

public import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Verified
import VerifiedGarbage.Proof.Blake2.X86_64.Stream.CT
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# BLAKE2s (RFC 7693) on x86-64

The backend-independent initialization function. Compression and streaming
callers are registered through `Variants/Blake2s/X86_64/` and
`Generic/Blake2s/X86_64/Stream.lean`.
-/

@[expose] public section

namespace VG.Artifacts.Blake2s.X86_64

def artifacts : List Artifact := [
  Spec.Blake2.initSApi.artifact X86_64.target {
    code := Impl.Blake2.X86_64.Stream.init Spec.Blake2.s
    verified := Proof.Blake2.X86_64.Stream.initS_verified }]

end VG.Artifacts.Blake2s.X86_64
