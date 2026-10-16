module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Verified
public import VerifiedGarbage.Proof.Blake2.X86_64.Stream.CT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.Spill
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# BLAKE2b (RFC 7693) on x86-64

The backend-independent initialization function. Compression and streaming
callers are registered through `Variants/Blake2b/X86_64/` and
`Generic/Blake2b/X86_64/Stream.lean`.
-/

@[expose] public section

namespace VG.Artifacts.Blake2b.X86_64

def artifacts : List Artifact := [
  Spec.Blake2.initBApi.artifact X86_64.target {
    code := Impl.Blake2.X86_64.Stream.init Spec.Blake2.b
    verified := Proof.Blake2.X86_64.Stream.initB_verified }]

end VG.Artifacts.Blake2b.X86_64
