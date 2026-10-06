import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Verified

/-!
# BLAKE2s (RFC 7693) on x86-64

The backend-independent initialization function. Compression and streaming
callers are registered through `Variants/Blake2s/X86_64/` and
`Generic/Blake2s/X86_64/Stream.lean`.
-/

namespace VG.Artifacts.Blake2s.X86_64

def artifacts : List Artifact := [
  { Spec.Blake2.initSApi with
    target := X86_64.target
    doc := Spec.Blake2.initSApi.doc
    code := Impl.Blake2.X86_64.Stream.init Spec.Blake2.s
    contract := Spec.Blake2.initSContract X86_64.abi
    verified := Proof.Blake2.X86_64.Stream.initS_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Blake2s.X86_64
