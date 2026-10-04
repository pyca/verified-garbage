import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Sha1.X86.Shared

/-!
# SHA-1 (FIPS 180-4) on x86

`init`. The compression function, and the streaming `update` and `finalize`
made with it, are registered for each of its implementations
(`Variants/Sha1/X86/`, `Generic/Sha1/X86/Stream.lean`).
-/

namespace VG.Artifacts.Sha1.X86

def artifacts : List Artifact := [
  { Spec.Sha1.initApi with
    target := X86.target
    doc := Spec.Sha1.initApi.doc
    code := Impl.Sha1.X86.Stream.init
    contract := Spec.Sha1.initContract X86.abi
    verified := Proof.Sha1.X86.Shared.init
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Sha1.X86
