import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Sha1.X86.Variants.Interface

/-! SHA-1's compression and streaming functions on x86, registered for every x86 SHA-1
backend (`Proof/Sha1/X86/Variants/Interface.lean`). -/

namespace VG.Generic.Sha1.X86.Stream

def artifacts (v : Proof.Sha1.X86.Variants.Backend) : List Artifact := v.functions.map fun f =>
  { f.api with
    name := f.api.name ++ v.suffix
    target := X86.target
    doc := f.api.doc
    code := f.code
    contract := f.contract
    stack := f.stack
    verified := f.verified
    ofSig := f.ofSig
    ofApi := f.ofApi
    spSafe := f.spSafe
    features := v.features }

end VG.Generic.Sha1.X86.Stream
