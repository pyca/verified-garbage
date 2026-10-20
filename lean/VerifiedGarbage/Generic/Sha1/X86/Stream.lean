module

public import VerifiedGarbage.Proof.Sha1.X86.Variants.Interface

/-! SHA-1's compression and streaming functions on x86, registered for every x86 SHA-1
backend (`Proof/Sha1/X86/Variants/Interface.lean`). -/

@[expose] public section

namespace VG.Generic.Sha1.X86.Stream

def artifacts (v : Proof.Sha1.X86.Variants.Backend) : List Artifact := v.functions.map fun f =>
  f.api.artifact X86.target { f.reg with suffix := v.suffix, features := v.features }

end VG.Generic.Sha1.X86.Stream
