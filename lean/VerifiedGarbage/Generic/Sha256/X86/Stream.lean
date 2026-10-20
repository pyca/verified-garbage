module

public import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface

/-! Generic stream registrations for every x86 SHA-256 backend. -/

@[expose] public section

namespace VG.Generic.Sha256.X86.Stream

def artifacts (v : Proof.Sha256.X86.Variants.Backend) : List Artifact := v.functions.map fun f =>
  f.api.artifact X86.target { f.reg with suffix := v.suffix, features := v.features }

end VG.Generic.Sha256.X86.Stream
