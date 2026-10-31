module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant

/-! # Streaming Merkle–Damgård hash functions on X86_64 -/

@[expose] public section

namespace VG.Generic.MdHash.X86_64.Stream

def artifacts (v : Proof.Pbkdf2.Md.X86_64.MdHash) : List Artifact := v.stream.map fun f =>
  f.api.artifact X86_64.target { f.reg with suffix := v.suffix, features := v.features }

end VG.Generic.MdHash.X86_64.Stream
