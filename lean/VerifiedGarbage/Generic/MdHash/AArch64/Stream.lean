module

public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant

/-! # Streaming Merkle–Damgård hash functions on AArch64 -/

@[expose] public section

namespace VG.Generic.MdHash.AArch64.Stream

def artifacts (v : Proof.Pbkdf2.Md.AArch64.MdHash) : List Artifact := v.stream.map fun f =>
  f.api.artifact AArch64.target { f.reg with suffix := v.suffix, features := v.features }

end VG.Generic.MdHash.AArch64.Stream
