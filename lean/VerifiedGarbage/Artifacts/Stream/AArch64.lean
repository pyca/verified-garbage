module

public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.MdHash.AArch64

/-! # Streaming Merkle–Damgård hash functions on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Stream.AArch64

def artifactsFor (v : Proof.Pbkdf2.Md.AArch64.MdHash) : List Artifact := v.stream.map fun f =>
  f.api.artifact AArch64.target { f.reg with suffix := v.suffix, features := v.features }

def artifacts : List Artifact :=
  VG.Proof.Variants.MdHash.AArch64.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.Stream.AArch64
