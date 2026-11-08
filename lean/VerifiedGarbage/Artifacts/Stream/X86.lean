module

public import VerifiedGarbage.Proof.Sha1.X86.Variants.Interface
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.Sha1.X86
public import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface
public import VerifiedGarbage.Proof.Variants.Sha256.X86

/-! # SHA-1 (FIPS 180-4) streaming on x86, for each SHA-1 implementation -/

@[expose] public section

namespace VG.Artifacts.Stream.X86.Sha1

def artifacts (v : Proof.Sha1.X86.Variants.Backend) : List Artifact := v.functions.map fun f =>
  f.api.artifact X86.target { f.reg with suffix := v.suffix, features := v.features }

end VG.Artifacts.Stream.X86.Sha1

-- Generic stream registrations for every x86 SHA-256 backend
namespace VG.Artifacts.Stream.X86.Sha256

def artifacts (v : Proof.Sha256.X86.Variants.Backend) : List Artifact := v.functions.map fun f =>
  f.api.artifact X86.target { f.reg with suffix := v.suffix, features := v.features }

end VG.Artifacts.Stream.X86.Sha256

namespace VG.Artifacts.Stream.X86

def artifacts : List Artifact :=
  (VG.Proof.Variants.Sha1.X86.variants.flatMap fun v => Sha1.artifacts v) ++
  (VG.Proof.Variants.Sha256.X86.variants.flatMap fun v => Sha256.artifacts v)

end VG.Artifacts.Stream.X86
