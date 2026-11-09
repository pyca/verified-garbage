module

public import VerifiedGarbage.Proof.MdStream.X86.DigestInstances
public import VerifiedGarbage.Proof.Sha1.X86.Variants.Interface
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.Sha1.X86
public import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface
public import VerifiedGarbage.Proof.Variants.Sha256.X86

/-! # SHA-1 (FIPS 180-4) on x86, for every x86 SHA-1 backend -/

@[expose] public section

namespace VG.Artifacts.Digest.X86.Sha1

def artifacts (v : Proof.Sha1.X86.Variants.Backend) : List Artifact := [
  Spec.Sha1.digestApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.MdStream.X86.Digest.digest (Proof.Pbkdf2.Stream.X86.sha1H v.stream)
    stack := 48 + Impl.MdStream.X86.Digest.dframe (Proof.Pbkdf2.Stream.X86.sha1H v.stream)
    verified := Proof.MdStream.X86.Digest.sha1_digest v.stream
    spSafe := Proof.MdStream.X86.Digest.sha1_digestSp v.stream
    features := v.features }]

end VG.Artifacts.Digest.X86.Sha1

-- SHA-256 (FIPS 180-4) on x86, for every x86 SHA-256 backend
namespace VG.Artifacts.Digest.X86.Sha256

def artifacts (v : Proof.Sha256.X86.Variants.Backend) : List Artifact := [
  Spec.Sha256.digest256Api.artifact X86.target {
    suffix := v.suffix
    code := Impl.MdStream.X86.Digest.digest (Proof.Pbkdf2.Stream.X86.sha256H v.stream)
    stack := 48 + Impl.MdStream.X86.Digest.dframe (Proof.Pbkdf2.Stream.X86.sha256H v.stream)
    verified := Proof.MdStream.X86.Digest.sha256_digest v.stream
    spSafe := Proof.MdStream.X86.Digest.sha256_digestSp v.stream
    features := v.features }]

end VG.Artifacts.Digest.X86.Sha256

namespace VG.Artifacts.Digest.X86

def artifacts : List Artifact :=
  (VG.Proof.Variants.Sha1.X86.variants.flatMap fun v => Sha1.artifacts v) ++
  (VG.Proof.Variants.Sha256.X86.variants.flatMap fun v => Sha256.artifacts v)

end VG.Artifacts.Digest.X86
