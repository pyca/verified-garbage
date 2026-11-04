module

public import VerifiedGarbage.Proof.MdStream.X86.DigestInstances
public import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SHA-224 (FIPS 180-4) on x86, for every x86 SHA-256 backend -/

@[expose] public section

namespace VG.Generic.Sha256.X86.DigestSha224

def artifacts (v : Proof.Sha256.X86.Variants.Backend) : List Artifact := [
  Spec.Sha256.digest224Api.artifact X86.target {
    suffix := v.suffix
    code := Impl.MdStream.X86.Digest.digest (Proof.Pbkdf2.Stream.X86.sha224H v.stream)
    stack := 48 + Impl.MdStream.X86.Digest.dframe (Proof.Pbkdf2.Stream.X86.sha224H v.stream)
    verified := Proof.MdStream.X86.Digest.sha224_digest v.stream
    spSafe := Proof.MdStream.X86.Digest.sha224_digestSp v.stream
    features := v.features }]

end VG.Generic.Sha256.X86.DigestSha224
