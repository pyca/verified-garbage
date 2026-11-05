module

public import VerifiedGarbage.Proof.MdStream.X86.DigestInstances
public import VerifiedGarbage.Proof.Sha1.X86.Variants.Interface
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SHA-1 (FIPS 180-4) on x86, for every x86 SHA-1 backend -/

@[expose] public section

namespace VG.Generic.Sha1.X86.Digest

def artifacts (v : Proof.Sha1.X86.Variants.Backend) : List Artifact := [
  Spec.Sha1.digestApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.MdStream.X86.Digest.digest (Proof.Pbkdf2.Stream.X86.sha1H v.stream)
    stack := 48 + Impl.MdStream.X86.Digest.dframe (Proof.Pbkdf2.Stream.X86.sha1H v.stream)
    verified := Proof.MdStream.X86.Digest.sha1_digest v.stream
    spSafe := Proof.MdStream.X86.Digest.sha1_digestSp v.stream
    features := v.features }]

end VG.Generic.Sha1.X86.Digest
