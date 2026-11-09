module

public import VerifiedGarbage.Proof.Sha1.X86.Shared
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.MdStream.X86.DigestInstances
public import VerifiedGarbage.Proof.Sha1.X86.Variants.Interface
public import VerifiedGarbage.Proof.Variants.Sha1.X86

/-! # SHA-1 (FIPS 180-4) on x86 -/

@[expose] public section

-- SHA-1's one-shot digest on x86, for every x86 SHA-1 backend
namespace VG.Artifacts.Sha1.X86.Digest

def artifactsFor (v : Proof.Sha1.X86.Variants.Backend) : List Artifact := [
  Spec.Sha1.digestApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.MdStream.X86.Digest.digest (Proof.Pbkdf2.Stream.X86.sha1H v.stream)
    stack := 48 + Impl.MdStream.X86.Digest.dframe (Proof.Pbkdf2.Stream.X86.sha1H v.stream)
    verified := Proof.MdStream.X86.Digest.sha1_digest v.stream
    spSafe := Proof.MdStream.X86.Digest.sha1_digestSp v.stream
    features := v.features }]

def artifacts : List Artifact :=
  VG.Proof.Variants.Sha1.X86.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.Sha1.X86.Digest

namespace VG.Artifacts.Sha1.X86

def artifacts : List Artifact :=
  Digest.artifacts ++ [
  Spec.Sha1.initApi.artifact X86.target {
    code := Impl.Sha1.X86.Stream.init
    verified := Proof.Sha1.X86.Shared.init }]

end VG.Artifacts.Sha1.X86
