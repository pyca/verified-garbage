module

public import VerifiedGarbage.Proof.Sha1.X86.Shared
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.MdStream.X86.DigestInstances
public import VerifiedGarbage.Proof.Sha1.X86.Variants.Interface
public import VerifiedGarbage.Proof.Variants.Sha1.X86
public import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface
public import VerifiedGarbage.Proof.Variants.Sha256.X86

/-! # SHA-1 (FIPS 180-4) on x86 -/

@[expose] public section

namespace VG.Artifacts.Sha1.X86

def artifacts : List Artifact :=
  (VG.Proof.Variants.Sha1.X86.variants.flatMap fun (v : Proof.Sha1.X86.Variants.Backend) => [
    Spec.Sha1.digestApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.MdStream.X86.Digest.digest (Proof.Pbkdf2.Stream.X86.sha1H v.stream)
      stack := 48 + Impl.MdStream.X86.Digest.dframe (Proof.Pbkdf2.Stream.X86.sha1H v.stream)
      verified := Proof.MdStream.X86.Digest.sha1_digest v.stream
      spSafe := Proof.MdStream.X86.Digest.sha1_digestSp v.stream }]) ++ [
  Spec.Sha1.initApi.artifact X86.target {
    code := Impl.Sha1.X86.Stream.init
    verified := Proof.Sha1.X86.Shared.init }] ++
  (VG.Proof.Variants.Sha1.X86.variants.flatMap fun (v : Proof.Sha1.X86.Variants.Backend) =>
    v.functions.map fun f =>
      f.api.artifact X86.target { f.reg with suffix := v.suffix})

end VG.Artifacts.Sha1.X86
