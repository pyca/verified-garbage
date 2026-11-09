module

public import VerifiedGarbage.Proof.Sha1.AArch64.Shared
public import VerifiedGarbage.Proof.Sha1.AArch64.Sha2.Compress
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
public import VerifiedGarbage.Proof.Variants.MdHash.AArch64

/-! # SHA-1 (FIPS 180-4) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Sha1.AArch64

def artifacts : List Artifact := [
  Spec.Sha1.initApi.artifact AArch64.target {
    code := Impl.Sha1.AArch64.Stream.init
    verified := Proof.Sha1.AArch64.Shared.init }] ++
  (VG.Proof.Variants.MdHash.AArch64.sha1Variants.flatMap fun (v : Proof.Pbkdf2.Md.AArch64.MdHash) =>
    v.stream.map fun f =>
      f.api.artifact AArch64.target { f.reg with suffix := v.suffix, features := v.features })

end VG.Artifacts.Sha1.AArch64
