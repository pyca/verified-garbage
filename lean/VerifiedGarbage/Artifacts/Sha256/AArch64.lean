module

public import VerifiedGarbage.Proof.Sha256.AArch64.Shared
public import VerifiedGarbage.Proof.Sha256.AArch64.Sha2.Compress
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
public import VerifiedGarbage.Proof.Variants.MdHash.AArch64

/-! # SHA-256 (FIPS 180-4) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Sha256.AArch64

def artifacts : List Artifact := [
  Spec.Sha256.init224Api.artifact AArch64.target {
    code := Impl.Sha256.AArch64.Stream.init224
    verified := Proof.Sha256.AArch64.Shared.init224 },
  Spec.Sha256.initApi.artifact AArch64.target {
    code := Impl.Sha256.AArch64.Stream.init
    verified := Proof.Sha256.AArch64.Shared.init }] ++
  ((VG.Proof.Variants.MdHash.AArch64.sha224Variants ++
      VG.Proof.Variants.MdHash.AArch64.sha256Variants).flatMap fun (v : Proof.Pbkdf2.Md.AArch64.MdHash) =>
    v.stream.map fun f =>
      f.api.artifact AArch64.target { f.reg with suffix := v.suffix, features := v.features })

end VG.Artifacts.Sha256.AArch64
