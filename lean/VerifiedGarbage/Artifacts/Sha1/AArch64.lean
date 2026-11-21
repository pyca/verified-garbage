module

public import VerifiedGarbage.Proof.Sha1.AArch64.Shared
public import VerifiedGarbage.Proof.Sha1.AArch64.Stream.Init
public import VerifiedGarbage.Proof.Sha1.AArch64.Sha2.Compress
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.Sha1Compress.AArch64

/-! # SHA-1 (FIPS 180-4) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Sha1.AArch64

def artifacts : List Artifact := [
  Spec.Sha1.initApi.artifact AArch64.target {
    code := Impl.Sha1.AArch64.Stream.init
    verified := Proof.Sha1.AArch64.Stream.init_scrubbed }] ++
  (VG.Proof.Variants.Sha1Compress.AArch64.variants.flatMap fun (v : Proof.Sha1.AArch64.Compress) => [
    Spec.Sha1.updateApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Sha1.AArch64.Stream.Fn.update v.name v.code
      verified := Proof.Pbkdf2.Md.AArch64.Sha1.update_scrubbed v },
    Spec.Sha1.finalizeApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Sha1.AArch64.Stream.Fn.finalize v.name v.code
      verified := Proof.Pbkdf2.Md.AArch64.Sha1.finalize_scrubbed v },
    Spec.Sha1.digestApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Sha1.AArch64.Stream.Fn.digest v.name v.code
      verified := Proof.Pbkdf2.Md.AArch64.Sha1.digest_scrubbed v }])

end VG.Artifacts.Sha1.AArch64
