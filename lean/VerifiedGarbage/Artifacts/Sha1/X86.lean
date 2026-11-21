module

public import VerifiedGarbage.Proof.Sha1.X86.Scrub
public import VerifiedGarbage.Impl.Sha1.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
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
      code := Impl.Sha1.X86.Fn.digest (Proof.Pbkdf2.Stream.X86.sha1H v.stream)
      verified := Proof.Sha1.X86.Scrub.digest_scrubbed v
      spSafe := Proof.Sha1.X86.Scrub.digest_spSafe v }]) ++ [
  Spec.Sha1.initApi.artifact X86.target {
    code := Impl.Sha1.X86.Fn.init
    verified := Proof.Sha1.X86.Scrub.init_scrubbed }] ++
  (VG.Proof.Variants.Sha1.X86.variants.flatMap fun (v : Proof.Sha1.X86.Variants.Backend) => [
    Spec.Sha1.updateApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.Sha1.X86.Fn.update v.stream.upd
      verified := Proof.Sha1.X86.Variants.Backend.update_scrubbed v
      spSafe := Proof.Sha1.X86.Variants.Backend.update_spSafe v },
    Spec.Sha1.finalizeApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.Sha1.X86.Fn.finalize v.stream.fin
      verified := Proof.Sha1.X86.Variants.Backend.finalize_scrubbed v
      spSafe := Proof.Sha1.X86.Variants.Backend.finalize_spSafe v }])

end VG.Artifacts.Sha1.X86
