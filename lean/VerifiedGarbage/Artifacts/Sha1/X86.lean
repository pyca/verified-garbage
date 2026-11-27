module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sha1.Contract
import VerifiedGarbage.Proof.Sha1.X86.Scrub
import VerifiedGarbage.Impl.Sha1.X86.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sha1.X86.Variants.Interface
import VerifiedGarbage.Proof.Variants.Sha1.X86
import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface
import VerifiedGarbage.Proof.Variants.Sha256.X86
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SHA-1 (FIPS 180-4) on x86 -/

namespace VG.Artifacts.Sha1.X86

public def artifacts : List (Artifact X86.target) :=
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

spec_apis artifacts

end VG.Artifacts.Sha1.X86
