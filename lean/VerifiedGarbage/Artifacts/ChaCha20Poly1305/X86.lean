module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.ChaCha20Poly1305.Contract
public import VerifiedGarbage.Spec.ChaCha20Poly1305.OutOfPlace
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86.Scrub
import VerifiedGarbage.Impl.ChaCha20Poly1305.X86.SealGather
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Spec.Gcm.OutOfPlace
import VerifiedGarbage.Proof.Variants.ChaCha20Xor.X86
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ChaCha20-Poly1305 (RFC 8439 §2.8) on x86 -/

namespace VG.Artifacts.ChaCha20Poly1305.X86

public def artifacts : List (Artifact X86.target) :=
  VG.Proof.Variants.ChaCha20Xor.X86.variants.flatMap fun (v : Proof.ChaCha20.X86.XorImpl) => [
    Spec.ChaCha20Poly1305.sealApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.ChaCha20Poly1305.X86.Fn.«seal» v.callee
      verified := Proof.ChaCha20Poly1305.X86.Scrub.seal_scrubbed v
      spSafe := Proof.ChaCha20Poly1305.X86.Scrub.seal_spSafe v },
    Spec.ChaCha20Poly1305.openZeroApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.ChaCha20Poly1305.X86.Fn.«open» v.callee
      verified := Proof.ChaCha20Poly1305.X86.Scrub.open_scrubbed v
      spSafe := Proof.ChaCha20Poly1305.X86.Scrub.open_spSafe v },
    Spec.ChaCha20Poly1305.openToApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.ChaCha20Poly1305.X86.Fn.openTo v.callee
      verified := Proof.ChaCha20Poly1305.X86.Scrub.openTo_scrubbed v
      spSafe := Proof.ChaCha20Poly1305.X86.Scrub.openTo_spSafe v },
    Spec.ChaCha20Poly1305.sealGatherApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.ChaCha20Poly1305.X86.Fn.sealGather v.callee v.suffix
      verified := Proof.ChaCha20Poly1305.X86.Scrub.sealGather_scrubbed v
      spSafe := Proof.ChaCha20Poly1305.X86.Scrub.sealGather_spSafe v }]

spec_apis artifacts

end VG.Artifacts.ChaCha20Poly1305.X86
