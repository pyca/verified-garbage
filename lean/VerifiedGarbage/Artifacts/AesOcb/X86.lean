module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ocb.Contract
import VerifiedGarbage.Impl.AesOcb.X86
import VerifiedGarbage.Proof.AesOcb.X86.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.AesBlocks.X86
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-OCB (RFC 7253) on x86 -/

namespace VG.Artifacts.AesOcb.X86

public def artifacts : List (Artifact X86.target) :=
  VG.Proof.Variants.AesBlocks.X86.variants.flatMap fun (v : Proof.Aes.X86.BlocksImpl) => [
    Spec.Ocb.initApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesOcb.X86.Fn.init (Proof.AesOcb.X86.callees v)
      verified := Proof.AesOcb.X86.Scrub.init_scrubbed v
      spSafe := Proof.AesOcb.X86.Scrub.init_fnSpSafe v },
    Spec.Ocb.sealApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesOcb.X86.Fn.«seal» (Proof.AesOcb.X86.callees v)
      verified := Proof.AesOcb.X86.Scrub.seal_scrubbed v
      spSafe := Proof.AesOcb.X86.Scrub.seal_fnSpSafe v },
    Spec.Ocb.openApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesOcb.X86.Fn.«open» (Proof.AesOcb.X86.callees v)
      verified := Proof.AesOcb.X86.Scrub.open_scrubbed v
      spSafe := Proof.AesOcb.X86.Scrub.open_fnSpSafe v }]

spec_apis artifacts

end VG.Artifacts.AesOcb.X86
