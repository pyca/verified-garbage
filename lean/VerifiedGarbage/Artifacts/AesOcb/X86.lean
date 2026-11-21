module

public import VerifiedGarbage.Impl.AesOcb.X86
public import VerifiedGarbage.Proof.AesOcb.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.AesBlocks.X86

/-! # AES-OCB (RFC 7253) on x86 -/

@[expose] public section

namespace VG.Artifacts.AesOcb.X86

def artifacts : List Artifact :=
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

end VG.Artifacts.AesOcb.X86
