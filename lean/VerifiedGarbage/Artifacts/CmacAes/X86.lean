module

public import VerifiedGarbage.Impl.CmacAes.Stream.X86
public import VerifiedGarbage.Proof.CmacAes.Stream.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.AesCtr32.X86

/-! # AES-CMAC (NIST SP 800-38B) on x86 -/

@[expose] public section

namespace VG.Artifacts.CmacAes.X86

def artifacts : List Artifact :=
  VG.Proof.Variants.AesCtr32.X86.variants.flatMap fun (v : Proof.Aes.X86.Ctr32Impl) => [
    Spec.Cmac.aesInitApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.CmacAes.Stream.X86.Fn.init v.expand v.callee v.suffix
      verified := .scrubbed (Proof.CmacAes.Stream.X86.Scrub.init_scrubbed v)
      spSafe := Proof.CmacAes.Stream.X86.Scrub.init_fnSpSafe v },
    Spec.Cmac.aesAbsorbApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.CmacAes.Stream.X86.Fn.absorb v.callee v.suffix
      verified := .scrubbed (Proof.CmacAes.Stream.X86.Scrub.absorb_scrubbed v)
      spSafe := Proof.CmacAes.Stream.X86.Scrub.absorb_fnSpSafe v },
    Spec.Cmac.aesFinishApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.CmacAes.Stream.X86.Fn.finish v.callee v.suffix
      verified := .scrubbed (Proof.CmacAes.Stream.X86.Scrub.finish_scrubbed v)
      spSafe := Proof.CmacAes.Stream.X86.Scrub.finish_fnSpSafe v }]

end VG.Artifacts.CmacAes.X86
