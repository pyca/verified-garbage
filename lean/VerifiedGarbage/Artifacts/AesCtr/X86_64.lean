module

public import VerifiedGarbage.Impl.AesCtr.X86_64.Fn
public import VerifiedGarbage.Proof.AesCtr.X86_64.Verified
public import VerifiedGarbage.Proof.AesCtr.X86_64.Final
public import VerifiedGarbage.Proof.Aes.X86_64.FinalScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.Variants.AesCtr32.X86_64

/-! # AES-CTR (NIST SP 800-38A §6.5) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.AesCtr.X86_64

def artifacts : List Artifact :=
  VG.Proof.Variants.AesCtr32.X86_64.variants.flatMap fun (v : Proof.Aes.X86_64.Ctr32Impl) => [
    Spec.Ctr.aesApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.AesCtr.X86_64.Fn.ctr v.level v.callee
      verified := .scrubbed (Proof.Aes.X86_64.FinalScrub.ctr_scrubbed v)
      spSafe := Proof.Aes.X86_64.FinalScrub.ctr_spSafeFn v },
    Spec.Ctr.aesFinalApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.AesCtr.X86_64.Fn.ctrFinal v.level v.callee v.suffix
      verified := .scrubbed (Proof.Aes.X86_64.FinalScrub.ctrFinal_scrubbed v)
      spSafe := Proof.Aes.X86_64.FinalScrub.ctrFinal_spSafeFn v }]

end VG.Artifacts.AesCtr.X86_64
