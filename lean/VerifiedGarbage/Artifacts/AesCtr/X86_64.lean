module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ctr.Contract
public import VerifiedGarbage.Spec.Ctr.Final
import VerifiedGarbage.Impl.AesCtr.X86_64.Fn
import VerifiedGarbage.Proof.AesCtr.X86_64.Verified
import VerifiedGarbage.Proof.AesCtr.X86_64.Final
import VerifiedGarbage.Proof.Aes.X86_64.FinalScrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.AesCtr32.X86_64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-CTR (NIST SP 800-38A §6.5) on x86-64 -/

namespace VG.Artifacts.AesCtr.X86_64

public def artifacts : List (Artifact X86_64.target) :=
  VG.Proof.Variants.AesCtr32.X86_64.variants.flatMap fun (v : Proof.Aes.X86_64.Ctr32Impl) => [
    Spec.Ctr.aesApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.AesCtr.X86_64.Fn.ctr v.level v.callee
      verified := Proof.Aes.X86_64.FinalScrub.ctr_scrubbed v
      spSafe := Proof.Aes.X86_64.FinalScrub.ctr_spSafeFn v },
    Spec.Ctr.aesFinalApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.AesCtr.X86_64.Fn.ctrFinal v.level v.callee v.suffix
      verified := Proof.Aes.X86_64.FinalScrub.ctrFinal_scrubbed v
      spSafe := Proof.Aes.X86_64.FinalScrub.ctrFinal_spSafeFn v }]

spec_apis artifacts

end VG.Artifacts.AesCtr.X86_64
