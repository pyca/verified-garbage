module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ctr.Contract
public import VerifiedGarbage.Spec.Ctr.Final
import VerifiedGarbage.Proof.AesCtr.AArch64.Final
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.AesCtr32.AArch64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-CTR (NIST SP 800-38A §6.5) on AArch64 -/

namespace VG.Artifacts.AesCtr.AArch64

open VG.Proof.AesCtr.AArch64

public def artifacts : List (Artifact AArch64.target) :=
  VG.Proof.Variants.AesCtr32.AArch64.variants.flatMap fun (v : Proof.Aes.AArch64.Ctr32Impl) => [
    Spec.Ctr.aesApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.AesCtr.AArch64.Fn.crypt v.callee
      verified := Proof.AesCtr.AArch64.Final.crypt_scrubbed v },
    Spec.Ctr.aesFinalApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.AesCtr.AArch64.Fn.cryptFinal v.callee v.suffix
      verified := Proof.AesCtr.AArch64.Final.cryptFinal_scrubbed v }]

spec_apis artifacts

end VG.Artifacts.AesCtr.AArch64
