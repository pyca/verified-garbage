module

public import VerifiedGarbage.Proof.AesCtr.AArch64.Final
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.AesCtr32.AArch64

/-! # AES-CTR (NIST SP 800-38A §6.5) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.AesCtr.AArch64

open VG.Proof.AesCtr.AArch64

def artifacts : List Artifact :=
  VG.Proof.Variants.AesCtr32.AArch64.variants.flatMap fun (v : Proof.Aes.AArch64.Ctr32Impl) => [
    Spec.Ctr.aesApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.AesCtr.AArch64.Fn.crypt v.callee
      verified := .scrubbed (Final.crypt_scrubbed v) },
    Spec.Ctr.aesFinalApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.AesCtr.AArch64.Fn.cryptFinal v.callee v.suffix
      verified := .scrubbed (Final.cryptFinal_scrubbed v) }]

end VG.Artifacts.AesCtr.AArch64
