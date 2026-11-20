module

public import VerifiedGarbage.Proof.AesOcb.AArch64.Frame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.AesBlocks.AArch64

/-! # AES-OCB (RFC 7253) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.AesOcb.AArch64

open VG.Proof.AesOcb.AArch64

def artifacts : List Artifact :=
  VG.Proof.Variants.AesBlocks.AArch64.variants.flatMap fun (v : Proof.Aes.AArch64.BlocksImpl) => [
    Spec.Ocb.initApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.AesOcb.AArch64.Fn.init ⟨v.enc, v.dec, v.expand⟩
      verified := .scrubbed (init_scrubbed v) },
    Spec.Ocb.sealApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.AesOcb.AArch64.Fn.seal ⟨v.enc, v.dec, v.expand⟩
      verified := .scrubbed (seal_scrubbed v) },
    Spec.Ocb.openApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.AesOcb.AArch64.Fn.open ⟨v.enc, v.dec, v.expand⟩
      verified := .scrubbed (open_scrubbed v) }]

end VG.Artifacts.AesOcb.AArch64
