module

public import VerifiedGarbage.Proof.CmacAes.AArch64.Aese
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.CmacAes.AArch64
def artifacts : List Artifact := [
  Spec.Cmac.aesUpdateApi.artifact AArch64.target {
    suffix := "_aes_cbc"
    notes := [
      "The round keys and chaining value stay in vector registers across all blocks. \
      The first and last round keys are folded into the input, and the round count is selected once. \
      No stack or scratch space is used."]
    code := Impl.CmacAes.AArch64.Aese.update
    verified := Proof.CmacAes.AArch64.Aese.verified
    features := ["aes"] }]
end VG.Artifacts.CmacAes.AArch64
