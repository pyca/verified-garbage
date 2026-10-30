module

public import VerifiedGarbage.Proof.CmacAes.AArch64.Aese
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.CmacAes.AArch64
def artifacts : List Artifact := [
  Spec.Cmac.aesUpdateApi.artifact AArch64.target {
    suffix := "_aes_cbc"
    code := Impl.CmacAes.AArch64.Aese.update
    verified := Proof.CmacAes.AArch64.Aese.verified
    features := ["aes"] }]
end VG.Artifacts.CmacAes.AArch64
