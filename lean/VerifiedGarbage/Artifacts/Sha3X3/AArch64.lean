module

public import VerifiedGarbage.Proof.Sha3.AArch64.Hybrid.X3
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Keccak-f[1600] on three states on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Sha3X3.AArch64

def artifacts : List Artifact := [
  Spec.Sha3.permuteX3Api.artifact AArch64.target {
    suffix := "_sha3"
    features := ["sha3"]
    stack := 128
    code := Impl.Sha3.AArch64.Hybrid.X3.code
    verified := Proof.Sha3.AArch64.Hybrid.X3.verified }]

end VG.Artifacts.Sha3X3.AArch64
