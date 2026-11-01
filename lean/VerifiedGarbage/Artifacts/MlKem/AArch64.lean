module

public import VerifiedGarbage.Proof.MlKem.AArch64.CheckEk
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Inv
public import VerifiedGarbage.Proof.MlKem.AArch64.AddSub
public import VerifiedGarbage.Proof.MlKem.AArch64.Cbd2
public import VerifiedGarbage.Proof.MlKem.AArch64.CompressEncode
public import VerifiedGarbage.Proof.MlKem.AArch64.Decode12
public import VerifiedGarbage.Proof.MlKem.AArch64.DecodeDecompress
public import VerifiedGarbage.Proof.MlKem.AArch64.Encode12
public import VerifiedGarbage.Proof.MlKem.AArch64.Mul
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Fwd
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-KEM on AArch64 -/

@[expose] public section

namespace VG.Artifacts.MlKem.AArch64

def artifacts : List Artifact := [
  Spec.MlKem.checkEkApi.artifact AArch64.target {
    code := Impl.MlKem.AArch64.checkEk
    verified := Proof.MlKem.AArch64.CheckEk.checkEk_verified }]

end VG.Artifacts.MlKem.AArch64
