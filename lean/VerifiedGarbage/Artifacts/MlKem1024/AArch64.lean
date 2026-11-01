module

public import VerifiedGarbage.Proof.MlKem1024.AArch64.CompressEncode
public import VerifiedGarbage.Proof.MlKem1024.AArch64.DecodeDecompress
public import VerifiedGarbage.Proof.MlKem1024.AArch64.CheckEk
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-KEM-1024 on AArch64 -/

@[expose] public section

namespace VG.Artifacts.MlKem1024.AArch64

def artifacts : List Artifact := [
  Spec.MlKem1024.checkEkApi.artifact AArch64.target {
    code := Impl.MlKem1024.AArch64.checkEk
    verified := Proof.MlKem1024.AArch64.CheckEk.checkEk_verified }]

end VG.Artifacts.MlKem1024.AArch64
