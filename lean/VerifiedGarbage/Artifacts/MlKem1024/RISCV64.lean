module

public import VerifiedGarbage.Proof.MlKem1024.RISCV64.CheckEk
public import VerifiedGarbage.Proof.MlKem1024.RISCV64.KeyGenCT
public import VerifiedGarbage.Proof.MlKem1024.RISCV64.EncapsCT
public import VerifiedGarbage.Proof.MlKem1024.RISCV64.DecapsCT
public import VerifiedGarbage.Proof.MlKem1024.RISCV64.CompressEncode
public import VerifiedGarbage.Proof.MlKem1024.RISCV64.Decompress
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-KEM-1024 (FIPS 203) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.MlKem1024.RISCV64

def artifacts : List Artifact := [
  Spec.MlKem1024.compressEncodeApi.artifact RISCV64.target {
    code := Impl.MlKem1024.RISCV64.compressEncode1024
    verified := Proof.MlKem1024.RISCV64.CompressEncode.verified },
  Spec.MlKem1024.decodeDecompressApi.artifact RISCV64.target {
    code := Impl.MlKem1024.RISCV64.decodeDecompress1024
    verified := Proof.MlKem1024.RISCV64.Decompress.verified },
  Spec.MlKem1024.checkEkApi.artifact RISCV64.target {
    code := Impl.MlKem1024.RISCV64.checkEk1024
    verified := Proof.MlKem1024.RISCV64.CheckEk.verified },
  Spec.MlKem1024.keyGenApi.artifact RISCV64.target {
    code := Impl.MlKem1024.RISCV64.keygen1024
    stack := 1168
    verified := Proof.MlKem1024.RISCV64.KeyGen.verified },
  Spec.MlKem1024.encapsApi.artifact RISCV64.target {
    code := Impl.MlKem1024.RISCV64.encaps1024
    stack := 1168
    verified := Proof.MlKem1024.RISCV64.Encaps.verified },
  Spec.MlKem1024.decapsApi.artifact RISCV64.target {
    code := Impl.MlKem1024.RISCV64.decaps1024
    stack := 1168
    verified := Proof.MlKem1024.RISCV64.Decaps.verified }]

end VG.Artifacts.MlKem1024.RISCV64
