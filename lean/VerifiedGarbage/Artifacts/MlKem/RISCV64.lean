module

public import VerifiedGarbage.Proof.MlKem.RISCV64.SampleCT
public import VerifiedGarbage.Proof.MlKem.RISCV64.Add
public import VerifiedGarbage.Proof.MlKem.RISCV64.Ntt
public import VerifiedGarbage.Proof.MlKem.RISCV64.NttInv
public import VerifiedGarbage.Proof.MlKem.RISCV64.Mul
public import VerifiedGarbage.Proof.MlKem.RISCV64.Cbd2
public import VerifiedGarbage.Proof.MlKem.RISCV64.Encode12
public import VerifiedGarbage.Proof.MlKem.RISCV64.Decode12
public import VerifiedGarbage.Proof.MlKem.RISCV64.CheckEk
public import VerifiedGarbage.Proof.MlKem.RISCV64.CompressEncode
public import VerifiedGarbage.Proof.MlKem.RISCV64.DecodeDecompress
public import VerifiedGarbage.Proof.MlKem.RISCV64.KeyGenCT
public import VerifiedGarbage.Proof.MlKem.RISCV64.EncapsCT
public import VerifiedGarbage.Proof.MlKem.RISCV64.DecapsCT
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-KEM (FIPS 203) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.MlKem.RISCV64

def artifacts : List Artifact := [
  Spec.MlKem.keyGenApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.keygen
    stack := 1168
    verified := Proof.MlKem.RISCV64.KeyGen.verified },
  Spec.MlKem.encapsApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.encaps
    stack := 1168
    verified := Proof.MlKem.RISCV64.Encaps.verified },
  Spec.MlKem.decapsApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.decaps
    stack := 1168
    verified := Proof.MlKem.RISCV64.Decaps.verified },
  Spec.MlKem.checkEkApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.checkEk
    verified := Proof.MlKem.RISCV64.CheckEk.verified }]

end VG.Artifacts.MlKem.RISCV64
