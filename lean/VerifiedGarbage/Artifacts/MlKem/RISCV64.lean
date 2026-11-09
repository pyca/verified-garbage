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
public import VerifiedGarbage.Proof.MlKem.RISCV64.CallWipe
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # ML-KEM (FIPS 203) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.MlKem.RISCV64

def artifacts : List Artifact := [
  Spec.MlKem.keyGenApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.Wipe.keyGen
    stack := 1200
    verified := Proof.MlKem.RISCV64.Wipe.keyGen_verified },
  Spec.MlKem.encapsApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.Wipe.encaps
    stack := 1200
    verified := Proof.MlKem.RISCV64.Wipe.encaps_verified },
  Spec.MlKem.encapsHApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.Wipe.encapsH
    stack := 1200
    verified := Proof.MlKem.RISCV64.Wipe.encapsH_verified },
  Spec.MlKem.decapsApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.Wipe.decaps
    stack := 1200
    verified := Proof.MlKem.RISCV64.Wipe.decaps_verified },
  Spec.MlKem.checkEkApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.checkEk
    verified := Proof.MlKem.RISCV64.CheckEk.verified }]

end VG.Artifacts.MlKem.RISCV64
