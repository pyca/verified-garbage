module

public import VerifiedGarbage.Proof.MlKem1024.RISCV64.CheckEk
public import VerifiedGarbage.Proof.MlKem.RISCV64.CallWipe
public import VerifiedGarbage.Proof.MlKem1024.RISCV64.CompressEncode
public import VerifiedGarbage.Proof.MlKem1024.RISCV64.Decompress
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # ML-KEM-1024 (FIPS 203) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.MlKem1024.RISCV64

def artifacts : List Artifact := [
  Spec.MlKem1024.checkEkApi.artifact RISCV64.target {
    code := Impl.MlKem1024.RISCV64.checkEk1024
    verified := Proof.MlKem1024.RISCV64.CheckEk.verified },
  Spec.MlKem1024.keyGenApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.Wipe.keyGen1024
    stack := 1200
    verified := Proof.MlKem.RISCV64.Wipe.keyGen1024_verified },
  Spec.MlKem1024.encapsApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.Wipe.encaps1024
    stack := 1200
    verified := Proof.MlKem.RISCV64.Wipe.encaps1024_verified },
  Spec.MlKem1024.encapsHApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.Wipe.encapsH1024
    stack := 1200
    verified := Proof.MlKem.RISCV64.Wipe.encapsH1024_verified },
  Spec.MlKem1024.decapsApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.Wipe.decaps1024
    stack := 1200
    verified := Proof.MlKem.RISCV64.Wipe.decaps1024_verified }]

end VG.Artifacts.MlKem1024.RISCV64
