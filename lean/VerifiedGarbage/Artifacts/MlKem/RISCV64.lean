module

public import VerifiedGarbage.Proof.MlKem.RISCV64.Scrub
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
public import VerifiedGarbage.Proof.MlKem1024.RISCV64.CheckEk
public import VerifiedGarbage.Proof.MlKem1024.RISCV64.CompressEncode
public import VerifiedGarbage.Proof.MlKem1024.RISCV64.Decompress

/-! # ML-KEM (FIPS 203) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.MlKem.RISCV64

def artifacts : List Artifact := [
  Spec.MlKem.keyGenApi.artifact RISCV64.target Proof.MlKem.RISCV64.Scrub.keyGenReg,
  Spec.MlKem.encapsApi.artifact RISCV64.target Proof.MlKem.RISCV64.Scrub.encapsReg,
  Spec.MlKem.encapsHApi.artifact RISCV64.target Proof.MlKem.RISCV64.Scrub.encapsHReg,
  Spec.MlKem.decapsApi.artifact RISCV64.target Proof.MlKem.RISCV64.Scrub.decapsReg,
  Spec.MlKem.checkEkApi.artifact RISCV64.target Proof.MlKem.RISCV64.Scrub.checkEkReg,
  Spec.MlKem1024.checkEkApi.artifact RISCV64.target Proof.MlKem.RISCV64.Scrub.checkEk1024Reg,
  Spec.MlKem1024.keyGenApi.artifact RISCV64.target Proof.MlKem.RISCV64.Scrub.keyGen1024Reg,
  Spec.MlKem1024.encapsApi.artifact RISCV64.target Proof.MlKem.RISCV64.Scrub.encaps1024Reg,
  Spec.MlKem1024.encapsHApi.artifact RISCV64.target Proof.MlKem.RISCV64.Scrub.encapsH1024Reg,
  Spec.MlKem1024.decapsApi.artifact RISCV64.target Proof.MlKem.RISCV64.Scrub.decaps1024Reg]

end VG.Artifacts.MlKem.RISCV64
