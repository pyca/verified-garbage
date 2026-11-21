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
  Spec.MlKem.keyGenApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.Fn.keyGen
    verified := Proof.MlKem.RISCV64.Scrub.keyGen_scrubbed },
  Spec.MlKem.encapsApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.Fn.encaps
    verified := Proof.MlKem.RISCV64.Scrub.encaps_scrubbed },
  Spec.MlKem.encapsHApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.Fn.encapsH
    verified := Proof.MlKem.RISCV64.Scrub.encapsH_scrubbed },
  Spec.MlKem.decapsApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.Fn.decaps
    verified := Proof.MlKem.RISCV64.Scrub.decaps_scrubbed },
  Spec.MlKem.checkEkApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.Fn.checkEk
    verified := Proof.MlKem.RISCV64.Scrub.checkEk_scrubbed },
  Spec.MlKem1024.checkEkApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.Fn.checkEk1024
    verified := Proof.MlKem.RISCV64.Scrub.checkEk1024_scrubbed },
  Spec.MlKem1024.keyGenApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.Fn.keyGen1024
    verified := Proof.MlKem.RISCV64.Scrub.keyGen1024_scrubbed },
  Spec.MlKem1024.encapsApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.Fn.encaps1024
    verified := Proof.MlKem.RISCV64.Scrub.encaps1024_scrubbed },
  Spec.MlKem1024.encapsHApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.Fn.encapsH1024
    verified := Proof.MlKem.RISCV64.Scrub.encapsH1024_scrubbed },
  Spec.MlKem1024.decapsApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.Fn.decaps1024
    verified := Proof.MlKem.RISCV64.Scrub.decaps1024_scrubbed }]

end VG.Artifacts.MlKem.RISCV64
