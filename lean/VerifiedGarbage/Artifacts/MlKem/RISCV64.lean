module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.MlKem.Contract
public import VerifiedGarbage.Spec.MlKem.EncapsH
public import VerifiedGarbage.Spec.MlKem.Contract1024
import VerifiedGarbage.Proof.MlKem.RISCV64.Scrub
import VerifiedGarbage.Proof.MlKem.RISCV64.SampleCT
import VerifiedGarbage.Proof.MlKem.RISCV64.Add
import VerifiedGarbage.Proof.MlKem.RISCV64.Ntt
import VerifiedGarbage.Proof.MlKem.RISCV64.NttInv
import VerifiedGarbage.Proof.MlKem.RISCV64.Mul
import VerifiedGarbage.Proof.MlKem.RISCV64.Cbd2
import VerifiedGarbage.Proof.MlKem.RISCV64.Encode12
import VerifiedGarbage.Proof.MlKem.RISCV64.Decode12
import VerifiedGarbage.Proof.MlKem.RISCV64.CheckEk
import VerifiedGarbage.Proof.MlKem.RISCV64.CompressEncode
import VerifiedGarbage.Proof.MlKem.RISCV64.DecodeDecompress
import VerifiedGarbage.Proof.MlKem.RISCV64.CallWipe
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.MlKem1024.RISCV64.CheckEk
import VerifiedGarbage.Proof.MlKem1024.RISCV64.CompressEncode
import VerifiedGarbage.Proof.MlKem1024.RISCV64.Decompress
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ML-KEM (FIPS 203) on RISC-V -/

namespace VG.Artifacts.MlKem.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.MlKem.keyGenApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.Fn.keyGen
    verified := Proof.MlKem.RISCV64.Scrub.keyGen_scrubbed
    publicOutOk := Proof.MlKem.RISCV64.Scrub.keyGen_public },
  Spec.MlKem.encapsApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.Fn.encaps
    verified := Proof.MlKem.RISCV64.Scrub.encaps_scrubbed
    publicOutOk := Proof.MlKem.RISCV64.Scrub.encaps_public },
  Spec.MlKem.encapsHApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.Fn.encapsH
    verified := Proof.MlKem.RISCV64.Scrub.encapsH_scrubbed
    publicOutOk := Proof.MlKem.RISCV64.Scrub.encapsH_public },
  Spec.MlKem.decapsApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.Fn.decaps
    verified := Proof.MlKem.RISCV64.Scrub.decaps_scrubbed
    publicOutOk := Proof.MlKem.RISCV64.Scrub.decaps_public },
  Spec.MlKem.checkEkApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.Fn.checkEk
    verified := Proof.MlKem.RISCV64.Scrub.checkEk_scrubbed },
  Spec.MlKem1024.checkEkApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.Fn.checkEk1024
    verified := Proof.MlKem.RISCV64.Scrub.checkEk1024_scrubbed },
  Spec.MlKem1024.keyGenApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.Fn.keyGen1024
    verified := Proof.MlKem.RISCV64.Scrub.keyGen1024_scrubbed
    publicOutOk := Proof.MlKem.RISCV64.Scrub.keyGen1024_public },
  Spec.MlKem1024.encapsApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.Fn.encaps1024
    verified := Proof.MlKem.RISCV64.Scrub.encaps1024_scrubbed
    publicOutOk := Proof.MlKem.RISCV64.Scrub.encaps1024_public },
  Spec.MlKem1024.encapsHApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.Fn.encapsH1024
    verified := Proof.MlKem.RISCV64.Scrub.encapsH1024_scrubbed
    publicOutOk := Proof.MlKem.RISCV64.Scrub.encapsH1024_public },
  Spec.MlKem1024.decapsApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.Fn.decaps1024
    verified := Proof.MlKem.RISCV64.Scrub.decaps1024_scrubbed
    publicOutOk := Proof.MlKem.RISCV64.Scrub.decaps1024_public }]

spec_apis artifacts

end VG.Artifacts.MlKem.RISCV64
