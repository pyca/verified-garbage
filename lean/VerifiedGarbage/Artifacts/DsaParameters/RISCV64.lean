module

public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Backend
public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Instances
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
public import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
public import VerifiedGarbage.Proof.Variants.MillerRabin.RISCV64

/-! # DSA parameter generation over refillable tapes on RISC-V, calling each shared Miller–Rabin implementation -/

@[expose] public section

namespace VG.Artifacts.DsaParameters.RISCV64
open VG.Proof.Dsa.RISCV64.PSearch

def artifactsFor (v : Proof.MillerRabin.RISCV64.RoundImpl) : List Artifact := [
  Spec.Dsa.parameterSearchApi.artifact RISCV64.target {
    suffix := v.suffix
    stack := 512
    code := Impl.Dsa.RISCV64.ParameterSearch.code (gen1 v) (gen2 v) (gen3 v)
    verified := params_verified v
    features := v.features }]

def artifacts : List Artifact :=
  VG.Proof.Variants.MillerRabin.RISCV64.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.DsaParameters.RISCV64
