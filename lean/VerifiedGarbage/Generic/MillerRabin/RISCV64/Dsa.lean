module

public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Backend
public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Instances
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
public import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
public import VerifiedGarbage.Proof.Framework.Registration

/-! # DSA parameter generation over refillable tapes on RISC-V, calling each shared Miller–Rabin implementation -/

@[expose] public section

namespace VG.Generic.MillerRabin.RISCV64.Dsa
open VG.Proof.Dsa.RISCV64.PSearch

def artifacts (v : Proof.MillerRabin.RISCV64.RoundImpl) : List Artifact := [
  Spec.Dsa.parameterSearchApi.artifact RISCV64.target {
    suffix := v.suffix
    stack := 512
    consts := Impl.RsaKeyGen.TrialTable32.consts
    code := Impl.Dsa.RISCV64.ParameterSearch.code (gen1 v) (gen2 v) (gen3 v)
    verified := params_verified v
    features := v.features }]

end VG.Generic.MillerRabin.RISCV64.Dsa
