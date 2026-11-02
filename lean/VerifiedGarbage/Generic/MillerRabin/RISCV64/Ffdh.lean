module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.Generation.Search.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # FFDH parameter generation calls each shared Miller–Rabin implementation -/

@[expose] public section

namespace VG.Generic.MillerRabin.RISCV64.Ffdh

def artifacts (v : Proof.MillerRabin.RISCV64.RoundImpl) : List Artifact := [
  Spec.Ffdh.parameterSearchApi.artifact RISCV64.target {
    suffix := v.suffix
    stack := 128
    code := Proof.Ffdh.RISCV64.Generation.searchCode v
    verified := Proof.Ffdh.RISCV64.Generation.search_verified v
    features := v.features }]

end VG.Generic.MillerRabin.RISCV64.Ffdh
