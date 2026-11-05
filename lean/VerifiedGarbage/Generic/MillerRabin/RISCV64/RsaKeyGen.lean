module

public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Backend
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.Instances
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
public import VerifiedGarbage.Spec.RsaKeyGen.Contract
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Search.Verified

/-! # The RSA prime search on RISC-V, its candidates calling each shared Miller–Rabin implementation -/

@[expose] public section

namespace VG.Generic.MillerRabin.RISCV64.RsaKeyGen

def artifacts (v : Proof.MillerRabin.RISCV64.RoundImpl) : List Artifact := [
  Spec.RsaKeyGen.primeSearchApi.artifact RISCV64.target {
    suffix := v.suffix
    stack := 496
    consts := Impl.RsaKeyGen.TrialTable32.consts
    code := Proof.RsaKeyGen.RISCV64.Search.searchCode v
    verified := Proof.RsaKeyGen.RISCV64.Search.search_verified v
    features := v.features }]

end VG.Generic.MillerRabin.RISCV64.RsaKeyGen
