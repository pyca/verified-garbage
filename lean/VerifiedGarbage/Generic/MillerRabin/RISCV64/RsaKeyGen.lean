module

public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Backend
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.Instances
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
public import VerifiedGarbage.Spec.RsaKeyGen.Contract
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Search.Verified

/-! # RSA candidates on RISC-V call each shared Miller–Rabin implementation -/

@[expose] public section

namespace VG.Generic.MillerRabin.RISCV64.RsaKeyGen

def artifacts (v : Proof.MillerRabin.RISCV64.RoundImpl) : List Artifact := [
  Spec.RsaKeyGen.candidateApi.artifact RISCV64.target {
    suffix := v.suffix
    code := Impl.RsaKeyGen.RISCV64.Candidate.code
      (Impl.RsaKeyGen.RISCV64.Trial.trial Impl.RsaKeyGen.RISCV64.Candidate.hTrial) v.name v.code
    stack := 288
    consts := Impl.RsaKeyGen.TrialTable32.consts
    verified := Proof.RsaKeyGen.RISCV64.Cand.candidate_verified v
    features := v.features },
  Spec.RsaKeyGen.primeSearchApi.artifact RISCV64.target {
    suffix := v.suffix
    stack := 496
    consts := Impl.RsaKeyGen.TrialTable32.consts
    code := Proof.RsaKeyGen.RISCV64.Search.searchCode v
    verified := Proof.RsaKeyGen.RISCV64.Search.search_verified v
    features := v.features }]

end VG.Generic.MillerRabin.RISCV64.RsaKeyGen
