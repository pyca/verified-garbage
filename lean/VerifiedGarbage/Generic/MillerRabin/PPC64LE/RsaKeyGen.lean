module

public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Backend
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Instances
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
public import VerifiedGarbage.Spec.RsaKeyGen.Contract
public import VerifiedGarbage.Proof.Framework.Registration

/-! # RSA candidates on PPC64LE call each shared Miller–Rabin implementation -/

@[expose] public section

namespace VG.Generic.MillerRabin.PPC64LE.RsaKeyGen

def artifacts (v : Proof.MillerRabin.PPC64LE.RoundImpl) : List Artifact := [
  Spec.RsaKeyGen.candidateApi.artifact PPC64LE.target {
    suffix := v.suffix
    code := Impl.RsaKeyGen.PPC64LE.Candidate.code
      (Impl.RsaKeyGen.PPC64LE.Trial.trial Impl.RsaKeyGen.PPC64LE.Candidate.hTrial) v.name v.code
    stack := 400
    consts := Impl.RsaKeyGen.TrialTable32.consts
    verified := Proof.RsaKeyGen.PPC64LE.Cand.candidate_verified v
    features := v.features }]

end VG.Generic.MillerRabin.PPC64LE.RsaKeyGen
