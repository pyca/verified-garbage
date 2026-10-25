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
    notes := ["On the Montgomery working space of RSA's functions at `scratch`, in 64-bit words: \
        the check against `p` under masks; `gcd(c − 1, e)` by `(c − 1) mod e` bit by bit, then \
        a binary gcd on words under masks; trial division by the shared table of 32-bit primes \
        and their inverses (Montgomery reduction by 2^64 of the candidate's 64-bit words), \
        which returns at the first divisor; then RSA's witnesses from `rand`, each in \
        Montgomery form for a call of the shared `vg_miller_rabin_round`, whose 176 bytes of \
        frames lie below this function's 224. Branches release only the checks and witness \
        results allowed by the RSA candidate contract."]
    code := Impl.RsaKeyGen.PPC64LE.Candidate.code
      (Impl.RsaKeyGen.PPC64LE.Trial.trial Impl.RsaKeyGen.PPC64LE.Candidate.hTrial) v.name v.code
    stack := 400
    consts := Impl.RsaKeyGen.TrialTable32.consts
    verified := Proof.RsaKeyGen.PPC64LE.Cand.candidate_verified v
    features := v.features }]

end VG.Generic.MillerRabin.PPC64LE.RsaKeyGen
