module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterBackend
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
public import VerifiedGarbage.Spec.Ffdh.GenerationContract
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Verified
public import VerifiedGarbage.Spec.Ffdh.ScreenedContract

/-! Emit complete native FFDH parameter generation for every shared ARMv7 Miller–Rabin backend. -/

@[expose] public section
namespace VG.Generic.MillerRabin.Arm.Ffdh
open VG

def artifacts (v : Proof.MillerRabin.Arm.RoundImpl) : List Artifact :=
  let b := Proof.Ffdh.Arm.parameterBackend v
  [Spec.Ffdh.screenedParameterCandidateApi.artifact VG.Arm.target {
    suffix := b.suffix
    features := b.features
    stack := 184
    code := b.candidate
    verified := b.candidate_verified
    notes := ["ARMv7: candidate shaping, generator congruences, the shared RSA small-prime \
      sieve, q/p preparation, witness rejection sampling and entropy accounting run in \
      verified code. Both primality tests call the selected shared RSA four-bit-window \
      Miller–Rabin round. Caller arithmetic uses the same baseline or UMAAL variant."] },
   Spec.Ffdh.screenedParameterSearchApi.artifact VG.Arm.target {
    suffix := b.suffix
    features := b.features
    stack := 232
    code := Impl.Ffdh.Arm.ParameterSearch.code (.call b.candidateName b.candidate)
    verified := Proof.Ffdh.Arm.ParameterSearch.verified b
    notes := ["ARMv7: the whole safe-prime search runs in verified code, including the \
      full u64 attempt counter, candidate retries, exact entropy consumption, bounded \
      refill requests, exhaustion and output clearing. Rust allocates buffers and \
      supplies entropy. The public contract discloses the tape and first four controller \
      words; the remaining controller workspace and scratch contents need not agree."] }]

end VG.Generic.MillerRabin.Arm.Ffdh
