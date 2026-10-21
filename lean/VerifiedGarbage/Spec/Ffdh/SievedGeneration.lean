module

public import VerifiedGarbage.Spec.Ffdh.Generation
public import VerifiedGarbage.Spec.Ffdh.SievedCandidate

/-! # Bounded safe-prime search with RSA's trial-division sieve

Trusted. The original initialization, attempt limit, entropy budget and
refill policy remain in force. `sievedParameterCandidate` determines the
exact accepted value and tape consumption.
-/

@[expose] public section
namespace VG.Spec.Ffdh
open VG.Spec.RsaKeyGen (Rand)

def sievedParameterSearch (bits generator : Nat) : Nat → Rand → ParameterSearchResult
  | 0, _ => .exhausted 0
  | remaining + 1, rand =>
    match sievedParameterCandidate bits generator rand with
    | none =>
      if parameterEntropy bits ≤ rand.length then .exhausted 0
      else .entropy (remaining + 1) (parameterRequest bits rand.length) 0
    | some (some p, rest) => .accepted p (rand.length - rest.length)
    | some (none, rest) =>
      (sievedParameterSearch bits generator remaining rest).consume (rand.length - rest.length)

end VG.Spec.Ffdh
