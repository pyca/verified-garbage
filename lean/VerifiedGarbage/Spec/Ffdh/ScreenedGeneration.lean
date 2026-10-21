module

public import VerifiedGarbage.Spec.Ffdh.Generation
public import VerifiedGarbage.Spec.Ffdh.ScreenedCandidate

/-! # Bounded safe-prime search with early p screening

Trusted. Uses the existing attempt, entropy, refill and output policies, with
`screenedParameterCandidate` defining the exact tape consumption. Initialization
is the existing `parameterInit`; the controller's four public words are unchanged.
-/

@[expose] public section
namespace VG.Spec.Ffdh
open VG.Spec.RsaKeyGen (Rand)

def screenedParameterSearch (bits generator : Nat) : Nat → Rand → ParameterSearchResult
  | 0, _ => .exhausted 0
  | remaining + 1, rand =>
    match screenedParameterCandidate bits generator rand with
    | none =>
      if parameterEntropy bits ≤ rand.length then .exhausted 0
      else .entropy (remaining + 1) (parameterRequest bits rand.length) 0
    | some (some p, rest) => .accepted p (rand.length - rest.length)
    | some (none, rest) =>
      (screenedParameterSearch bits generator remaining rest).consume (rand.length - rest.length)

end VG.Spec.Ffdh
