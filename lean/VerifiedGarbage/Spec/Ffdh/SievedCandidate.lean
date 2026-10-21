module

public import VerifiedGarbage.Spec.Ffdh.ScreenedCandidate

/-! # Safe-prime generation with RSA's larger trial-division policy

Trusted. Keep the original candidate shaping, generator congruences and
64/128 independent Miller–Rabin witnesses, including the early p screen.
Before drawing witnesses, also screen p and q with RSA's trial-division
policy: the first 512 primes through 1024 bits, and 1024 primes above that.
The public requested p width selects one trial bound for both p and q.

Extra deterministic rejections consume no witnesses, so this defines a new
exact tape policy instead of changing an existing candidate's semantics.
-/

@[expose] public section
namespace VG.Spec.Ffdh
open VG.Spec.RsaKeyGen (Rand draw obviouslyComposite)

/-- Stronger trial division with the original early-p witness policy. -/
def sievedParameterCandidate (bits generator : Nat) (r : Rand) : Option (Option Nat × Rand) := do
  let (x, r) ← draw ((bits + 7) / 8) r
  let p := candidateOf bits x
  let q := (p - 1) / 2
  if !(generationShape bits generator p && primeShape p && primeShape q &&
      !obviouslyComposite bits p && !obviouslyComposite bits q) then
    return (none, r)
  let (pass, r) ← screenedParameterWitnesses p q r
  return (if pass then some p else none, r)

end VG.Spec.Ffdh
