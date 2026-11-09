module

public import VerifiedGarbage.Spec.Ffdh

/-! # Safe-prime generation with an early test of p

Trusted. The original tape policy completes all q rounds before checking p.
This policy first tests p once, completes q's rounds only if that passes,
then completes the remaining p rounds. Accepted pairs still pass exactly
`primeChecks (bitLength p)` and `primeChecks (bitLength q)` independently
sampled witnesses, including the first p witness. No witness is reused.

This obtains early rejection of a composite p, as OpenSSL's alternating
safe-prime tests do, while allowing one prepared q workspace to be reused
across its full batch. The sieved candidate (`SievedCandidate.lean`) draws
its witnesses so.
-/

@[expose] public section
namespace VG.Spec.Ffdh
open VG.Spec.RsaKeyGen (Rand draw bitLength)

/-- One p witness, all q witnesses, then the remaining p witnesses. Shortage
returns none; a composite result returns false and its exact unconsumed suffix.
The early p test counts toward its full policy, so acceptance never reduces
its 64/128-witness requirement. -/
def screenedParameterWitnesses (p q : Nat) (r : Rand) : Option (Bool × Rand) := do
  let (a, r) ← drawWitness p r
  if !mrRound p a then return (false, r)
  let (wq, r) ← drawWitnesses q (primeChecks (bitLength q)) r
  if !probablePrime q wq then return (false, r)
  let (wp, r) ← drawWitnesses p (primeChecks (bitLength p) - 1) r
  return (probablePrime p (a :: wp), r)

end VG.Spec.Ffdh
