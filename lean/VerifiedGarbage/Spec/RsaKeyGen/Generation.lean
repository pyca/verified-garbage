module

public import VerifiedGarbage.Spec.Entropy
public import VerifiedGarbage.Spec.RsaKeyGen.Contract

/-!
# RSA prime search over refillable random tapes

**Trusted.** A search for one prime of an RSA key, over the protocol of
`Spec/Entropy.lean`: verified code, rather than its host, counts rejected
candidates against `primeLimit` and chooses how much entropy to ask for.
It tests each candidate with `candidateOp`, unchanged: the candidate's bits,
the distance check against the other prime, trial division, the gcd check and
Miller–Rabin with its blinded witnesses keep their meaning, and candidates too
close to the other prime still do not count as attempts.

The search is `generatePrime` on the stream of octets the host hands out,
cut into refilled tapes (`GenerationAgrees.lean` states and proves it,
`primeSearch_agrees`): only an unfinished candidate is ever run again, from
its own octets.

It adds one way to fail: an unfinished candidate may use at most
`primeEntropy` octets (a candidate and 32768 witness draws). This bounds the
memory a refill takes and the search's running time; it does not change how
many witnesses the primality test needs, and the search never accepts a
candidate with fewer. Reaching the bound exhausts the search.

The tape and the other prime are secret. The trace is the `candidateLeak` of
each candidate, each after its length (a rejected candidate's entry has the
octets it read, so the entries vary in length): which candidates were rejected,
too close or accepted, and how much the accepted one read.
-/

@[expose] public section

namespace VG.Spec.RsaKeyGen

/-- An unfinished candidate's budget of entropy: the candidate and 32768
witness draws, each of the prime's width. -/
def primeEntropy (pLen : Nat) : Nat := 32769 * pLen

/-- The next tape's length when `available` octets did not hold a whole
candidate (`Entropy.request`): at first `32 * pLen`, a candidate and 31
witness draws. -/
def primeRequest (pLen available : Nat) : Nat :=
  Entropy.request (16 * pLen) (primeEntropy pLen) available

/-- The search's four public words: the counted candidates left, the prime's
width, the entropy budget and the first tape's length. `vg_rsa_keygen_candidate`'s
checks of the width and of the exponent's length: only full key generation
requires an odd 32-bit exponent. An exponent of 3 (with any leading zeros)
allows more candidates (`primeLimit`). -/
def primeInit (pLen : Nat) (eB : List Byte) : Option (List Nat) :=
  if 32 ≤ pLen && pLen ≤ 512 && pLen % 8 == 0 && 1 ≤ eB.length && eB.length ≤ 8 then
    some [primeLimit (8 * pLen) (Rsa.os2ip eB), pLen, primeEntropy pLen,
      primeRequest pLen 0]
  else none

/-- A prime search's result: its state across a refill is the counted
candidates left, and its result the prime. -/
abbrev PrimeSearchResult := Entropy.Result Nat Nat

/-- The counted candidates left after a search, or 0 if it ended. -/
def PrimeSearchResult.remaining (r : PrimeSearchResult) : Nat :=
  match r.outcome with
  | .entropy remaining _ => remaining
  | _ => 0

/-- Search the tape's whole candidates for a prime of `pLen` octets, with
the public exponent `eB`, not too close to the prime `pB` (none if empty),
with `remaining` rejected candidates allowed. A rejected or too close
candidate goes on to the next in the same call; a tape that ends inside a
candidate asks for more (consuming nothing of that candidate, and counting no
attempt for it), unless the candidate already had its whole budget. -/
def primeSearch (pLen : Nat) (eB pB : List Byte) (remaining : Nat) (rand : Rand) :
    PrimeSearchResult :=
  if remaining = 0 then ⟨.exhausted, 0, []⟩ else
    let entry := candidateLeak pLen eB pB rand
    let trace := entry.length :: entry
    match candidateOp pLen eB pB rand with
    | none =>
      if primeEntropy pLen ≤ rand.length then ⟨.exhausted, 0, trace⟩
      else ⟨.entropy remaining (primeRequest pLen rand.length), 0, trace⟩
    | some (.prime c, rest) => ⟨.accepted c, rand.length - rest.length, trace⟩
    | some (.close, rest) =>
      -- Every candidate reads its `pLen` octets, at least 32.
      if _h : rest.length < rand.length then
        (primeSearch pLen eB pB remaining rest).consume (rand.length - rest.length) trace
      else ⟨.exhausted, 0, trace⟩
    | some (.rejected, rest) =>
      if _h : rest.length < rand.length then
        (primeSearch pLen eB pB (remaining - 1) rest).consume (rand.length - rest.length) trace
      else ⟨.exhausted, 0, trace⟩
termination_by rand.length
decreasing_by all_goals exact _h

end VG.Spec.RsaKeyGen
