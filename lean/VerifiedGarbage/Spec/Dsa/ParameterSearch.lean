module

public import VerifiedGarbage.Spec.Entropy
public import VerifiedGarbage.Spec.Dsa.Generate

/-!
# DSA parameter generation over refillable random tapes

**Trusted.** FIPS 186-4 A.1.1.2 and A.2.1 parameter generation over the
protocol of `Spec/Entropy.lean`, in place of `generateParametersBytes`'s three
fixed tapes: verified code counts the seeds it tries and chooses how much
entropy to ask for, and its host only refills one tape.

Each seed is one candidate (`seedCandidate`), reading, in order: the seed
(`qLen` octets), the witnesses of `q`'s test, the witnesses of the tests of
the `p` candidates from that seed (A.1.1.2 step 11, up to `4 L` of them),
and the `h` candidates of A.2.1 (`pLen` octets each, up to
`generatorAttempts`). `q`, `p` and their tests are `qCandidate`,
`pCandidate` and `probablePrime`, unchanged, and the result must pass
`parametersValid`. A seed whose `q` is composite, that yields no `p`, no `g`
within its `h` candidates, or parameters that fail `parametersValid` is
rejected, and the next seed starts where it stopped. A tape that ends inside
a seed asks for more, so the seed is run again from its own octets, whole;
over a stream cut into refilled tapes the search finds what it finds over the
stream in one tape.

Where `generateParametersBytes` reads its seeds, `h` candidates and
witnesses from separate tapes, and starts every generator search at the
front of its `h` tape, this search reads all three from one tape, in the
order a seed uses them. Its limits replace those of the fixed tapes: at most
`parameterSeeds` seeds are rejected, and one seed may read at most
`parameterEntropy` octets (a seed and 32768 draws of `p`'s width) before the
search is exhausted. The parameters are public: the tape may affect the
search's timing, and must never be used for private scalars or nonces.
No primality certificate or Miller–Rabin error bound is asserted.
-/

@[expose] public section

namespace VG.Spec.Dsa

open VG.Spec.RsaKeyGen (Rand)

/-- The subgroup order's octets for each generated modulus width:
(1024, 160), (2048, 256) and (3072, 256). -/
def generationQLen (pLen : Nat) : Nat := if pLen = 128 then 20 else 32

/-- The modulus widths parameter generation supports. -/
def generationPLenValid (pLen : Nat) : Bool := pLen == 128 || pLen == 256 || pLen == 384

/-- The seeds the search may reject: as many as `generateParametersBytes`'s
seed tape held. -/
def parameterSeeds : Nat := 4096

/-- The `h` candidates one seed may draw for its generator (A.2.1): as many
as `generateParametersBytes`'s `h` tape held. -/
def generatorAttempts : Nat := 128

/-- An unfinished seed's budget of entropy: the seed and 32768 draws of the
modulus's width. -/
def parameterEntropy (pLen : Nat) : Nat := 32769 * pLen

/-- The search's first three public words: the seeds it may still reject,
the modulus's width and the entropy budget (the fourth, the first tape's
length, is the code's choice: `parameterInitContract`); `none` for an
unsupported width. -/
def parameterInit (pLen : Nat) : Option (List Nat) :=
  if generationPLenValid pLen then
    some [parameterSeeds, pLen, parameterEntropy pLen]
  else none

/-- A.2.1 over `h` candidates of `pLen` octets drawn from the tape, at most
`fuel` of them: the first `g = h^((p-1)/q) mod p` with `1 < h < p - 1` and
`1 < g`, as `generator` finds over a list. `some (none, rest)` if none of
them gives one; `none` if the tape ran out. -/
def generatorSearch (p q pLen : Nat) : (fuel : Nat) → Rand → Option (Option Nat × Rand)
  | 0, rand => some (none, rand)
  | fuel + 1, rand =>
    if rand.length < pLen then none else
      let h := decodeBE (rand.take pLen)
      let rest := rand.drop pLen
      if 1 < h && h < p - 1 then
        let g := powMod h ((p - 1) / q) p
        if 1 < g then some (some g, rest) else generatorSearch p q pLen fuel rest
      else generatorSearch p q pLen fuel rest

/-- One seed of `qLen` octets, with the `q` it gives, the `p` from it (A.1.1.2)
and a generator (A.2.1), the parameters if they pass `parametersValid`, and
the octets left; `some (none, rest)` if the seed is rejected, `none` if the
tape ran out inside it. -/
def seedCandidate (pLen qLen : Nat) (rand : Rand) : Option (Option Params × Rand) := do
  if rand.length < qLen then none else
  let seed := rand.take qLen
  let n := 8 * qLen
  let q := qCandidate n seed
  let (accepted, rand) ← probablePrime q (rand.drop qLen)
  if !accepted then return (none, rand)
  let (p, rand) ← primeFromSeed (8 * pLen) n q seed rand
  let some p := p | return (none, rand)
  let (g, rand) ← generatorSearch p q pLen generatorAttempts rand
  let some g := g | return (none, rand)
  let a : Params := ⟨p, q, g⟩
  return (if parametersValid a then some a else none, rand)

/-- A parameter search's result: its state across a refill is the seeds it
may still reject, and its result the parameters. -/
abbrev ParameterSearchResult := Entropy.Result Nat Params

/-- The seeds left after a search, or 0 if it ended. -/
def ParameterSearchResult.remaining (r : ParameterSearchResult) : Nat :=
  match r.outcome with
  | .entropy remaining _ => remaining
  | _ => 0

/-- Search the tape's whole seeds for parameters with a modulus of `pLen`
octets, with `remaining` rejected seeds allowed. A rejected seed goes on to
the next in the same call; a tape that ends inside a seed asks for more
(consuming nothing of that seed), unless the seed already had its whole
budget. The trace is empty: the parameters and the tape are public, and the
contract's leakage names the tape itself. -/
def parameterSearch (pLen : Nat) : (remaining : Nat) → Rand → ParameterSearchResult
  | 0, _ => ⟨.exhausted, 0, []⟩
  | remaining + 1, rand =>
    match seedCandidate pLen (generationQLen pLen) rand with
    | none =>
      if parameterEntropy pLen ≤ rand.length then ⟨.exhausted, 0, []⟩
      else ⟨.entropy (remaining + 1) rand.length, 0, []⟩
    | some (some a, rest) => ⟨.accepted a, rand.length - rest.length, []⟩
    | some (none, rest) =>
      (parameterSearch pLen remaining rest).consume (rand.length - rest.length) []

end VG.Spec.Dsa
