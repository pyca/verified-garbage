module

public import VerifiedGarbage.Spec.RsaKeyGen.Contract

/-!
# RSA prime generation over refillable entropy tapes

**Trusted.** This is an additive controller specification, not a replacement
for `generatePrime` or its existing implementation. It uses `candidateOp`
unchanged: candidate bits, distance rejection, sieving, the gcd check,
Miller–Rabin rounds and blinded witness selection retain their meaning.

As in FFDH parameter generation, verified code owns the rejection budget
and the entropy request. The host discards `used` bytes and extends the
unconsumed suffix, never replacing an unfinished candidate's prefix. Only
an unfinished candidate is replayed; completed candidates are not.

There is one deliberate additional failure condition: an unfinished
candidate may use at most `primeEntropy` bytes. This is an allocation and
termination bound, not a change to the primality-test round policy and not
a claim about its error probability. Reaching that bound fails generation;
it never accepts a candidate with fewer witnesses. Distance rejections
still do not count against `primeLimit`.

The random tape and the other prime remain secret. The trace composes
length-framed `candidateLeak` entries, retaining the distinction between ordinary
rejections, distance rejections and acceptance. It never declassifies the
whole tape, unlike public domain-parameter generation.
-/

@[expose] public section

namespace VG.Spec.RsaKeyGen

/-- At most 32768 prime-width witness draws after the candidate. This is a
resource bound, independent of the number of uniform witnesses required. -/
def primeEntropy (pLen : Nat) : Nat := 32769 * pLen

/-- Enough space initially for a candidate and 31 witness draws. Doubling
an incomplete candidate's tape amortizes replay; the cap never truncates a
successful primality test into an acceptance. -/
def primeRequest (pLen available : Nat) : Nat :=
  min (2 * max available (16 * pLen)) (primeEntropy pLen)

/-- Four public controller words: remaining counted candidates, prime
width, maximum tape length, and next entropy request. Numeric exponent
validation is intentionally the existing standalone prime API's policy:
the encoding is 1..=8 bytes; only full key generation requires an odd
32-bit exponent. Leading-zero encodings of 3 select the larger budget. -/
def primeInit (pLen : Nat) (eB : List Byte) : Option (List Nat) :=
  if 32 ≤ pLen && pLen ≤ 512 && pLen % 8 == 0 && 1 ≤ eB.length && eB.length ≤ 8 then
    some [primeLimit (8 * pLen) (Rsa.os2ip eB), pLen, primeEntropy pLen,
      primeRequest pLen 0]
  else none

inductive PrimeSearchResult where
  | entropy (remaining requested used : Nat) (trace : List Nat)
  | accepted (prime used : Nat) (trace : List Nat)
  | exhausted (used : Nat) (trace : List Nat)
  deriving DecidableEq, Repr

def PrimeSearchResult.used : PrimeSearchResult → Nat
  | .entropy _ _ used _ | .accepted _ used _ | .exhausted used _ => used

def PrimeSearchResult.status : PrimeSearchResult → Nat
  | .entropy .. => 0
  | .accepted .. => 1
  | .exhausted .. => 3

def PrimeSearchResult.remaining : PrimeSearchResult → Nat
  | .entropy remaining _ _ _ => remaining
  | _ => 0

def PrimeSearchResult.requested : PrimeSearchResult → Nat
  | .entropy _ requested _ _ => requested
  | _ => 0

def PrimeSearchResult.trace : PrimeSearchResult → List Nat
  | .entropy _ _ _ trace | .accepted _ _ trace | .exhausted _ trace => trace

/-- Add only completed candidates' consumption and permitted leakage. -/
def PrimeSearchResult.consume (n : Nat) (prior : List Nat) :
    PrimeSearchResult → PrimeSearchResult
  | .entropy remaining requested used trace =>
      .entropy remaining requested (n + used) (prior ++ trace)
  | .accepted prime used trace => .accepted prime (n + used) (prior ++ trace)
  | .exhausted used trace => .exhausted (n + used) (prior ++ trace)

/-- Search complete candidates internally, returning to the host only for
entropy or a terminal result. An incomplete candidate consumes no bytes
and no counted attempt. A request at the entropy cap fails closed.
The progress check agrees with the existing `loop` specification; valid
prime widths ensure that every completed candidate consumes bytes. -/
def primeSearch (pLen : Nat) (eB pB : List Byte) (remaining : Nat) (rand : Rand) :
    PrimeSearchResult :=
  if remaining = 0 then .exhausted 0 [] else
    let entry := candidateLeak pLen eB pB rand
    let trace := entry.length :: entry
    match candidateOp pLen eB pB rand with
    | none =>
      if primeEntropy pLen ≤ rand.length then .exhausted 0 trace
      else .entropy remaining (primeRequest pLen rand.length) 0 trace
    | some (.prime c, rest) => .accepted c (rand.length - rest.length) trace
    | some (.close, rest) =>
      if _h : rest.length < rand.length then
        (primeSearch pLen eB pB remaining rest).consume (rand.length - rest.length) trace
      else .exhausted 0 trace
    | some (.rejected, rest) =>
      if _h : rest.length < rand.length then
        (primeSearch pLen eB pB (remaining - 1) rest).consume (rand.length - rest.length) trace
      else .exhausted 0 trace
termination_by rand.length
decreasing_by all_goals exact _h

end VG.Spec.RsaKeyGen
