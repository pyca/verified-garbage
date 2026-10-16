module

public import VerifiedGarbage.Spec.Dsa

/-!
# DSA scalar sampling from random octets (trusted)

FIPS 186-4 B.1.2/B.2.2 rejection sampling. Each draw consumes ceil(N/8)
bytes and discards the excess high bits, where N is the actual bit length
of q, not its padded encoding width. No reduction modulo q is performed.
Independent uniform input octets give uniform N-bit candidates; uniformity
of accepted scalars is a probabilistic obligation, not a theorem here.

The finite tape is consumed in order. A partial final draw is not consumed.
Only acceptance/rejection and exhaustion are declassified, never candidate
values. The wrapper must supply fresh independent randomness for each call.
-/

@[expose] public section

namespace VG.Spec.Dsa.Random

/-- Width of one draw, independent of any leading-zero encoding padding. -/
def drawBytes (q : Nat) : Nat := (bitLength q + 7) / 8

/-- Exactly N random bits; equivalent to masking the first byte. -/
def candidate (q : Nat) (bytes : List Byte) : Nat :=
  decodeBE bytes % 2 ^ bitLength q

/-- `trace`: 0 rejected draw, 1 accepted draw, 2 exhausted tape,
3 exhausted draw limit, 4 invalid subgroup. `used` counts complete draws. -/
structure Sample where
  scalar : Option Nat
  used : Nat
  trace : List Nat
  deriving DecidableEq, Repr

/-- At most `fuel` draws. q <= 1 fails without consuming input. -/
def sample (q : Nat) : Nat → List Byte → Sample
  | 0, _ => ⟨none, 0, [3]⟩
  | fuel + 1, rand =>
    if q ≤ 1 then ⟨none, 0, [4]⟩ else
    let width := drawBytes q
    if rand.length < width then ⟨none, 0, [2]⟩ else
    let k := candidate q (rand.take width)
    if 0 < k && k < q then ⟨some k, width, [1]⟩ else
    let next := sample q fuel (rand.drop width)
    { next with used := width + next.used, trace := 0 :: next.trace }

end VG.Spec.Dsa.Random
