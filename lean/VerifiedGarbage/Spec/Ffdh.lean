module

public import VerifiedGarbage.Spec.RsaKeyGen

/-!
# Finite-field Diffie–Hellman

**Trusted.** The component operations requested in issue #1, following
SP 800-56A Rev. 3 §§5.6.1.1, 5.6.2.1 and 5.7.1.1 and PKCS #3 §8.
Serialization, hashing/KDFs, protocol negotiation and parameter certificates
belong to callers. Integers are unsigned; exchange is padded to the modulus'
byte length, as pyca/cryptography's DHPrivateKey.exchange requires.

Imported domains receive structural/algebraic checks, not primality
certificates. Callers must establish their provenance. An optional q gives
subgroup validation; without it only the public range can be checked.
Generation uses probable safe primes, generators 2 or 5, and OpenSSL's
congruence restrictions (p mod 24 = 11 for 2, p mod 10 = 3 or 7 for 5).
Generated parameters omit q: these generators need not have order (p-1)/2.

The tapes below represent independent uniform random integers after bounded
rejection sampling. Exhaustion is failure. "Octet tapes" draws them from
random octets, as the operations of `Ffdh/Contract.lean` read them.
Miller–Rabin uses 64 witnesses through 2048 bits and 128 above, rather than
RSA's distribution-specific round count. Acceptance is probable primality, not a theorem of primality.
This mathematical specification makes no execution timing claim.
-/

@[expose] public section
namespace VG.Spec.Ffdh
open VG.Spec.Rsa (powMod i2osp os2ip)
open VG.Spec.RsaKeyGen (bitLength Rand draw loop)

structure Parameters where
  p : Nat
  g : Nat
  q : Option Nat := none
  deriving DecidableEq, Repr

structure PublicKey where
  params : Parameters
  y : Nat
  deriving DecidableEq, Repr

structure PrivateKey where
  publicKey : PublicKey
  x : Nat
  deriving DecidableEq, Repr

/-- Structural/algebraic checks; imported p and q are not primality-tested. -/
def parametersValid (a : Parameters) : Bool :=
  512 ≤ bitLength a.p && bitLength a.p ≤ 8192 && a.p % 2 == 1 &&
  1 < a.g && a.g < a.p - 1 && match a.q with
    | none => true
    | some q => 2 < q && q % 2 == 1 && q < a.p - 1 &&
        (a.p - 1) % q == 0 && powMod a.g q a.p == 1

def parametersFrom (p g : Nat) (q : Option Nat) : Option Parameters :=
  let a : Parameters := ⟨p, g, q⟩
  if parametersValid a then some a else none

/-- Reject the identity and order-two value even without q. -/
def publicValid (k : PublicKey) : Bool :=
  1 < k.y && k.y < k.params.p - 1 && match k.params.q with
    | none => true
    | some q => powMod k.y q k.params.p == 1

def privateValid (a : Parameters) (x : Nat) : Bool :=
  0 < x && x < a.q.getD (a.p - 1)

def publicFrom (a : Parameters) (y : Nat) : Option PublicKey :=
  let k : PublicKey := ⟨a, y⟩
  if parametersValid a && publicValid k then some k else none

def privateFrom (a : Parameters) (y x : Nat) : Option PrivateKey := do
  let k ← publicFrom a y
  if privateValid a x && powMod a.g x a.p == y then some ⟨k, x⟩ else none

/-- Component export is exact, including whether q was supplied. -/
def publicComponents (k : PublicKey) : Nat × Nat × Option Nat × Nat :=
  (k.params.p, k.params.g, k.params.q, k.y)
def privateComponents (k : PrivateKey) : Nat × Nat × Option Nat × Nat × Nat :=
  (k.publicKey.params.p, k.publicKey.params.g, k.publicKey.params.q, k.publicKey.y, k.x)

/-- Uniform scalar sampling; invalid samples and degenerate public keys retry. -/
def generate (a : Parameters) : List Nat → Option PrivateKey
  | [] => none
  | x :: xs =>
    if !parametersValid a then none else
    match privateFrom a (powMod a.g x a.p) x with
    | some k => some k
    | none => generate a xs

/-- Parameter equality prevents exchanging across domains. Reject degenerate
shared values as well as invalid peers. No KDF is applied. -/
def exchange (k : PrivateKey) (peer : PublicKey) : Option (List Byte) :=
  let a := k.publicKey.params
  if a != peer.params || !publicValid peer then none else
  let z := powMod peer.y k.x a.p
  if z ≤ 1 || z == a.p - 1 then none else
    some (i2osp z ((bitLength a.p + 7) / 8))

def primeChecks (bits : Nat) : Nat := if bits ≤ 2048 then 64 else 128

/-- One strong probable-prime test with a uniform witness in [2,p-2]. -/
def mrRound (p a : Nat) : Bool :=
  let (s, d) := VG.Spec.Rsa.splitTwos (p - 1)
  let z := powMod a d p
  z == 1 || ((List.range s).any fun j => powMod z (2 ^ j) p == p - 1)

/-- The checks before Miller–Rabin: odd, above 2, and no prime below 256
divides it but itself. -/
def primeShape (p : Nat) : Bool :=
  p > 2 && p % 2 == 1 &&
  !(VG.Spec.RsaKeyGen.smallPrimes.take 54).any (fun s => p % s == 0 && p != s)

/-- The witnesses are supplied explicitly, already rejection-sampled. -/
def probablePrime (p : Nat) (witnesses : List Nat) : Bool :=
  primeShape p &&
  witnesses.length == primeChecks (bitLength p) &&
  witnesses.all (fun a => 2 ≤ a && a < p - 1 && mrRound p a)

def generationShape (bits generator p : Nat) : Bool :=
  512 ≤ bits && bits ≤ 8192 && bitLength p == bits &&
  if generator == 2 then p % 24 == 11 else
    generator == 5 && (p % 10 == 3 || p % 10 == 7)

/-- Random candidate with independent witness tapes for p and (p-1)/2.
The result contains no q, matching PKCS #3 parameter generation. -/
def generateParameters (bits generator : Nat) : List (Nat × List Nat × List Nat) → Option Parameters
  | [] => none
  | (p, wp, wq) :: rest =>
    if generationShape bits generator p && probablePrime p wp && probablePrime ((p - 1) / 2) wq
    then some ⟨p, generator, none⟩ else generateParameters bits generator rest

/-! ## Octet tapes

The lists of integers above, drawn from random octets as the operations draw
them. Each draw takes the next octets of the tape as an integer, most
significant first (`RsaKeyGen.draw`), cut to the bit length of its bound;
a value outside its range is rejected and drawn again. A tape that runs out
gives `none`; a caller supplying more randomness gets the same result for
any extension of a tape that sufficed. -/

/-- The bound a private scalar is below: q, or p-1 without q. -/
def scalarBound (a : Parameters) : Nat := a.q.getD (a.p - 1)

/-- The scalar of one key-generation attempt (an element of `generate`'s
list) from random octets: their integer cut to the bit length of
`scalarBound`. A value outside [1, bound-1] fails `privateValid`, and
`generate` goes on to the next attempt. -/
def scalarOfOctets (a : Parameters) (r : List Byte) : Nat :=
  os2ip r % 2 ^ bitLength (scalarBound a)

/-- A candidate p of `bits` bits from the random integer `x`: `x` cut to
`bits` bits, with its most and least significant bits set. -/
def candidateOf (bits x : Nat) : Nat := x % 2 ^ bits ||| 2 ^ (bits - 1) ||| 1

/-- The octets drawn for a witness for `w`: those of `w - 1`. -/
def witnessOctets (w : Nat) : Nat := (bitLength (w - 1) + 7) / 8

/-- One draw of a Miller–Rabin witness for `w`, cut to the bit length of
`w - 1`: the witness if it is in [2, w-2], otherwise draw again. -/
def witnessStep (w : Nat) (_ : Unit) (r : Rand) : Option ((Nat ⊕ Unit) × Rand) := do
  let (x, r) ← draw (witnessOctets w) r
  let a := x % 2 ^ bitLength (w - 1)
  if 2 ≤ a && a < w - 1 then return (.inl a, r) else return (.inr (), r)

/-- A uniform witness in [2, w-2], by rejection sampling. -/
def drawWitness (w : Nat) (r : Rand) : Option (Nat × Rand) := loop (witnessStep w) () r

/-- Up to `n` witnesses for `w`, drawn one at a time; the first that proves
`w` composite (`mrRound`) is the last one drawn. -/
def drawWitnesses (w : Nat) : Nat → Rand → Option (List Nat × Rand)
  | 0, r => some ([], r)
  | n + 1, r => do
    let (a, r) ← drawWitness w r
    if mrRound w a then
      let (as, r) ← drawWitnesses w n r
      return (a :: as, r)
    else return ([a], r)

/-- One element of `generateParameters`' list from the tape, and whether it
is accepted: the candidate p from `⌈bits/8⌉` octets (`candidateOf`); if it
has the generator's shape and p and q = (p-1)/2 pass `primeShape`, the
witnesses for q and then, if q is a probable prime, those for p. Returns
the accepted p, if it is, and the octets left. -/
def parameterCandidate (bits generator : Nat) (r : Rand) : Option (Option Nat × Rand) := do
  let (x, r) ← draw ((bits + 7) / 8) r
  let p := candidateOf bits x
  let q := (p - 1) / 2
  if !(generationShape bits generator p && primeShape p && primeShape q) then
    return (none, r)
  let (wq, r) ← drawWitnesses q (primeChecks (bitLength q)) r
  let (wp, r) ← if probablePrime q wq then drawWitnesses p (primeChecks (bitLength p)) r
    else some ([], r)
  return (if generationShape bits generator p && probablePrime p wp && probablePrime q wq
    then some p else none, r)

/-- Select a word by the low bit, used by the fixed-schedule exponentiation.
Both candidate words and the bit are secret. -/
def choose (a b bit : BitVec 64) : BitVec 64 :=
  a ^^^ ((a ^^^ b) &&& (0 - (bit &&& 1)))
end VG.Spec.Ffdh
