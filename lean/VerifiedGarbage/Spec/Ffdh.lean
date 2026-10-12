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
rejection sampling. Exhaustion is failure. Miller–Rabin uses 64 witnesses
through 2048 bits and 128 above, rather than RSA's distribution-specific
round count. Acceptance is probable primality, not a theorem of primality.
This mathematical specification makes no execution timing claim.
-/

@[expose] public section
namespace VG.Spec.Ffdh
open VG.Spec.Rsa (powMod i2osp)
open VG.Spec.RsaKeyGen (bitLength)

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
    some (i2osp ((bitLength a.p + 7) / 8) z)

def primeChecks (bits : Nat) : Nat := if bits ≤ 2048 then 64 else 128

/-- One strong probable-prime test with a uniform witness in [2,p-2]. -/
def mrRound (p a : Nat) : Bool :=
  let (s, d) := VG.Spec.Rsa.splitTwos (p - 1)
  let z := powMod a d p
  z == 1 || ((List.range s).any fun j => powMod z (2 ^ j) p == p - 1)

/-- The witnesses are supplied explicitly, already rejection-sampled. -/
def probablePrime (p : Nat) (witnesses : List Nat) : Bool :=
  p > 2 && p % 2 == 1 &&
  !(VG.Spec.RsaKeyGen.smallPrimes.take 54).any (fun s => p % s == 0 && p != s) &&
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

/-- Select a word by the low bit, used by the fixed-schedule exponentiation.
Both candidate words and the bit are secret. -/
def choose (a b bit : BitVec 64) : BitVec 64 :=
  a ^^^ ((a ^^^ b) &&& (0 - (bit &&& 1)))
end VG.Spec.Ffdh
