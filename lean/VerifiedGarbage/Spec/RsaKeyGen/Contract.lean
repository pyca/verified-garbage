module

public import VerifiedGarbage.Spec.RsaKeyGen
public import VerifiedGarbage.Spec.Rsa.Contract

/-!
# RSA key generation: what its contracts share

**Trusted** (as every file in `Spec/`). The bounds on a prime's length
(`primeLenValid`), the other prime a candidate must not be too close to
(`otherPrime`), and a candidate for a prime (`RsaKeyGen.candidateStep`) from
the random octets given (`candidateOp`), its status and what its timing may
depend on (`candidateLeak`): what the prime search (`Generation.lean`) and
`vg_rsa_generate` (`KeySearchContract.lean`) are built on.

A prime is `p_len` octets, a multiple of 8 from 32 to 512 (primes of 256 to
4096 bits); `e` is 1 to 8 octets. The randomness is read from the front as
`RsaKeyGen.generate` reads its randomness. Everything about a rejected
candidate may leak (its octets, and the witnesses read for it), but for a
candidate rejected for being too close to `p`, only that: the candidate is
then not independent of `p`. Of a candidate accepted as a probable prime,
only how many octets of `rand` were read (the number of Miller–Rabin
witnesses BoringSSL's blinding needed, which it declassifies).
-/

@[expose] public section

namespace VG.Spec.RsaKeyGen

open VG.Spec.Rsa (os2ip)

/-- The bounds on a prime's length, in octets: a multiple of 8 (whole 64-bit
words) from 32 to 512, which `generate` makes `nlen / 16` for its modulus of
`nlen` bits from 512 to 8192, a multiple of 128. -/
def primeLenValid (pLen : Nat) : Prop := 32 ≤ pLen ∧ pLen ≤ 512 ∧ pLen % 8 = 0

/-- The other prime a candidate must not be too close to: none for no
octets. -/
def otherPrime (pB : List Byte) : Option Nat := if pB = [] then none else some (os2ip pB)

/-- `candidateStep` for a prime of `pLen` octets and the public exponent `eB`,
not too close to the prime `pB` (none if empty), from the random octets
`rand`. -/
def candidateOp (pLen : Nat) (eB pB rand : List Byte) : Option (Candidate × Rand) :=
  candidateStep (8 * pLen) (os2ip eB) (otherPrime pB) rand

/-- The status `vg_rsa_keygen_candidate` returns. -/
def candidateStatus : Option (Candidate × Rand) → Nat
  | none => 0
  | some (.prime _, _) => 1
  | some (.close, _) => 2
  | some (.rejected, _) => 3

/-- What a candidate's timing may depend on, beyond the lengths and `e`: what
became of it; for a probable prime, how many octets of `rand` were read; for
a rejected one, but too close to `p`, the octets read. -/
def candidateLeak (pLen : Nat) (eB pB rand : List Byte) : List Nat :=
  match candidateOp pLen eB pB rand with
  | none => [0]
  | some (.prime _, rest) => [1, rand.length - rest.length]
  | some (.close, _) => [2]
  | some (.rejected, rest) => 3 :: (rand.take (rand.length - rest.length)).map (·.toNat)

end VG.Spec.RsaKeyGen
