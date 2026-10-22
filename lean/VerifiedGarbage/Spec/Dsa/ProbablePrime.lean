module

public import VerifiedGarbage.Spec.Dsa.ModPow
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract

/-!
# DSA's probable-prime test at a fixed offset of a working space

**Trusted.** A callable piece of DSA parameter generation:
`vg_dsa_probable_prime_{bits}` runs `Spec.Dsa.probablePrime` (trial
division, then RSA's blinded Miller–Rabin loop with DSA's round policy) on
an odd number of exactly `bits` bits, stored in `8 n` bytes, little-endian,
at a fixed offset of a working space, drawing its witnesses from the front
of a tape of random octets. Parameter generation tests q and every p
candidate this way, with one tape threaded through all of them; each has
its size's exact bit length and is odd by construction, so the test's
trial division, witness width and round count are fixed by its layout.

It returns 1 for a probable prime, 2 for a composite, and 0 if the tape ran
out; for 1 and 2 it writes to `used` the number of octets it read. Its
`Layout` gives the width, the candidate's offset and the ranges of the
working space it may change; every other byte keeps its value. Acceptance
is probable primality, not a certificate.

The candidate and the tape are public: parameter generation discloses all
of its tapes, and the test's running time depends on both (how many
witnesses it reads, and where trial division or a round rejects).
-/

@[expose] public section
namespace VG.Spec.Dsa.ProbablePrime
open VG.Spec.Rsa (bytesAt wordsAt)
open VG.Spec.Dsa.ModPow (numAt Keeps rangesDoc)

/-- The width and byte offsets of a test in its working space. -/
structure Layout where
  /-- The candidate's exact bit length. -/
  bits : Nat
  /-- The 64-bit words that hold the candidate. -/
  n : Nat
  /-- The candidate's byte offset in the working space. -/
  candidate : Nat
  /-- The ranges `(offset, bytes)` of the working space that the function
  may change. -/
  scratch : List (Nat × Nat)
  /-- The bytes of the working space that the function uses. -/
  size : Nat

/-- The status of a test's result: 0 if the tape ran out, 1 for a probable
prime, 2 for a composite. -/
def status : Option (Bool × Spec.RsaKeyGen.Rand) → Nat
  | none => 0
  | some (true, _) => 1
  | some (false, _) => 2

/-- The working space, the random tape and the octets read. -/
def sig : Sig where
  params := [("ws", .slice true .u64 "ws_len"), ("rand", .slice false .u8 "rand_len"),
    ("used", .array true .u64 1)]
  ret := some .u32

/-- For a working space of at least `L.size` bytes and an odd candidate `w`
at `L.candidate` of exactly `L.bits` bits: the status of `probablePrime w
rand` for the tape `rand`, and when the tape sufficed, the octets read into `used`. Only the
bytes of `L.scratch` may change. The candidate and the tape are public. -/
def contract {I : ISA} (L : Layout) (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig.contract A
    (pre := fun ws wsLen _rand _randLen _used m =>
      let w := numAt m ws L.candidate (8 * L.n)
      L.size ≤ 8 * wsLen.toNat ∧ w % 2 = 1 ∧ Spec.Dsa.bitLength w = L.bits)
    (post := fun ws wsLen rand randLen used m m' r =>
      let res := Spec.Dsa.probablePrime (numAt m ws L.candidate (8 * L.n)) (bytesAt m rand randLen.toNat)
      r.toNat = status res ∧ Keeps ws wsLen.toNat L.scratch m m' ∧
        ∀ b rest, res = some (b, rest) →
          wordsAt m' used 1 = [BitVec.ofNat 64 (randLen.toNat - rest.length)])
    (writeArgs := true) (stack := stack)
    (leak := some fun ws _wsLen rand randLen _used m =>
      numAt m ws L.candidate (8 * L.n) :: (bytesAt m rand randLen.toNat).map (·.toNat))

/-- The test of layout `L`, with the same meaning on every target that
registers it. -/
def api (L : Layout) : Api where
  module := "dsa"
  name := s!"vg_dsa_probable_prime_{L.bits}"
  sig := sig
  writeArgs := true
  contracts := some fun A stack => contract L A stack
  summary := s!"DSA's probable-prime test (`VG.Spec.Dsa.probablePrime`: trial division, then \
    RSA's blinded Miller–Rabin loop with 64 uniform witnesses through 2048 bits and 128 above) \
    of the odd {L.bits}-bit number of {8 * L.n} bytes, little-endian, at byte {L.candidate} \
    of `ws`, with witnesses drawn from the front of `rand`. Returns 1 for a probable prime, 2 for a \
    composite, and 0 if `rand` ran out; for 1 and 2 writes the octets read to `used`. Every \
    byte of `ws` but those of the ranges {rangesDoc L.scratch} keeps its value. Acceptance \
    is probable primality, not a certificate.\n\n\
    Contract: `VG.Spec.Dsa.ProbablePrime.contract`. The candidate and the tape are public: \
    timing may depend on both."
  safety := [s!"`ws_len` must be at least {(L.size + 7) / 8}.",
    s!"The {8 * L.n} bytes at byte {L.candidate} of `ws` must hold an odd number of exactly \
      {L.bits} bits.",
    "`rand` must contain independent uniform random octets for the probabilistic \
      interpretation. They are not secret under this contract.",
    s!"The bytes {rangesDoc L.scratch} of `ws` are unspecified on return."]

end VG.Spec.Dsa.ProbablePrime
