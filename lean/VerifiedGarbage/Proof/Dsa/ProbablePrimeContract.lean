module

public import VerifiedGarbage.Proof.Dsa.ModPowContract
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Impl.Dsa.HelperLayout

/-!
# DSA's probable-prime test at a fixed offset of a working space

Not trusted: the contracts of internal functions (`Rust.Internal`), which only
verified code calls, that their proofs and their callers' compose.

A callable piece of DSA parameter generation:
`vg_dsa_probable_prime_{bits}` runs `Spec.Dsa.probablePrime` (trial
division, then RSA's blinded Miller–Rabin loop with DSA's round policy) on
an odd number of exactly `bits` bits, stored as `bits / 8` big-endian bytes
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
namespace VG.Proof.Dsa.ProbablePrime

open VG.Spec VG.Spec.Dsa
open VG.Impl.Dsa.ProbablePrime (Layout)
open VG.Spec.Rsa (bytesAt wordsAt)
open VG.Proof.Dsa.ModPow (Keeps)

/-- The candidate in memory `m`. -/
def candidateAt (L : Layout) (m : Mem) (ws : Addr) : Nat :=
  decodeBE (bytesAt m (ws + BitVec.ofNat 64 L.candidate) (L.bits / 8))

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
      let w := candidateAt L m ws
      L.size ≤ 8 * wsLen.toNat ∧ w % 2 = 1 ∧ Spec.Dsa.bitLength w = L.bits)
    (post := fun ws wsLen rand randLen used m m' r =>
      let res := Spec.Dsa.probablePrime (candidateAt L m ws) (bytesAt m rand randLen.toNat)
      r.toNat = status res ∧ Keeps ws wsLen.toNat L.scratch m m' ∧
        ∀ b rest, res = some (b, rest) →
          wordsAt m' used 1 = [BitVec.ofNat 64 (randLen.toNat - rest.length)])
    (writeArgs := true) (stack := stack)
    (leak := some fun ws _wsLen rand randLen _used m =>
      candidateAt L m ws :: (bytesAt m rand randLen.toNat).map (·.toNat))

/-! ## One function for every size

`vg_dsa_probable_prime` is the test of `api (layout bits)` for a size
`bits` it takes as an argument, one of `sizes`: one function where a target
would otherwise register one per size. Its meaning for each size is
`contract (layout bits)`'s. -/

/-- The working space, the random tape, the octets read and the size. -/
def sizedSig : Sig where
  params := [("ws", .slice true .u64 "ws_len"), ("rand", .slice false .u8 "rand_len"),
    ("used", .array true .u64 1), ("bits", .int .usize true)]
  ret := some .u32

/-- `contract (layout bits)` for a size `bits` of `sizes`, given as an
argument. The size is public, with the candidate and the tape. -/
def sizedContract {I : ISA} (layout : Nat → Layout) (sizes : List Nat) (A : Abi I)
    (stack : Nat := 0) : Contract I :=
  sizedSig.contract A
    (pre := fun ws wsLen _rand _randLen _used bits m =>
      let L := layout bits.toNat
      let w := candidateAt L m ws
      bits.toNat ∈ sizes ∧ L.bits = bits.toNat ∧
        L.size ≤ 8 * wsLen.toNat ∧ w % 2 = 1 ∧ Spec.Dsa.bitLength w = L.bits)
    (post := fun ws wsLen rand randLen used bits m m' r =>
      let L := layout bits.toNat
      let res := Spec.Dsa.probablePrime (candidateAt L m ws) (bytesAt m rand randLen.toNat)
      r.toNat = status res ∧ Keeps ws wsLen.toNat L.scratch m m' ∧
        ∀ b rest, res = some (b, rest) →
          wordsAt m' used 1 = [BitVec.ofNat 64 (randLen.toNat - rest.length)])
    (writeArgs := true) (stack := stack)
    (leak := some fun ws _wsLen rand randLen _used bits m =>
      bits.toNat :: candidateAt (layout bits.toNat) m ws ::
        (bytesAt m rand randLen.toNat).map (·.toNat))

end VG.Proof.Dsa.ProbablePrime
