module

public import VerifiedGarbage.Spec.Ed25519.Contract

/-!
# Ed25519 public-key derivation from the seed's SHA-512 digest

**Trusted** (as every file in `Spec/`). RFC 8032 §5.1.5 derives the public key
from the SHA-512 digest of the seed (step 1); §5.1.6, step 1 hashes the seed
again for every signature. A caller that computes the digest once, to keep it
for `signExpandedContract` (`ExpandedSign.lean`), can derive the public key
from it with this contract rather than hashing the seed a second time.

As in `signExpandedContract`, some seed must have the digest at `expanded`,
and the postcondition is `publicKeyContract`'s, `publicKey seed`, for every
such seed. It does not specify a public key for 64 bytes that are not the
digest of a seed. The seed itself is not a parameter: the public key depends
on the seed only through its digest. No buffer contents may affect timing.
-/

@[expose] public section

namespace VG.Spec.Ed25519

/-- `(out: *mut [u8; 32], expanded: *const [u8; 64], scratch: *mut [u64; 1024])`. -/
def publicKeyExpandedSig : Sig where
  params := [("out", .array true .u8 32), ("expanded", .array false .u8 64),
    ("scratch", .array true .u64 scratchWords)]

/-- Derive the public key from the SHA-512 digest of a seed, including pruning. -/
def publicKeyExpandedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  publicKeyExpandedSig.contract A
    (pre := fun _out expanded _scratch m =>
      ∃ seed : List Byte, seed.length = 32 ∧ bytesAt m expanded 64 = Sha512.sha512 seed)
    (post := fun out expanded _scratch m m' _ =>
      ∀ seed : List Byte, seed.length = 32 → bytesAt m expanded 64 = Sha512.sha512 seed →
        bytesAt m' out 32 = publicKey seed)
    (writeArgs := true) (stack := stack)

/-- Public-key derivation from the seed's digest, on every target. -/
def publicKeyExpandedApi : Api where
  module := "ed25519"
  name := "vg_ed25519_public_key_expanded"
  sig := publicKeyExpandedSig
  writeArgs := true
  contracts := some fun A stack => publicKeyExpandedContract A stack
  summary := "Ed25519 public-key derivation (RFC 8032 §5.1.5): writes the 32-byte public \
    key to `*out`, for the 32-byte private seed whose SHA-512 digest (§5.1.5, step 1) is at \
    `expanded`, including pruning. \
    Contract: `VG.Spec.Ed25519.publicKeyExpandedContract`. Constant time: only pointers may \
    affect timing."
  safety := [
    "The 64 bytes at `expanded` must equal the SHA-512 digest (`VG.Spec.Sha512.sha512`) \
      of a 32-byte seed.",
    "The seed must originate from a cryptographically secure random generator.", scratchSafety]

end VG.Spec.Ed25519
