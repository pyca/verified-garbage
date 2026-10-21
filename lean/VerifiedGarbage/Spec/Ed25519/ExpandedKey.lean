module

public import VerifiedGarbage.Spec.Ed25519.Contract

/-!
# Ed25519 public-key derivation that also returns the seed's SHA-512 digest

**Trusted** (as every file in `Spec/`). RFC 8032 §5.1.5 derives the public key
from the SHA-512 digest of the seed (step 1); §5.1.6, step 1 hashes the seed
again for every signature. This contract derives the public key as
`publicKeyContract` does and also writes that digest, so that a caller can
keep it for `signExpandedContract` (`ExpandedSign.lean`) without hashing the
seed a second time. Its postcondition is `publicKeyContract`'s, plus the
digest: nothing is required of the caller beyond the signature's buffers.
No buffer contents may affect timing.
-/

@[expose] public section

namespace VG.Spec.Ed25519

/-- `(out: *mut [u8; 32], expanded: *mut [u8; 64], seed: *const [u8; 32],
scratch: *mut [u64; 1024])`. -/
def publicKeyExpandedSig : Sig where
  params := [("out", .array true .u8 32), ("expanded", .array true .u8 64),
    ("seed", .array false .u8 32), ("scratch", .array true .u64 scratchWords)]

/-- Derive the public key from a seed, including SHA-512 and pruning, and
write the seed's SHA-512 digest. -/
def publicKeyExpandedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  publicKeyExpandedSig.contract A
    (post := fun out expanded seed _scratch m m' _ =>
      bytesAt m' out 32 = publicKey (bytesAt m seed 32) ∧
        bytesAt m' expanded 64 = Sha512.sha512 (bytesAt m seed 32))
    (writeArgs := true) (stack := stack)

/-- Public-key derivation that also returns the seed's digest, on every target. -/
def publicKeyExpandedApi : Api where
  module := "ed25519"
  name := "vg_ed25519_public_key_expanded"
  sig := publicKeyExpandedSig
  writeArgs := true
  contracts := some fun A stack => publicKeyExpandedContract A stack
  summary := "Ed25519 public-key derivation (RFC 8032 §5.1.5): writes the 32-byte public \
    key to `*out`, from the 32-byte private seed at `seed`, including SHA-512 and pruning, \
    and the seed's 64-byte SHA-512 digest (§5.1.6, step 1) to `*expanded`, for \
    `vg_ed25519_sign_expanded`. \
    Contract: `VG.Spec.Ed25519.publicKeyExpandedContract`. Constant time: only pointers may \
    affect timing."
  safety := ["`seed` must originate from a cryptographically secure random generator.",
    "The 64 bytes written to `expanded` are secret, as the seed is: the caller must \
      destroy them after use.", scratchSafety]

end VG.Spec.Ed25519
