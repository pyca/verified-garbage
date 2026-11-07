module

public import VerifiedGarbage.Spec.Ed25519.Contract

/-!
# Ed25519: the contracts of its internal functions

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.

`vg_ed25519_public_key_expanded` derives the public key from the seed's
SHA-512 digest (RFC 8032 §5.1.5), which `vg_ed25519_key_pair`
(`Spec.Ed25519.keyPairContract`) calls after hashing the seed. As in
`Spec.Ed25519.signExpandedContract`, some seed must have the digest at
`expanded`, and the postcondition is the public key of every such seed.
-/

@[expose] public section

namespace VG.Proof.Ed25519

open VG.Spec VG.Spec.Ed25519

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

end VG.Proof.Ed25519
