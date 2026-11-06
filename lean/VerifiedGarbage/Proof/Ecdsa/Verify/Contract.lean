module

public import VerifiedGarbage.Spec.Ecdsa.Verify
public import VerifiedGarbage.Spec.Ecdsa.Generic

/-!
# ECDSA verification of `len` octets: the internal verifications' contract

Not trusted: what each target's internal verification of a curve, run by
the implementations of `vg_ecdsa_<name>_verify` once they have converted
the hash to `len` octets, is proven against. The trusted contract,
`Spec/Ecdsa/Verify/Generic.lean`'s `Instance.verifyHashContract`, takes the
hash function's output itself; each target's `verifyHash_verified` proves
it from this one and from `hashToInt_fixedDigest`
(`Proof/Ecdsa/Verify/Hash.lean`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa

open Spec.Weierstrass Spec.Ecdsa

variable (I : Spec.Ecdsa.Instance)

/-- `(public: *const [u8; 2 len + 1], digest: *const [u8; len],
sig: *const [u8; 2 len], scratch: *mut [u64; 1024]) -> u32`. -/
def verifySig : Sig where
  params := [("public", .array false .u8 (2 * I.curve.len + 1)), ("digest", .array false .u8 I.curve.len),
    ("sig", .array false .u8 (2 * I.curve.len)), ("scratch", .array true .u64 scratchWords)]
  ret := some .u32

/-- Whether the signature at `sig` of the `len` octets at `digest` (whose
leftmost `N` bits are `e`, as `hashToInt` reads them) verifies with the
public key at `public` (`verify`): it returns 1 if it does and 0 otherwise.
Every input is public, and may affect timing. -/
def verifyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (verifySig I).contract A
    (post := fun pk digest sig _scratch m _m' r =>
      r = if verify I.curve (bytesAt m pk (2 * I.curve.len + 1))
          (hashToInt I.curve (bytesAt m digest I.curve.len)) (bytesAt m sig (2 * I.curve.len))
        then 1 else 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun pk digest sig _scratch m =>
      (bytesAt m pk (2 * I.curve.len + 1) ++ bytesAt m digest I.curve.len ++
        bytesAt m sig (2 * I.curve.len)).map (·.toNat))

end VG.Proof.Ecdsa
