module

public import VerifiedGarbage.Spec.Dsa.SignVerify

/-!
# Separate DSA public-key validation and verification contracts (trusted)

An immutable owner may validate its packed public key once and use the
prevalidated verifier for subsequent signatures. Validation includes every
parameter/public-key algebraic check made by `verifyBytes`; it does not
establish primality. The prevalidated verifier still returns exactly
`verifyBytes`, including signature rejection and digest handling.

These contracts do not change the existing fully checked verification API.
A caller of the new verifier must establish validation for the exact bytes
it passes, and keep those bytes unchanged. Signature and digest bytes retain
the existing leakage policy; only the public key and result are declassified.
-/

@[expose] public section

namespace VG.Spec.Dsa

open VG.Spec.Rsa (bytesAt)

/-- All reusable validation, including both public subgroup memberships. -/
def validatePublicKeyBytes (pLen qLen : Nat) (key : List Byte) : Bool :=
  if !(lengthsValid pLen qLen) || key.length != 3 * pLen + qLen then false else
    let k := publicKeyBytes pLen qLen key
    decide (parametersValid k.params) && keyValid k

def validatePublicKeySig : Sig where
  params := [("key", .slice false .u8 "key_len"), ("p_len", .int .usize true),
    ("q_len", .int .usize true), ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

/-- Return one exactly for an algebraically valid public key; no primality test. -/
def validatePublicKeyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  validatePublicKeySig.contract A
    (pre := fun _key keyLen pLen qLen _scratch scratchLen _ =>
      lengthsValid pLen.toNat qLen.toNat ∧ keyLen.toNat = 3 * pLen.toNat + qLen.toNat ∧
        scratchWords pLen.toNat ≤ scratchLen.toNat)
    (post := fun key keyLen pLen qLen _scratch _scratchLen m _m' r =>
      r.toNat = if validatePublicKeyBytes pLen.toNat qLen.toNat
        (bytesAt m key keyLen.toNat) then 1 else 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun key keyLen pLen qLen _scratch _scratchLen m =>
      publicBytesLeak pLen.toNat qLen.toNat (bytesAt m key keyLen.toNat))

/-- The old verification result, under an explicit validated-key precondition.
The key's exact bytes, rather than a caller-provided boolean or workspace
flag, must satisfy validation. Scratch contents cannot certify validation. -/
def verifyPrevalidatedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  verifySig.contract A
    (pre := fun key keyLen pLen qLen _signature signatureLen _digest _digestLen _scratch scratchLen m =>
      lengthsValid pLen.toNat qLen.toNat ∧ keyLen.toNat = 3 * pLen.toNat + qLen.toNat ∧
        signatureLen.toNat = 2 * qLen.toNat ∧ scratchWords pLen.toNat ≤ scratchLen.toNat ∧
        validatePublicKeyBytes pLen.toNat qLen.toNat (bytesAt m key keyLen.toNat) = true)
    (post := fun key keyLen pLen qLen signature signatureLen digest digestLen _scratch _scratchLen m _m' r =>
      r.toNat = if verifyBytes pLen.toNat qLen.toNat (bytesAt m key keyLen.toNat)
        (bytesAt m signature signatureLen.toNat) (bytesAt m digest digestLen.toNat) then 1 else 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun key keyLen pLen qLen signature signatureLen digest digestLen _scratch _scratchLen m =>
      let kb := bytesAt m key keyLen.toNat
      publicBytesLeak pLen.toNat qLen.toNat kb ++
        [if verifyBytes pLen.toNat qLen.toNat kb (bytesAt m signature signatureLen.toNat)
          (bytesAt m digest digestLen.toNat) then 1 else 0])

def validatePublicKeyApi : Api where
  module := "dsa"
  name := "vg_dsa_validate_public_key"
  sig := validatePublicKeySig
  writeArgs := true
  contracts := some fun A stack => validatePublicKeyContract A stack
  summary := "Validate packed DSA p||q||g||y, including domain consistency and both subgroup \
    memberships. Returns 1 exactly when validation succeeds, otherwise 0. Does not test primality. \
    The key is public; scratch contents are unspecified on return. \
    Contract: `VG.Spec.Dsa.validatePublicKeyContract`."
  safety := ["(p_len, q_len) must be (128,20), (256,20), (256,28), (256,32), or (384,32).",
    "key_len must be 3*p_len + q_len; scratch_len must be at least 16*p_len words."]

def verifyPrevalidatedApi : Api where
  module := "dsa"
  name := "vg_dsa_verify_prevalidated"
  sig := verifySig
  writeArgs := true
  contracts := some fun A stack => verifyPrevalidatedContract A stack
  summary := "DSA verification with the same result as vg_dsa_verify, for an already validated \
    packed public key. Signature scalars and digest handling retain the fully checked API's \
    behavior. Timing may depend on p,q,g,y and the result, not otherwise on signature or digest. \
    Contract: `VG.Spec.Dsa.verifyPrevalidatedContract`."
  safety := ["(p_len, q_len) must be (128,20), (256,20), (256,28), (256,32), or (384,32).",
    "key_len must be 3*p_len + q_len; signature_len must be 2*q_len.",
    "scratch_len must be at least 16*p_len words. Scratch contents are unspecified on return.",
    "The exact key bytes must satisfy validatePublicKeyBytes p_len q_len key = true. \
      A successful vg_dsa_validate_public_key call establishes this only while the key bytes \
      remain unchanged. Primality remains the caller's responsibility."]

end VG.Spec.Dsa
