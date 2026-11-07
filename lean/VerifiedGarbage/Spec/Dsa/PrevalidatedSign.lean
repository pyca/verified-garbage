module

public import VerifiedGarbage.Spec.Dsa.RandomSign

/-!
# Separate DSA private-key validation from randomized signing (trusted)

`vg_dsa_sign_random` checks the whole key on every call: the domain's
consistency, including `g^q mod p = 1`, and the key's, including
`g^x mod p = y`. Those are two modular exponentiations of the same size as
signing's own `g^k mod p`, repeated for every signature although they depend
only on the key. As `vg_dsa_validate_public_key` does for verification
(`Prevalidated.lean`), an owner of an immutable packed private key may
validate it once (`vg_dsa_validate_private_key`) and then sign with
`vg_dsa_sign_random_prevalidated`, which returns exactly what
`vg_dsa_sign_random` returns (`randomSignContract`): the same signature,
status, consumption, output zeroing and permitted leakage.

Validation is every check `signBytes` makes of the key alone, independent
of the nonce and the digest: the supported widths, `parametersValid` of the
domain and `keyValid` of the key with its private scalar. It does not
establish primality. A caller of the prevalidated signer must establish
validation for the exact key bytes it passes, and keep those bytes
unchanged; neither a caller-provided boolean nor scratch contents can
certify it. The validation result depends on the private scalar (its range
and `g^x mod p = y`), and is declassified, as signing's success bit is.
-/

@[expose] public section

namespace VG.Spec.Dsa

open VG.Spec.Rsa (bytesAt wordsAt)

/-- Every check `signBytes` makes of the packed private key alone. -/
def validatePrivateKeyBytes (pLen qLen : Nat) (key : List Byte) : Bool :=
  if !(lengthsValid pLen qLen) || key.length != 3 * pLen + 2 * qLen then false else
    let k := privateKeyBytes pLen qLen key
    decide (parametersValid k.params) && keyValid k

def validatePrivateKeySig : Sig where
  params := [("key", .slice false .u8 "key_len"), ("p_len", .int .usize true),
    ("q_len", .int .usize true), ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

/-- Return one exactly for an algebraically valid private key; no primality
test. Timing may depend on the public components and the result. -/
def validatePrivateKeyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  validatePrivateKeySig.contract A
    (pre := fun _key keyLen pLen qLen _scratch scratchLen _ =>
      lengthsValid pLen.toNat qLen.toNat ∧ keyLen.toNat = 3 * pLen.toNat + 2 * qLen.toNat ∧
        scratchWords pLen.toNat ≤ scratchLen.toNat)
    (post := fun key keyLen pLen qLen _scratch _scratchLen m _m' r =>
      r.toNat = if validatePrivateKeyBytes pLen.toNat qLen.toNat
        (bytesAt m key keyLen.toNat) then 1 else 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun key keyLen pLen qLen _scratch _scratchLen m =>
      let kb := bytesAt m key keyLen.toNat
      publicBytesLeak pLen.toNat qLen.toNat kb ++
        [if validatePrivateKeyBytes pLen.toNat qLen.toNat kb then 1 else 0])

/-- `randomSignContract`'s result and leakage, under an explicit
validated-key precondition on the key's exact bytes. -/
def randomSignPrevalidatedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  randomSignSig.contract A
    (pre := fun _out outLen _used key keyLen pLen qLen _digest _digestLen
        _rand _randLen _scratch scratchLen m =>
      lengthsValid pLen.toNat qLen.toNat ∧ outLen.toNat = 2 * qLen.toNat ∧
        keyLen.toNat = 3 * pLen.toNat + 2 * qLen.toNat ∧
        randomSignScratchWords pLen.toNat ≤ scratchLen.toNat ∧
        validatePrivateKeyBytes pLen.toNat qLen.toNat (bytesAt m key keyLen.toNat) = true)
    (post := fun out outLen used key keyLen pLen qLen digest digestLen
        rand randLen _scratch _scratchLen m m' r =>
      let res := randomSignBytes pLen.toNat qLen.toNat (bytesAt m key keyLen.toNat)
        (bytesAt m digest digestLen.toNat) (bytesAt m rand randLen.toNat)
      r.toNat = res.status ∧
        bytesAt m' out outLen.toNat = res.signature.getD (List.replicate outLen.toNat 0) ∧
        wordsAt m' used 1 = [BitVec.ofNat 64 res.used])
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen _used key keyLen pLen qLen digest digestLen
        rand randLen _scratch _scratchLen m =>
      let kb := bytesAt m key keyLen.toNat
      let res := randomSignBytes pLen.toNat qLen.toNat kb
        (bytesAt m digest digestLen.toNat) (bytesAt m rand randLen.toNat)
      publicBytesLeak pLen.toNat qLen.toNat kb ++ [res.status, res.used] ++ res.trace)

def validatePrivateKeyApi : Api where
  module := "dsa"
  name := "vg_dsa_validate_private_key"
  sig := validatePrivateKeySig
  writeArgs := true
  contracts := some fun A stack => validatePrivateKeyContract A stack
  summary := "Validate packed DSA p||q||g||y||x as signing checks it: domain consistency, \
    including g^q mod p = 1, 1 < y < p, 0 < x < q and g^x mod p = y. Returns 1 exactly when \
    validation succeeds, otherwise 0. Does not test primality. Timing may depend on p,q,g,y \
    and the result, not otherwise on x. Scratch contents are unspecified on return and may \
    hold secrets. Contract: `VG.Spec.Dsa.validatePrivateKeyContract`."
  safety := ["(p_len, q_len) must be (128,20), (256,20), (256,28), (256,32), or (384,32).",
    "key_len must be 3*p_len + 2*q_len; scratch_len must be at least 16*p_len words; \
      destroy scratch after use."]

def randomSignPrevalidatedApi : Api where
  module := "dsa"
  name := "vg_dsa_sign_random_prevalidated"
  sig := randomSignSig
  writeArgs := true
  contracts := some fun A stack => randomSignPrevalidatedContract A stack
  summary := "Randomized DSA signing of a prehashed digest, for an already validated packed \
    private key (big-endian p||q||g||y||x; vg_dsa_validate_private_key validates it). Returns \
    exactly what vg_dsa_sign_random returns (`VG.Spec.Dsa.randomSignContract`): 1 with \
    fixed-width r||s, 0 for retry exhaustion, or 2 for insufficient random bytes; out is zero \
    on failure and used counts consumed complete draws on every return. Timing may depend on \
    public p,q,g,y, sampling decisions, signing success bits and consumption, not otherwise on \
    secrets. Contract: `VG.Spec.Dsa.randomSignPrevalidatedContract`."
  safety := ["(p_len, q_len) must be (128,20), (256,20), (256,28), (256,32), or (384,32).",
    "key_len must be 3*p_len + 2*q_len; out_len must be 2*q_len.",
    "scratch_len must be at least 16*p_len + 64 words; destroy scratch after use.",
    "The exact key bytes must satisfy validatePrivateKeyBytes p_len q_len key = true. \
      A successful vg_dsa_validate_private_key call establishes this only while the key bytes \
      remain unchanged. Primality remains the caller's responsibility.",
    "Provide fresh independent random octets; never reuse a completed signing tape for \
      another signature."]

end VG.Spec.Dsa
