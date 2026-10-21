module

public import VerifiedGarbage.Spec.EcKey.Generic

/-!
# Standalone validation of encoded elliptic curve public keys

**Trusted** (as every file in `Spec/`). This adds an exported contract for
the existing `EcKey.decodePublicKey`, without changing that specification.
For each `EcKey.Instance`, `vg_ec_<name>_validate_public_key` takes an
uncompressed SEC 1 octet string and returns exactly 1 if it decodes to a
valid public key, and exactly 0 otherwise.

The contract includes the encoding check and the decoding of both
coordinates, as well as their bounds and the curve equation. It requires
no caller-provided curve constants or decoded coordinates. The input is
public: its bytes may affect timing, as in ECDSA verification. `scratch`
is 8 KiB of working space, with no required initial contents; its final
contents are unspecified. Memory validity, separation, preservation of
read-only inputs, and the ABI obligations come from `Sig.contract`.
-/

@[expose] public section

namespace VG.Spec.EcKey.Instance

variable (I : Instance)

/-- `(public: *const [u8; 2 len + 1], scratch: *mut [u64; 1024]) -> u32`. -/
def validatePublicKeySig : Sig where
  params := [("public", .array false .u8 (2 * I.curve.len + 1)),
    ("scratch", .array true .u64 scratchWords)]
  ret := some .u32

/-- Returns 1 exactly when the encoded public key is accepted by
`decodePublicKey`, and 0 otherwise. The public key's bytes may affect timing. -/
def validatePublicKeyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  I.validatePublicKeySig.contract A
    (post := fun pk _scratch m _m' r =>
      r = if (decodePublicKey I.curve (bytesAt m pk (2 * I.curve.len + 1))).isSome then 1 else 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun pk _scratch m =>
      (bytesAt m pk (2 * I.curve.len + 1)).map (·.toNat))

/-- `vg_ec_<name>_validate_public_key` on every target. -/
def validatePublicKeyApi : Api where
  module := s!"ec_{I.name}_validate"
  name := s!"vg_ec_{I.name}_validate_public_key"
  sig := I.validatePublicKeySig
  writeArgs := true
  contracts := some fun A stack => I.validatePublicKeyContract A stack
  summary := s!"{I.title} public-key validation (SEC 1 §2.3.4, SP 800-56A §5.6.2.3.3): \
    returns 1 if `public` is a valid public key in the uncompressed form of SEC 1 \
    §2.3.3 (`04`, then `x` and `y` in {I.curve.len} bytes each, most significant first), \
    and 0 otherwise. Checks the encoding tag, both coordinates below the field prime \
    and the curve equation; rejects infinity and compressed or hybrid encodings. \
    The curve has cofactor one, so no scalar multiplication is required.\n\n\
    Contract: `VG.Spec.EcKey.Instance.validatePublicKeyContract`. The input is public: \
    timing may depend on the pointers and the contents of `public`."
  safety := ["The contents of `scratch` on return are unspecified; the caller may reuse or \
    destroy them."]

end VG.Spec.EcKey.Instance
