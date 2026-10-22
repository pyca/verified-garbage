module

public import VerifiedGarbage.Spec.EcKey.Compressed
public import VerifiedGarbage.Spec.EcKey.Generic

/-!
# Compressed public-key conversion contracts, on every target

**Trusted** (as every file in `Spec/`). Each `EcKey.Instance` has two
conversion APIs: validate and compress an uncompressed public key, or
validate and decompress a compressed one. Success returns exactly 1 and
writes the other encoding; failure returns exactly 0 and clears the entire
output. Decompression must succeed whenever a matching finite curve point
exists, rather than merely checking any root an implementation happens to
find. Neither API accepts infinity or hybrid encodings.

Inputs are public, as in standalone public-key validation: timing may
depend on every input byte. The 8 KiB scratch buffer needs no initial
contents and is unspecified on return. `Sig.contract` supplies memory
validity, separation, preservation of read-only inputs and ABI obligations.
No existing artifact is registered or changed by this specification.
-/

@[expose] public section

namespace VG.Spec.EcKey.Instance

variable (I : Instance)

/-- `(out: *mut [u8; len + 1], public: *const [u8; 2 len + 1],
scratch: *mut [u64; 1024]) -> u32`. -/
def compressPublicKeySig : Sig where
  params := [("out", .array true .u8 (I.curve.len + 1)),
    ("public", .array false .u8 (2 * I.curve.len + 1)),
    ("scratch", .array true .u64 scratchWords)]
  ret := some .u32

/-- `(out: *mut [u8; 2 len + 1], public: *const [u8; len + 1],
scratch: *mut [u64; 1024]) -> u32`. -/
def decompressPublicKeySig : Sig where
  params := [("out", .array true .u8 (2 * I.curve.len + 1)),
    ("public", .array false .u8 (I.curve.len + 1)),
    ("scratch", .array true .u64 scratchWords)]
  ret := some .u32

/-- Validate and compress, or return zero and clear the output. -/
def compressPublicKeyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  I.compressPublicKeySig.contract A
    (post := fun out pk _scratch m m' r =>
      match compressPublicKey I.curve (bytesAt m pk (2 * I.curve.len + 1)) with
      | some bs => r = 1 ∧ bytesAt m' out (I.curve.len + 1) = bs
      | none => r = 0 ∧ bytesAt m' out (I.curve.len + 1) = List.replicate (I.curve.len + 1) 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun _out pk _scratch m =>
      (bytesAt m pk (2 * I.curve.len + 1)).map (·.toNat))

/-- Recover a validated finite point with the encoded `x` and `y` parity,
or, exactly when no such point exists, return zero and clear the output. -/
def decompressPublicKeyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  I.decompressPublicKeySig.contract A
    (post := fun out pk _scratch m m' r =>
      let bs := bytesAt m pk (I.curve.len + 1)
      (r = 1 ∧ ∃ Q, matchesCompressedPublicKey I.curve bs Q ∧
        bytesAt m' out (2 * I.curve.len + 1) = encodePoint Q) ∨
      (r = 0 ∧ (¬ ∃ Q, matchesCompressedPublicKey I.curve bs Q) ∧
        bytesAt m' out (2 * I.curve.len + 1) = List.replicate (2 * I.curve.len + 1) 0))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out pk _scratch m =>
      (bytesAt m pk (I.curve.len + 1)).map (·.toNat))

/-- `vg_ec_<name>_compress_public_key` on every target. -/
def compressPublicKeyApi : Api where
  module := s!"ec_{I.name}_compressed"
  name := s!"vg_ec_{I.name}_compress_public_key"
  sig := I.compressPublicKeySig
  writeArgs := true
  contracts := some fun A stack => I.compressPublicKeyContract A stack
  summary := s!"Validate and compress a {I.title} public key (SEC 1 §§2.3.3–2.3.4, \
    SP 800-56A §5.6.2.3.3): reads `04` then `x` and `y` in {I.curve.len} bytes each, \
    most significant first; checks both coordinates below the field prime and the curve \
    equation; writes `02` for even `y` or `03` for odd `y`, then `x` in {I.curve.len} bytes, \
    and returns 1. On invalid input, writes {I.curve.len + 1} zero bytes and returns 0. \
    Rejects infinity and hybrid encodings.\n\n\
    Contract: `VG.Spec.EcKey.Instance.compressPublicKeyContract`. The input is public: \
    timing may depend on the pointers and the contents of `public`."
  safety := ["The contents of `scratch` on return are unspecified; the caller may reuse or \
    destroy them."]

/-- `vg_ec_<name>_decompress_public_key` on every target. -/
def decompressPublicKeyApi : Api where
  module := s!"ec_{I.name}_compressed"
  name := s!"vg_ec_{I.name}_decompress_public_key"
  sig := I.decompressPublicKeySig
  writeArgs := true
  contracts := some fun A stack => I.decompressPublicKeyContract A stack
  summary := s!"Validate and decompress a {I.title} public key (SEC 1 §2.3.4, \
    SP 800-56A §5.6.2.3.3): reads `02` or `03` followed by `x` in {I.curve.len} bytes, \
    most significant first; checks `x` below the field prime and recovers a coordinate `y` \
    satisfying the curve equation with even parity for `02`, odd for `03`. Writes `04` \
    followed by `x` and `y` in {I.curve.len} bytes each and returns 1. If no such finite \
    point exists, writes {2 * I.curve.len + 1} zero bytes and returns 0. Rejects infinity \
    and hybrid encodings. The curve has cofactor one, so no subgroup multiplication is \
    required.\n\n\
    Contract: `VG.Spec.EcKey.Instance.decompressPublicKeyContract`. The input is public: \
    timing may depend on the pointers and the contents of `public`."
  safety := ["The contents of `scratch` on return are unspecified; the caller may reuse or \
    destroy them."]

end VG.Spec.EcKey.Instance
