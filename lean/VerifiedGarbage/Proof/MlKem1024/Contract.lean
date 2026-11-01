module

public import VerifiedGarbage.Proof.MlKem.PolyContract

/-!
# ML-KEM-1024: the contracts of its internal functions

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.

The polynomial primitives of `Proof/MlKem/PolyContract.lean` serve every
parameter set but for compression: `vg_mlkem_compress_encode` and
`vg_mlkem_decode_decompress` take the widths of ML-KEM-768 (1, 4 and 10), and
ML-KEM-1024 compresses to 11 (`d_u`) and 5 (`d_v`), which
`vg_mlkem1024_compress_encode` and `vg_mlkem1024_decode_decompress` take.
(They have a name of their own, not `vg_mlkem_compress_encode_…`: a
function named after another with a suffix and the same signature is a
variant of it to `ci/check_variants.py`.)
-/

@[expose] public section

namespace VG.Proof.MlKem1024

open VG.Spec VG.Spec.MlKem VG.Proof.MlKem
open Sha3 (bytesAt)

/-- The values of `d` that ML-KEM-1024 compresses to, but ML-KEM-768 does
not (`d_v` and `d_u`, Table 2). -/
def compressWidths : List Nat := [5, 11]

/-- `vg_mlkem1024_compress_encode(f: *const [u32; 256], d: u32, out: *mut u8, len: usize)`. -/
def compressEncodeSig : Sig where
  params := [("f", .array false .u32 256), ("d", .int .u32 true), ("out", .slice true .u8 "len")]

/-- If `d` is in `compressWidths`, `len = 32d` and the polynomial at `f` is
reduced: writes `ByteEncode_d(Compress_d(f))` to `out`. -/
def compressEncodeContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  compressEncodeSig.contract A
    (pre := fun f d _out len m =>
      d.toNat ∈ compressWidths ∧ len.toNat = 32 * d.toNat ∧ Reduced m f)
    (post := fun f d out len m m' _ =>
      bytesAt m' out len.toNat = compressEncode d.toNat (polyAt m f))
    (writeArgs := true)
    (stack := stack)

/-- `vg_mlkem1024_decode_decompress(b: *const u8, len: usize, d: u32, f: *mut [u32; 256])`. -/
def decodeDecompressSig : Sig where
  params := [("b", .slice false .u8 "len"), ("d", .int .u32 true), ("f", .array true .u32 256)]

/-- If `d` is in `compressWidths` and `len = 32d`: writes
`Decompress_d(ByteDecode_d(B))` of the `len` bytes `B` at `b` to `f`,
reduced. -/
def decodeDecompressContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  decodeDecompressSig.contract A
    (pre := fun _b len d _f _m => d.toNat ∈ compressWidths ∧ len.toNat = 32 * d.toNat)
    (post := fun b len d f m m' _ =>
      PolyIs m' f (decodeDecompress d.toNat (bytesAt m b len.toNat)))
    (writeArgs := true)
    (stack := stack)

end VG.Proof.MlKem1024
