module

import VerifiedGarbage.Proof.MlKem.Compress
public import VerifiedGarbage.Spec.MlKem.Contract1024
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.MlKem.PolyContract

/-! ### `MlKem1024.Contract`, which this module and modules that import it used -/

section

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
function named after another with a suffix and the same signature is an
implementation of it to its dispatcher, `Rust.groupsOf`.)
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

end

end

/-!
# ML-KEM-1024: Compress and Decompress without division, for every target

The analog of `Compress.lean` for the widths only ML-KEM-1024 compresses to
(`Proof.MlKem1024.compressWidths`: `d_v = 5` and `d_u = 11`), with a 32-bit
multiply-low, an addition and shifts:

* `Compress_d(x) = ((x · M_d + 261888) >> 19) mod 2ᵈ` for every `x < q`,
  with `M₅ = 5040` and `M₁₁ = 322542` (`compressMul1024`); the intermediate
  value is less than `2³⁰` (`compress1024_eq`, `compress1024_arg_lt`). The
  shift is that of `Compress.lean`; the addend `2¹⁸ - 2⁸` (not its
  `2¹⁸ - 64`, which is too large for `d = 11`) serves both widths.
* `Decompress_d(y) = (q · y + 2ᵈ⁻¹) >> d` for every `y < 2ᵈ`, which is less
  than `q` (`decompress1024_val`).

Both use `Compress.lean`'s kernel check (`compress_formula`) and decompress
formula (`decompress_val_of_le`).

The compress formula is checked for each of the `q` inputs by the kernel.
-/

@[expose] public section

namespace VG.Proof.MlKem

open VG.Spec.MlKem

/-- The multiplier `M_d` of the compress formula of ML-KEM-1024: 5040 and
322542 for `d` = 5 and 11. -/
def compressMul1024 (d : Nat) : Nat := if d = 5 then 5040 else 322542

/-- The addend of the compress formula of ML-KEM-1024, `2¹⁸ - 2⁸`. -/
def compressAdd1024 : Nat := 261888

theorem mem_compressWidths1024 {d : Nat} (hd : d ∈ Proof.MlKem1024.compressWidths) :
    d = 5 ∨ d = 11 := by
  simpa [Proof.MlKem1024.compressWidths] using hd

private theorem compress5 (x : Nat) (hx : x < 3329) :
    roundDiv (2 ^ 5 * x) 3329 % 2 ^ 5 = (x * 5040 + 261888) / 2 ^ 19 % 2 ^ 5 :=
  compress_formula (by decide +kernel) x hx

private theorem compress11 (x : Nat) (hx : x < 3329) :
    roundDiv (2 ^ 11 * x) 3329 % 2 ^ 11 = (x * 322542 + 261888) / 2 ^ 19 % 2 ^ 11 :=
  compress_formula (by decide +kernel) x hx

/-- `Compress_d(x)` with a multiplication, an addition and a shift, for `d`
in ML-KEM-1024's `compressWidths`. -/
theorem compress1024_eq {d : Nat} (hd : d ∈ Proof.MlKem1024.compressWidths) (x : Zq) :
    compress d x = (x.val * compressMul1024 d + compressAdd1024) / 2 ^ 19 % 2 ^ d := by
  rcases mem_compressWidths1024 hd with rfl | rfl
  · exact compress5 x.val x.isLt
  · exact compress11 x.val x.isLt

/-- The value shifted in `compress1024_eq` fits in 30 bits. -/
theorem compress1024_arg_lt {d : Nat} (hd : d ∈ Proof.MlKem1024.compressWidths) (x : Zq) :
    x.val * compressMul1024 d + compressAdd1024 < 2 ^ 30 := by
  have := val_lt x
  rcases mem_compressWidths1024 hd with rfl | rfl
  · show x.val * 5040 + 261888 < 2 ^ 30; omega_using [this]
  · show x.val * 322542 + 261888 < 2 ^ 30; omega_using [this]

/-- For `d = 11` the shifted value is less than `2¹¹`, so the reduction
modulo `2¹¹` of `compress1024_eq` does nothing. -/
theorem compress11_eq (x : Zq) : compress 11 x = (x.val * 322542 + 261888) / 2 ^ 19 := by
  rw [compress1024_eq (d := 11) (by decide), Nat.mod_eq_of_lt (by
    have := val_lt x; show (x.val * 322542 + 261888) / 2 ^ 19 < 2 ^ 11; omega_using [this])]
  rfl

/-- `Decompress_d(y)` with a multiplication, an addition and a shift, for
`d` in ML-KEM-1024's `compressWidths` and `y < 2ᵈ`: the result is less than
`q`. -/
theorem decompress1024_val {d : Nat} (hd : d ∈ Proof.MlKem1024.compressWidths) {y : Nat}
    (hy : y < 2 ^ d) :
    (decompress d y).val = (q * y + 2 ^ (d - 1)) / 2 ^ d ∧ (q * y + 2 ^ (d - 1)) / 2 ^ d < q :=
  decompress_val_of_le (by rcases mem_compressWidths1024 hd with rfl | rfl <;> decide)
    (by rcases mem_compressWidths1024 hd with rfl | rfl <;> decide) hy

end VG.Proof.MlKem
