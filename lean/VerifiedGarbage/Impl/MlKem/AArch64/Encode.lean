module

public import VerifiedGarbage.Impl.MlKem.AArch64.Cbd16
public import VerifiedGarbage.Impl.MlKem.AArch64.Codec16
import VerifiedGarbage.Impl.MlKem.AArch64.Ntt

/-!
# ML-KEM on AArch64: encoding, decoding and sampling from bytes

* `encode12(f = x0, out = x1)`: `ByteEncode₁₂`, 3 bytes per pair of
  coefficients `f₀, f₁`: `f₀`, `⌊f₀ / 2⁸⌋ + 2⁴ f₁` and `⌊f₁ / 2⁴⌋`, each
  packed eight coefficients at a time and stored as twelve contiguous bytes.
* `decode12(b = x0, f = x1)`: `ByteDecode₁₂`, 2 coefficients per 3 bytes
  `b₀, b₁, b₂`: `b₀ + 2⁸ (b₁ mod 2⁴)` and `⌊b₁ / 2⁴⌋ + 2⁴ b₂`, each less than
  `2¹²` and reduced modulo `q` with unsigned vector minimum.
* `cbd2(b = x0, f = x1)`: `SamplePolyCBD₂`, 2 coefficients per byte `b`:
  `s = (b & 0x55) + ((b >> 1) & 0x55)` holds the sums of the pairs of bits
  of `b` in its four 2-bit fields `x₀, y₀, x₁, y₁`, and coefficient `j` is
  `(xⱼ + q - yⱼ) mod q`.

* `checkEk(ek = x0) -> w0`: the modulus check of ML-KEM-768 (and, with
  `checkEkWith 512`, of ML-KEM-1024): for each of the 384 (512) groups of
  3 bytes of `ek[0 : 1152]` (`ek[0 : 1536]`), its two 12-bit fields `f`
  (as in `decode12`), each counted in `x10` if `q - 1 - f` is negative;
  returns 1 if the count is 0 (`x10 - 1` negative), and 0 otherwise.

Every address and branch depends only on the pointers.
-/

@[expose] public section

namespace VG.Impl.MlKem.AArch64

open VG.AArch64

/-! ## `encode12` -/

/-- Eight coefficients packed into twelve contiguous bytes per iteration. -/
def encode12 : Prog isa := Codec16.enc

/-! ## `decode12` -/

/-- Twelve bytes decoded into eight canonical coefficients per iteration. -/
def decode12 : Prog isa := Codec16.dec

/-! ## `cbd2` -/

/-- Sixteen input bytes per iteration, with two centered coefficients per byte. -/
def cbd2 : Prog isa := Cbd16.code

/-! ## `checkEk` -/

def checkEkBody : List Instr :=
  [.ldrb .x12 .x0 0, .ldrb .x13 .x0 1,
    .logic .and .x .x15 .x13 .x14, .lsl .x .x15 .x15 8, .add .x .x15 .x15 .x12,
    .sub .x .x15 .x9 .x15, .lsr .x .x15 .x15 63, .add .x .x10 .x10 .x15,
    .ldrb .x12 .x0 2,
    .lsr .x .x13 .x13 4, .lsl .x .x12 .x12 4, .add .x .x13 .x13 .x12,
    .sub .x .x13 .x9 .x13, .lsr .x .x13 .x13 63, .add .x .x10 .x10 .x13,
    .addImm .x .x0 .x0 3, .subImm .x .x11 .x11 1]

/-- The check of the `n` groups of a key's `3n` bytes. -/
def checkEkWith (n : Nat) : Prog isa :=
  .seq (.block [.movz .x .x9 3328 0, .movz .x .x10 0 0, .movz .x .x11 (BitVec.ofNat 16 n) 0,
      .movz .x .x14 15 0]) <|
  .seq (.loop (.block checkEkBody) (.nonzero .x .x11))
    (.block [.subImm .x .x0 .x10 1, .lsr .x .x0 .x0 63])

/-- The check of ML-KEM-768 (`k = 3`): 384 groups. -/
abbrev checkEk : Prog isa := checkEkWith 384

end VG.Impl.MlKem.AArch64
