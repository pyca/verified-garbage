import VerifiedGarbage.Spec.Cbc

/-!
# CTR (NIST SP 800-38A §6.5 and Appendix B.1)

**Trusted** (as every file in `Spec/`). The Counter mode, transcribed from
NIST SP 800-38A, *Recommendation for Block Cipher Modes of Operation:
Methods and Techniques* (December 2001); section numbers below refer to
it. It reuses CBC's blocks, `⊕` and AES (`Spec/Cbc.lean`).

CTR enciphers a sequence of counter blocks `T₁ T₂ …` and XORs the output
blocks with the input. It uses only the forward cipher, and encryption and
decryption are the same function (`crypt`). §6.5 leaves the generation of
the counter blocks to Appendix B; this is its standard incrementing
function (B.1) applied to the whole block (`m = b = 128`):
`Tⱼ₊₁ = [Tⱼ + 1 mod 2¹²⁸]₁₂₈`, the block read as a big-endian integer
(`inc`), wrapping from `1¹²⁸` to `0¹²⁸`. The caller chooses `T₁`, and is
responsible for the uniqueness of the counter blocks across messages that
B.2 requires. The last block may be partial (`Pₙ*`, of `u` bytes), XORed
with `MSB_u(Oₙ)`: `aesCtr` takes a string of any length.

A message may be processed in pieces of whole blocks: CTR of `P₁ … Pₙ`
from `T₁` is CTR of `P₁ … Pₖ` from `T₁`, followed by CTR of
`Pₖ₊₁ … Pₙ` from `Tₖ₊₁` (`next`). The function implemented in assembly
takes a piece of whole blocks and the counter block to start from, and
leaves the one to continue from; its contract is in
`Spec/Ctr/Contract.lean`.
-/

namespace VG.Spec.Ctr

open Cbc (Cipher xor)

/-- A block of bytes as a big-endian integer (§2.1, the bit string as a
binary number, most significant bit first). -/
def toNat (x : List Byte) : Nat := x.foldl (fun a b => 256 * a + b.toNat) 0

/-- `[x]ₖ` in bytes: the `k`-byte big-endian representation of `x mod 256ᵏ`. -/
def ofNat (x k : Nat) : List Byte := (List.range k).map fun i => BitVec.ofNat 8 (x / 256 ^ (k - 1 - i))

/-- Appendix B.1, the standard incrementing function on the whole 16-byte
block: `[X + 1 mod 2¹²⁸]₁₂₈`. -/
def inc (t : List Byte) : List Byte := ofNat (toNat t + 1) 16

/-- The counter blocks `T₁ … Tₙ` from `T₁ = t`: `Tⱼ₊₁ = inc(Tⱼ)`. -/
def counters (t : List Byte) : Nat → List (List Byte)
  | 0 => []
  | n + 1 => t :: counters (inc t) n

/-- §6.5, CTR Encryption (and Decryption, which is the same) of the whole
blocks `X₁ … Xₙ` from the counter block `T₁ = t`:
```
Oⱼ = CIPH_K(Tⱼ)  for j = 1, 2 … n;
Yⱼ = Xⱼ ⊕ Oⱼ     for j = 1, 2 … n.
```
-/
def crypt (ciph : Cipher) (t : List Byte) (xs : List (List Byte)) : List (List Byte) :=
  List.zipWith xor xs ((counters t xs.length).map ciph)

/-- The counter block to continue from after `n` blocks from `t`:
`Tₙ₊₁`, the `n`-th increment of `t` (see above). -/
def next (t : List Byte) (n : Nat) : List Byte := Nat.repeat inc n t

/-! ## With AES -/

/-- AES-CTR encryption or decryption of `x` (of any length) under the key
`key` (16, 24 or 32 bytes) from the 16-byte initial counter block `t`: `x`
XORed with the output blocks, the last one truncated to what is left of
`x` (§6.5, `Cₙ* = Pₙ* ⊕ MSB_u(Oₙ)`). -/
def aesCtr (key t x : List Byte) : List Byte :=
  let ciph := Cbc.aesWith (Aes.rounds (key.length / 4)) (Aes.expandKey key)
  List.zipWith (· ^^^ ·) x ((counters t ((x.length + 15) / 16)).map ciph).flatten

end VG.Spec.Ctr
