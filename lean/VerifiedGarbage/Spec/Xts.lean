import VerifiedGarbage.Spec.Cbc

/-!
# XTS-AES (IEEE Std 1619-2007, NIST SP 800-38E)

**Trusted** (as every file in `Spec/`). The XTS-AES mode of IEEE Std
1619-2007, *Standard for Cryptographic Protection of Data on Block-Oriented
Storage Devices*, which NIST SP 800-38E approves; section numbers below
refer to IEEE 1619. It reuses CBC's blocks, `⊕` and AES (`Spec/Cbc.lean`).

The key is `Key1 ‖ Key2`, two AES keys of the same length (§5.1): `Key1`
encrypts the data, `Key2` the tweak value `i` (16 bytes), giving
`T = AES-enc(Key2, i)`. Block `j` of a data unit is encrypted with the tweak
`T ⊗ αʲ` (§5.3.1): its bytes are the coefficients of a polynomial over
GF(2), the first byte least significant (§5.2), and `⊗ α` (`mulAlpha`) is
multiplication by the primitive element `x` modulo `x¹²⁸ + x⁷ + x² + x + 1`.
A data unit of at least 16 bytes whose length is not a multiple of 16 ends
with ciphertext stealing (§5.3.2, §5.4.2; `aesXtsEncrypt`,
`aesXtsDecrypt`).

The functions implemented in assembly encrypt or decrypt whole blocks with
`Key1`, from a tweak `T ⊗ αʲ` they are given, and leave the tweak to
continue from (`next`): XTS of the first `k + 1` blocks is XTS of the first
`k`, followed by the block with the next tweak. Their contracts are in
`Spec/Xts/Contract.lean`; computing `T` and ciphertext stealing are the
caller's.
-/

namespace VG.Spec.Xts

open Cbc (Cipher xor)

/-- §5.2, multiplication by a primitive element `α` of the 16-byte tweak
`a₀ … a₁₅`:
```
Cin ← 0
for j ← 0 to 15:
  Cout ← (aⱼ >> 7) & 1
  aⱼ ← ((aⱼ << 1) + Cin) mod 256
  Cin ← Cout
if Cout: a₀ ← a₀ ⊕ 135
```
`step` runs the loop from byte `j` with the carry `Cin`, returning the bytes
from `j` on and the last `Cout`. -/
def mulAlpha (a : List Byte) : List Byte :=
  let rec step : List Byte → Bool → List Byte × Bool
    | [], cin => ([], cin)
    | aj :: rest, cin =>
      let cout := aj.msb
      let (rest', c) := step rest cout
      (((aj <<< 1) + (if cin then 1 else 0)) :: rest', c)
  match step a false with
  | (a₀ :: rest, true) => (a₀ ^^^ 135) :: rest
  | (bs, _) => bs

/-- The tweaks `T ⊗ αʲ` of blocks `j = 0 … n − 1`, from `T = t`. -/
def tweaks (t : List Byte) : Nat → List (List Byte)
  | 0 => []
  | n + 1 => t :: tweaks (mulAlpha t) n

/-- The tweak to continue from after `n` blocks from `t`: `t ⊗ αⁿ`. -/
def next (t : List Byte) (n : Nat) : List Byte := Nat.repeat mulAlpha n t

/-- §5.3.1, XTS-AES-blockEnc of the block `P` with the tweak `T ⊗ αʲ` (here
`t`):
```
PP ← P ⊕ T
CC ← AES-enc(Key1, PP)
C ← CC ⊕ T
```
(and, with `AES-dec(Key1, ·)` for `ciph`, §5.4.1's XTS-AES-blockDec). -/
def block (ciph : Cipher) (t p : List Byte) : List Byte := xor (ciph (xor p t)) t

/-- XTS of whole blocks `X₀ … Xₙ₋₁` from the tweak `T = t`, block `j` with
`T ⊗ αʲ`: encryption for `AES-enc(Key1, ·)`, decryption for
`AES-dec(Key1, ·)` (§5.3.2 and §5.4.2 without stealing). -/
def crypt (ciph : Cipher) (t : List Byte) (xs : List (List Byte)) : List (List Byte) :=
  List.zipWith (block ciph) (tweaks t xs.length) xs

/-! ## With AES -/

/-- `AES-enc(Key1, ·)`, `AES-dec(Key1, ·)` and `T = AES-enc(Key2, i)` for the
key `Key1 ‖ Key2` (32, 48 or 64 bytes). -/
def keys (key i : List Byte) : Cipher × Cipher × List Byte :=
  let k1 := key.take (key.length / 2)
  let k2 := key.drop (key.length / 2)
  let w1 := Aes.expandKey k1
  let nr := Aes.rounds (k1.length / 4)
  (Cbc.aesWith nr w1, Cbc.aesInvWith nr w1, Cbc.aesWith (Aes.rounds (k2.length / 4)) (Aes.expandKey k2) i)

/-- §5.3.2, XTS-AES encryption of the data unit `p` (at least 16 bytes) with
the key `Key1 ‖ Key2` and the tweak value `i`; `none` if `p` is shorter. With
`m` whole blocks and `b` bytes left: blocks `0 … m − 2` are encrypted with
their tweaks, then
```
CC ← XTS-AES-blockEnc(Key, Pₘ₋₁, i, m − 1)
Cₘ ← MSB_b(CC)
CP ← LSB_(128−b)(CC)
PP ← Pₘ ‖ CP
Cₘ₋₁ ← XTS-AES-blockEnc(Key, PP, i, m)
```
and the result is `C₀ ‖ … ‖ Cₘ₋₁ ‖ Cₘ` (if `b = 0`, every block is encrypted
with its tweak). -/
def aesXtsEncrypt (key i p : List Byte) : Option (List Byte) :=
  if p.length < 16 then none else
  let (enc, _, t) := keys key i
  let m := p.length / 16
  let b := p.length % 16
  if b = 0 then some (crypt enc t (Cbc.blocks p)).flatten else
  let head := (crypt enc t (Cbc.blocks (p.take (16 * (m - 1))))).flatten
  let cc := block enc (next t (m - 1)) ((p.drop (16 * (m - 1))).take 16)
  let pp := p.drop (16 * m) ++ cc.drop b
  some (head ++ block enc (next t m) pp ++ cc.take b)

/-- §5.4.2, XTS-AES decryption of the data unit `c` (at least 16 bytes) with
the key `Key1 ‖ Key2` and the tweak value `i`; `none` if `c` is shorter. With
`m` whole blocks and `b` bytes left: blocks `0 … m − 2` are decrypted with
their tweaks, then
```
PP ← XTS-AES-blockDec(Key, Cₘ₋₁, i, m)
Pₘ ← MSB_b(PP)
CP ← LSB_(128−b)(PP)
CC ← Cₘ ‖ CP
Pₘ₋₁ ← XTS-AES-blockDec(Key, CC, i, m − 1)
```
and the result is `P₀ ‖ … ‖ Pₘ₋₁ ‖ Pₘ` (if `b = 0`, every block is decrypted
with its tweak). -/
def aesXtsDecrypt (key i c : List Byte) : Option (List Byte) :=
  if c.length < 16 then none else
  let (_, dec, t) := keys key i
  let m := c.length / 16
  let b := c.length % 16
  if b = 0 then some (crypt dec t (Cbc.blocks c)).flatten else
  let head := (crypt dec t (Cbc.blocks (c.take (16 * (m - 1))))).flatten
  let pp := block dec (next t m) ((c.drop (16 * (m - 1))).take 16)
  let cc := c.drop (16 * m) ++ pp.drop b
  some (head ++ block dec (next t (m - 1)) cc ++ pp.take b)

end VG.Spec.Xts
