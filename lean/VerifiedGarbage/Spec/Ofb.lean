module

public import VerifiedGarbage.Spec.Cbc

/-!
# OFB (NIST SP 800-38A §6.4)

**Trusted** (as every file in `Spec/`). The Output Feedback mode,
transcribed from NIST SP 800-38A, *Recommendation for Block Cipher Modes of
Operation: Methods and Techniques* (December 2001); section numbers below
refer to it. It reuses CBC's blocks, `⊕` and AES (`Spec/Cbc.lean`).

OFB enciphers the initialization vector repeatedly, `Oⱼ = CIPH_K(Oⱼ₋₁)`
with `O₀ = IV`, and XORs the output blocks `O₁ O₂ …` with the input. It
uses only the forward cipher, and encryption and decryption are the same
function (`crypt`). The last block may be partial (`Pₙ*`, of `u` bytes),
XORed with `MSB_u(Oₙ)`: `aesOfb` takes a string of any length.

A message may be processed in pieces of whole blocks: OFB of
`P₁ … Pₙ` from `IV` is OFB of `P₁ … Pₖ` from `IV`, followed by OFB of
`Pₖ₊₁ … Pₙ` from `Oₖ`, the last output block of the first piece (`next`).
The function implemented in assembly takes a piece of whole blocks and the
block to start from, and leaves the one to continue from; its contract is
in `Spec/Ofb/Contract.lean`.
-/

@[expose] public section

namespace VG.Spec.Ofb

open Cbc (Cipher xor)

/-- §6.4, the output blocks `O₁ … Oₙ` from the initialization vector `IV`:
```
I₁ = IV;
Iⱼ = Oⱼ₋₁       for j = 2 … n;
Oⱼ = CIPH_K(Iⱼ) for j = 1, 2 … n.
```
-/
def outputs (ciph : Cipher) (iv : List Byte) : Nat → List (List Byte)
  | 0 => []
  | n + 1 => let o := ciph iv; o :: outputs ciph o n

/-- §6.4, OFB Encryption (and Decryption, which is the same) of the whole
blocks `X₁ … Xₙ` from `IV`: `Yⱼ = Xⱼ ⊕ Oⱼ`. -/
def crypt (ciph : Cipher) (iv : List Byte) (xs : List (List Byte)) : List (List Byte) :=
  List.zipWith xor xs (outputs ciph iv xs.length)

/-- The block to continue from after `n` blocks from `iv`: `Oₙ`, or `iv` if
`n = 0` (see above). -/
def next (ciph : Cipher) (iv : List Byte) (n : Nat) : List Byte := (outputs ciph iv n).getLastD iv

/-! ## With AES -/

/-- AES-OFB encryption or decryption of `x` (of any length) under the key
`key` (16, 24 or 32 bytes) with the 16-byte `iv`: `x` XORed with the
output blocks, the last one truncated to what is left of `x` (§6.4,
`Cₙ* = Pₙ* ⊕ MSB_u(Oₙ)`). -/
def aesOfb (key iv x : List Byte) : List Byte :=
  let ciph := Cbc.aesWith (Aes.rounds (key.length / 4)) (Aes.expandKey key)
  List.zipWith (· ^^^ ·) x (outputs ciph iv ((x.length + 15) / 16)).flatten

end VG.Spec.Ofb
