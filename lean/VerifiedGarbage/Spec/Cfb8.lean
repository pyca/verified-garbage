module

public import VerifiedGarbage.Spec.Cbc

/-!
# CFB with 8-bit segments (NIST SP 800-38A §6.3)

**Trusted** (as every file in `Spec/`). The Cipher Feedback mode,
transcribed from NIST SP 800-38A, *Recommendation for Block Cipher Modes of
Operation: Methods and Techniques* (December 2001); section numbers below
refer to it, with the segment size `s = 8` (CFB8), so each segment is a
byte. It reuses CBC's AES (`Spec/Cbc.lean`).

Both directions use only the forward cipher. Each input block is the one
before it shifted left by a byte, with the last ciphertext byte shifted in,
so a message may be encrypted or decrypted in pieces of any length: CFB8 of
`P₁ … Pₙ` from `IV` is CFB8 of `P₁ … Pₖ` from `IV`, followed by CFB8 of
`Pₖ₊₁ … Pₙ` from the input block after the first piece, the last 16 bytes
of `IV` followed by its ciphertext (`next`). The functions implemented in
assembly take a piece and the block to start from, and leave the one to
continue from; their contracts are in `Spec/Cfb8/Contract.lean`.
-/

@[expose] public section

namespace VG.Spec.Cfb8

open Cbc (Cipher)

/-- §6.3, CFB Encryption of the plaintext segments `P#₁ … P#ₙ` (bytes) with
the initialization vector `IV`, for `s = 8`:
```
I₁ = IV;
Iⱼ = LSB_{b−s}(Iⱼ₋₁) | C#ⱼ₋₁    for j = 2 … n;
Oⱼ = CIPH_K(Iⱼ)                for j = 1, 2 … n;
C#ⱼ = P#ⱼ ⊕ MSB_s(Oⱼ)          for j = 1, 2 … n.
```
(`LSB_{b−s}` of a block drops its first byte, and `MSB_s` is its first
byte; the recursion passes `Iⱼ₊₁` on as the `IV` of the rest.) -/
def encrypt (ciph : Cipher) (iv : List Byte) : List Byte → List Byte
  | [] => []
  | p :: ps => let c := p ^^^ (ciph iv).headD 0; c :: encrypt ciph (iv.tail ++ [c]) ps

/-- §6.3, CFB Decryption of the ciphertext segments `C#₁ … C#ₙ` (bytes)
with the initialization vector `IV`, for `s = 8`:
```
I₁ = IV;
Iⱼ = LSB_{b−s}(Iⱼ₋₁) | C#ⱼ₋₁    for j = 2 … n;
Oⱼ = CIPH_K(Iⱼ)                for j = 1, 2 … n;
P#ⱼ = C#ⱼ ⊕ MSB_s(Oⱼ)          for j = 1, 2 … n.
``` -/
def decrypt (ciph : Cipher) (iv : List Byte) : List Byte → List Byte
  | [] => []
  | c :: cs => (c ^^^ (ciph iv).headD 0) :: decrypt ciph (iv.tail ++ [c]) cs

/-- The input block after the ciphertext segments `cs` from `iv`: the input
block of the next segment, `iv` followed by `cs` without as many bytes at
the start as `cs` has (the last 16 bytes, for a 16-byte `iv`). -/
def next (iv cs : List Byte) : List Byte := (iv ++ cs).drop cs.length

/-! ## With AES -/

/-- AES-CFB8 encryption of the plaintext `pt` under the key `key` (16, 24
or 32 bytes) with the 16-byte `iv`. -/
def aesCfb8Encrypt (key iv pt : List Byte) : List Byte :=
  encrypt (Cbc.aesWith (Aes.rounds (key.length / 4)) (Aes.expandKey key)) iv pt

/-- AES-CFB8 decryption of the ciphertext `ct` under the key `key` (16, 24
or 32 bytes) with the 16-byte `iv`. -/
def aesCfb8Decrypt (key iv ct : List Byte) : List Byte :=
  decrypt (Cbc.aesWith (Aes.rounds (key.length / 4)) (Aes.expandKey key)) iv ct

end VG.Spec.Cfb8
