module

public import VerifiedGarbage.Spec.Cbc

/-!
# CFB with 128-bit segments (NIST SP 800-38A §6.3)

**Trusted** (as every file in `Spec/`). The Cipher Feedback mode,
transcribed from NIST SP 800-38A, *Recommendation for Block Cipher Modes of
Operation: Methods and Techniques* (December 2001); section numbers below
refer to it, with the segment size `s` the block size (CFB128 for AES), so
each segment is a whole block. It reuses CBC's blocks, `⊕`, AES and the
chaining value to continue from (`Spec/Cbc.lean`).

Both directions use only the forward cipher. Each ciphertext block is the
input block of the next, so a message may be encrypted or decrypted in
pieces of whole blocks: CFB of `P₁ … Pₙ` from `IV` is CFB of `P₁ … Pₖ` from
`IV`, followed by CFB of `Pₖ₊₁ … Pₙ` from `Cₖ`, the last ciphertext block of
the first piece (`Cbc.next`). The functions implemented in assembly take a
piece and the block to start from, and leave the one to continue from;
their contracts are in `Spec/Cfb/Contract.lean`.
-/

@[expose] public section

namespace VG.Spec.Cfb

open Cbc (Cipher xor)

/-- §6.3, CFB Encryption of the plaintext blocks `P₁ … Pₙ` with the
initialization vector `IV`, for `s = b`:
```
I₁ = IV;
Iⱼ = Cⱼ₋₁           for j = 2 … n;
Oⱼ = CIPH_K(Iⱼ)     for j = 1, 2 … n;
Cⱼ = Pⱼ ⊕ Oⱼ        for j = 1, 2 … n.
```
(Each ciphertext block is the input block of the next, so the recursion
passes `Cⱼ` on as the `IV` of the rest.) -/
def encrypt (ciph : Cipher) (iv : List Byte) : List (List Byte) → List (List Byte)
  | [] => []
  | p :: ps => let c := xor p (ciph iv); c :: encrypt ciph c ps

/-- §6.3, CFB Decryption of the ciphertext blocks `C₁ … Cₙ` with the
initialization vector `IV`, for `s = b`:
```
I₁ = IV;
Iⱼ = Cⱼ₋₁           for j = 2 … n;
Oⱼ = CIPH_K(Iⱼ)     for j = 1, 2 … n;
Pⱼ = Cⱼ ⊕ Oⱼ        for j = 1, 2 … n.
``` -/
def decrypt (ciph : Cipher) (iv : List Byte) : List (List Byte) → List (List Byte)
  | [] => []
  | c :: cs => xor c (ciph iv) :: decrypt ciph c cs

/-! ## With AES -/

/-- AES-CFB128 encryption of the plaintext `pt` (a multiple of 16 bytes)
under the key `key` (16, 24 or 32 bytes) with the 16-byte `iv`. -/
def aesCfbEncrypt (key iv pt : List Byte) : List Byte :=
  (encrypt (Cbc.aesWith (Aes.rounds (key.length / 4)) (Aes.expandKey key)) iv (Cbc.blocks pt)).flatten

/-- AES-CFB128 decryption of the ciphertext `ct` (a multiple of 16 bytes)
under the key `key` (16, 24 or 32 bytes) with the 16-byte `iv`. -/
def aesCfbDecrypt (key iv ct : List Byte) : List Byte :=
  (decrypt (Cbc.aesWith (Aes.rounds (key.length / 4)) (Aes.expandKey key)) iv (Cbc.blocks ct)).flatten

end VG.Spec.Cfb
