module

public import VerifiedGarbage.Spec.Aes

/-!
# CBC (NIST SP 800-38A §6.2)

**Trusted** (as every file in `Spec/`). The Cipher Block Chaining mode,
transcribed from NIST SP 800-38A, *Recommendation for Block Cipher Modes of
Operation: Methods and Techniques* (December 2001); section numbers below
refer to it. §6.2 defines it on `n` whole blocks, with no padding (the
plaintext's padding, §6 and Appendix A, is the caller's): every string here
is a list of whole blocks.

CBC is defined here for any block cipher, given as a function on blocks
(`Cipher`): the forward function `CIPH_K` for encryption, and the inverse
function `CIPH⁻¹_K` for decryption. `aesCbcEncrypt` and `aesCbcDecrypt` are
CBC with AES (FIPS 197, `Spec/Aes.lean`), whose blocks are 16 bytes.

A message may be encrypted or decrypted in pieces of whole blocks: CBC of
`P₁ … Pₙ` from `IV` is CBC of `P₁ … Pₖ` from `IV`, followed by CBC of
`Pₖ₊₁ … Pₙ` from `Cₖ`, the last ciphertext block of the first piece
(`next`): `Cₖ₊₁` is `CIPH_K(Pₖ₊₁ ⊕ Cₖ)` and `Pₖ₊₁` is
`CIPH⁻¹_K(Cₖ₊₁) ⊕ Cₖ`, as in the whole message. The functions implemented
in assembly take a piece and the chaining value to start from, and leave
the one to continue from; their contracts are in `Spec/Cbc/Contract.lean`.
-/

@[expose] public section

namespace VG.Spec.Cbc

/-- A block cipher's forward function `CIPH_K` or inverse function
`CIPH⁻¹_K`, on blocks. -/
abbrev Cipher := List Byte → List Byte

/-- `X ⊕ Y` on blocks (§2.1), byte by byte. -/
def xor (x y : List Byte) : List Byte := List.zipWith (· ^^^ ·) x y

/-- §6.2, CBC Encryption of the plaintext blocks `P₁ … Pₙ` with the
initialization vector `IV`:
```
C₁ = CIPH_K(P₁ ⊕ IV);
Cⱼ = CIPH_K(Pⱼ ⊕ Cⱼ₋₁)    for j = 2 … n.
```
(Each ciphertext block is the chaining value of the next, so the recursion
passes `Cⱼ` on as the `IV` of the rest.) -/
def encrypt (ciph : Cipher) (iv : List Byte) : List (List Byte) → List (List Byte)
  | [] => []
  | p :: ps => let c := ciph (xor p iv); c :: encrypt ciph c ps

/-- §6.2, CBC Decryption of the ciphertext blocks `C₁ … Cₙ` with the
initialization vector `IV`, for the inverse cipher `ciphInv`:
```
P₁ = CIPH⁻¹_K(C₁) ⊕ IV;
Pⱼ = CIPH⁻¹_K(Cⱼ) ⊕ Cⱼ₋₁    for j = 2 … n.
``` -/
def decrypt (ciphInv : Cipher) (iv : List Byte) : List (List Byte) → List (List Byte)
  | [] => []
  | c :: cs => xor (ciphInv c) iv :: decrypt ciphInv c cs

/-- The chaining value to continue from after the ciphertext blocks `cs`,
encrypted or decrypted from `iv`: the last of them, or `iv` if there are
none (see above). -/
def next (iv : List Byte) (cs : List (List Byte)) : List Byte := cs.getLastD iv

/-! ## With AES -/

/-- The 16-byte blocks of a string whose length is a multiple of 16. -/
def blocks (bs : List Byte) : List (List Byte) :=
  (List.range (bs.length / 16)).map fun i => (bs.drop (16 * i)).take 16

/-- `CIPH_K` for AES with `nr` rounds and the key schedule `w` (as bytes). -/
def aesWith (nr : Nat) (w : List Byte) : Cipher := fun x =>
  (Aes.cipher nr w (Vector.ofFn fun i => x.getD i 0)).toList

/-- `CIPH⁻¹_K` for AES with `nr` rounds and the key schedule `w` (as bytes,
the forward cipher's, which the inverse cipher uses in the reverse order). -/
def aesInvWith (nr : Nat) (w : List Byte) : Cipher := fun x =>
  (Aes.invCipher nr w (Vector.ofFn fun i => x.getD i 0)).toList

/-- AES-CBC encryption of the plaintext `pt` (a multiple of 16 bytes) under
the key `key` (16, 24 or 32 bytes) with the 16-byte `iv`. -/
def aesCbcEncrypt (key iv pt : List Byte) : List Byte :=
  (encrypt (aesWith (Aes.rounds (key.length / 4)) (Aes.expandKey key)) iv (blocks pt)).flatten

/-- AES-CBC decryption of the ciphertext `ct` (a multiple of 16 bytes)
under the key `key` (16, 24 or 32 bytes) with the 16-byte `iv`. -/
def aesCbcDecrypt (key iv ct : List Byte) : List Byte :=
  (decrypt (aesInvWith (Aes.rounds (key.length / 4)) (Aes.expandKey key)) iv (blocks ct)).flatten

end VG.Spec.Cbc
