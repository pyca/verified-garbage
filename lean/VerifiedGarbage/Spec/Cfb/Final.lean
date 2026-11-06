module

public import VerifiedGarbage.Spec.Cfb.Contract

/-!
# CFB of a message of any length, and AES-CFB128's final functions

**Trusted** (as every file in `Spec/`). CFB with segments of a whole block
(`Spec/Cfb.lean`) of a message whose length need not be a multiple of the
block size `b`, and the contracts of `vg_aes_cfb128_encrypt_final` and
`vg_aes_cfb128_decrypt_final`, which take a message's last piece, of any
length, and handle its partial last segment themselves; those of the other
block ciphers are in `Spec/<Cipher>/CfbFinal.lean`. Existing contracts are
unchanged.

NIST SP 800-38A defines CFB only for a whole number of segments: "For the
CFB mode, the total number of bits in the plaintext must be a multiple of a
parameter, denoted s" (§5.2; also Appendix A). A message of `(n − 1) b + u`
bytes, `0 < u < b`, is CFB-encrypted here as other implementations do
(OpenSSL's CFB128, for one): its `n − 1` whole blocks as `Cfb.encrypt`,
then its partial last segment `Pₙ*` by one more of §6.3's steps, from the
input block `Iₙ = Cₙ₋₁` as for a whole segment (`C₀ = IV`), keeping only
the `u` bytes it has:
```
Oₙ = CIPH_K(Cₙ₋₁);
Cₙ* = Pₙ* ⊕ MSB_u(Oₙ)       (decryption: Pₙ* = Cₙ* ⊕ MSB_u(Oₙ)),
```
the rule that §6.4 (OFB) and §6.5 (CTR) give their partial last block.
Decryption uses the same `Oₙ`, from the last whole ciphertext block, so it
undoes encryption, and the encryption of a message is the first bytes of
that of any message that starts with it.

A final function leaves in `iv` the block a further call would continue from
when the piece is whole blocks (`Cbc.next`, the last ciphertext block, as
the whole-block functions do), and `Oₙ` after a partial last segment, whose
ciphertext cannot be fed back: the message must end there, and `Oₙ` is
keystream, which the caller wipes.
-/

@[expose] public section

namespace VG.Spec.Cfb

open Cbc (Cipher xor)

/-- The whole `b`-byte segments of `x`, in order, without a partial last
one. -/
def segments (b : Nat) (x : List Byte) : List (List Byte) :=
  (List.range (x.length / b)).map fun i => (x.drop (b * i)).take b

/-- The partial last segment of `x`: its last `x.length % b` bytes (none if
its length is a multiple of `b`). -/
def tail (b : Nat) (x : List Byte) : List Byte := x.drop (b * (x.length / b))

/-- CFB encryption of the plaintext `x`, of any length, with segments of a
whole block of `b` bytes, from `iv`: its whole segments as `encrypt`, then
its partial last segment `Pₙ*` XORed with the first bytes of
`Oₙ = CIPH_K(Cₙ₋₁)`, `MSB_u(Oₙ)` (`xor` stops at the shorter operand), where
`Cₙ₋₁` is the last whole ciphertext block, or `iv` if there is none (see
above). -/
def encryptFinal (ciph : Cipher) (b : Nat) (iv x : List Byte) : List Byte :=
  let cs := encrypt ciph iv (segments b x)
  cs.flatten ++ xor (tail b x) (ciph (Cbc.next iv cs))

/-- CFB decryption of the ciphertext `x`, of any length, with segments of a
whole block of `b` bytes, from `iv`: its whole segments as `decrypt`, then
its partial last segment `Cₙ*` XORed with `MSB_u(Oₙ)`,
`Oₙ = CIPH_K(Cₙ₋₁)`, where `Cₙ₋₁` is the last whole ciphertext block of
`x`, or `iv` if there is none (see above). -/
def decryptFinal (ciph : Cipher) (b : Nat) (iv x : List Byte) : List Byte :=
  let cs := segments b x
  (decrypt ciph iv cs).flatten ++ xor (tail b x) (ciph (Cbc.next iv cs))

/-- The block an encryption of `x` from `iv` leaves (see above): the last
ciphertext block (`iv` if there is none) when `x` is whole segments, and
`Oₙ = CIPH_K(Cₙ₋₁)` after a partial last segment. -/
def encryptFinalNext (ciph : Cipher) (b : Nat) (iv x : List Byte) : List Byte :=
  let c := Cbc.next iv (encrypt ciph iv (segments b x))
  if tail b x = [] then c else ciph c

/-- The block a decryption of `x` from `iv` leaves (see above): the last
ciphertext block, the last whole segment of `x` (`iv` if there is none),
when `x` is whole segments, and `Oₙ = CIPH_K(Cₙ₋₁)` after a partial last
segment. -/
def decryptFinalNext (ciph : Cipher) (b : Nat) (iv x : List Byte) : List Byte :=
  let c := Cbc.next iv (segments b x)
  if tail b x = [] then c else ciph c

/-- The final encryption's postcondition, for `CIPH_K` `ciph` on blocks of
`b` bytes: the `len` bytes at `data` replaced by their CFB encryption
(`encryptFinal`) from the block at `iv`, and that block by the one the
encryption leaves (`encryptFinalNext`). -/
def EncryptFinal (ciph : Cipher) (b : Nat) (m m' : Mem) (iv data : Addr) (len : Nat) :
    Prop :=
  let v := Aes.bytesAt m iv b
  let x := Aes.bytesAt m data len
  Aes.bytesAt m' data len = encryptFinal ciph b v x ∧
    Aes.bytesAt m' iv b = encryptFinalNext ciph b v x

/-- The final decryption's postcondition, for `CIPH_K` `ciph` on blocks of
`b` bytes: the `len` bytes at `data` replaced by their CFB decryption
(`decryptFinal`) from the block at `iv`, and that block by the one the
decryption leaves (`decryptFinalNext`). -/
def DecryptFinal (ciph : Cipher) (b : Nat) (m m' : Mem) (iv data : Addr) (len : Nat) :
    Prop :=
  let v := Aes.bytesAt m iv b
  let x := Aes.bytesAt m data len
  Aes.bytesAt m' data len = decryptFinal ciph b v x ∧
    Aes.bytesAt m' iv b = decryptFinalNext ciph b v x

/-! ## With AES -/

/-- `vg_aes_cfb128_encrypt_final(schedule: *const [u8; 240], rounds: usize, iv: *mut [u8; 16], data: *mut u8, len: usize, scratch: *mut [u64; 272])`,
and `vg_aes_cfb128_decrypt_final` with the same signature: the whole-block
functions' (`aesSig`), with the data `len` bytes. `rounds` is public;
`scratch` is working space. -/
def aesFinalSig : Sig where
  params := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
    ("iv", .array true .u8 16), ("data", .slice true .u8 "len"),
    ("scratch", .array true .u64 272)]

/-- For `rounds` of 10, 12 or 14, and every AES key `K` whose key schedule
is at `schedule` with `rounds` rounds (`Aes.KeySchedule`): replaces the
`len` bytes at `data` with their CFB128 encryption by AES with `K`, a
partial last segment included, from the block at `iv`, and that block with
the one the encryption leaves (`EncryptFinal`). -/
def aesEncryptFinalContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  aesFinalSig.contract A
    (pre := fun _schedule rounds _iv _data _len _scratch _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun schedule rounds iv data len _scratch m m' _ =>
      ∀ key, Aes.KeySchedule m schedule rounds.toNat key →
        EncryptFinal (Cbc.aes key) 16 m m' iv data len.toNat)
    (stack := stack)

/-- For `rounds` of 10, 12 or 14, and every AES key `K` whose key schedule
is at `schedule` with `rounds` rounds (`Aes.KeySchedule`): replaces the
`len` bytes at `data` with their CFB128 decryption by AES with `K`, a
partial last segment included, from the block at `iv`, and that block with
the one the decryption leaves (`DecryptFinal`). -/
def aesDecryptFinalContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  aesFinalSig.contract A
    (pre := fun _schedule rounds _iv _data _len _scratch _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun schedule rounds iv data len _scratch m m' _ =>
      ∀ key, Aes.KeySchedule m schedule rounds.toNat key →
        DecryptFinal (Cbc.aes key) 16 m m' iv data len.toNat)
    (stack := stack)

/-- `vg_aes_cfb128_encrypt_final` on every target. -/
def aesEncryptFinalApi : Api where
  module := "aes_cfb"
  name := "vg_aes_cfb128_encrypt_final"
  sig := aesFinalSig
  contracts := some fun A stack => aesEncryptFinalContract A stack
  summary := "AES-CFB128 encryption (NIST SP 800-38A §6.3, with 128-bit segments) of the last \
    piece of a message, of any length, in place: replaces its whole 16-byte blocks \
    `P₁ … Pₙ₋₁` at `data` with `Cⱼ = Pⱼ ⊕ CIPH_K(Cⱼ₋₁)`, where `C₀` is the block at `*iv`, and \
    a partial last segment `Pₙ*` of `u` bytes with `Cₙ* = Pₙ* ⊕ MSB_u(Oₙ)`, \
    `Oₙ = CIPH_K(Cₙ₋₁)` (an extension of SP 800-38A, which defines CFB only for whole \
    segments, by the rule of §6.4 and §6.5). Replaces `*iv` with the last ciphertext block, \
    so that a further call continues the message, if `len` is a multiple of 16 (leaving it \
    unchanged if `len = 0`), and otherwise with `Oₙ`: keystream, to be wiped, after which \
    the message must end. `CIPH_K` is AES (FIPS 197) with `rounds` rounds and the key \
    schedule in the first `16 * (rounds + 1)` bytes of `*schedule`, as `vg_aes_expand_key` \
    writes it.\n\n\
    Contract: `VG.Spec.Cfb.aesEncryptFinalContract`. Constant time: only the pointers, \
    `rounds` and `len` may affect timing, not the key schedule, the chaining value or the \
    data."
  safety := Cbc.aesSafety

/-- `vg_aes_cfb128_decrypt_final` on every target. -/
def aesDecryptFinalApi : Api where
  module := "aes_cfb"
  name := "vg_aes_cfb128_decrypt_final"
  sig := aesFinalSig
  contracts := some fun A stack => aesDecryptFinalContract A stack
  summary := "AES-CFB128 decryption (NIST SP 800-38A §6.3, with 128-bit segments) of the last \
    piece of a message, of any length, in place: replaces its whole 16-byte blocks \
    `C₁ … Cₙ₋₁` at `data` with `Pⱼ = Cⱼ ⊕ CIPH_K(Cⱼ₋₁)`, where `C₀` is the block at `*iv`, and \
    a partial last segment `Cₙ*` of `u` bytes with `Pₙ* = Cₙ* ⊕ MSB_u(Oₙ)`, \
    `Oₙ = CIPH_K(Cₙ₋₁)` (an extension of SP 800-38A, which defines CFB only for whole \
    segments, by the rule of §6.4 and §6.5). Replaces `*iv` with the last ciphertext block, \
    the last whole block at `data` on entry, so that a further call continues the message, \
    if `len` is a multiple of 16 (leaving it unchanged if `len = 0`), and otherwise with \
    `Oₙ`: keystream, to be wiped, after which the message must end. `CIPH_K` is AES \
    (FIPS 197) with `rounds` rounds and the key schedule in the first `16 * (rounds + 1)` \
    bytes of `*schedule`, as `vg_aes_expand_key` writes it.\n\n\
    Contract: `VG.Spec.Cfb.aesDecryptFinalContract`. Constant time: only the pointers, \
    `rounds` and `len` may affect timing, not the key schedule, the chaining value or the \
    data."
  safety := Cbc.aesSafety

end VG.Spec.Cfb
