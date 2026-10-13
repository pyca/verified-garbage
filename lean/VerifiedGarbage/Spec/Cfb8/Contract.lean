module

public import VerifiedGarbage.Spec.Cfb8
public import VerifiedGarbage.Spec.Cbc.Contract

/-!
# AES-CFB8: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of
`vg_aes_cfb8_encrypt` and `vg_aes_cfb8_decrypt`, in terms of
`Spec/Cfb8.lean`, for any target: `A` is the target's calling convention.
The signature fixes where the arguments are, the memory each function may
access, disjointness, and that the pointers, the number of rounds and the
length are public (see `TCB/Sig.lean`). The key schedule, the input block
and the data are secret.

Each reads the AES key schedule that `vg_aes_expand_key`
(`VG.Spec.Aes.expandKeyContract`) writes, `16 (rounds + 1)` bytes, at the
start of a 240-byte buffer, and transforms `len` bytes in place, from the
input block in `iv`, which it replaces with the one to continue from
(`Cfb8.next`): so a caller may encrypt or decrypt a message in pieces of
any length, keeping `iv` between calls.

Each takes CBC's `scratch` buffer: room for the working space of
`vg_aes_encrypt_blocks` (`[u64; 256]`) and 128 bytes more. `stack` is the
number of bytes of stack below the stack pointer that an implementation's
calls and frames use (see `Sig.contract`).
-/

@[expose] public section

namespace VG.Spec.Cfb8

/-- `vg_aes_cfb8_encrypt(schedule: *const [u8; 240], rounds: usize, iv: *mut [u8; 16], data: *mut u8, len: usize, scratch: *mut [u64; 272])`,
and `vg_aes_cfb8_decrypt` with the same signature. `rounds` is public;
`scratch` is working space. -/
def aesSig : Sig where
  params := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
    ("iv", .array true .u8 16), ("data", .slice true .u8 "len"),
    ("scratch", .array true .u64 272)]

/-- For `rounds` of 10, 12 or 14, with the key schedule `w` in the first
`16 (rounds + 1)` bytes at `schedule`: replaces the `len` bytes at `data`
with their CFB8 encryption (§6.3) by AES with `w`, from the input block at
`iv`, and that block with the input block of the next byte, its last
`16 - len` bytes followed by the last `len` (up to 16) ciphertext bytes
(unchanged if `len = 0`). -/
def aesEncryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  aesSig.contract A
    (pre := fun _schedule rounds _iv _data _len _scratch _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun schedule rounds iv data len _scratch m m' _ =>
      let ciph := Cbc.aesWith rounds.toNat (Aes.bytesAt m schedule (16 * (rounds.toNat + 1)))
      let cs := encrypt ciph (Aes.bytesAt m iv 16) (Aes.bytesAt m data len.toNat)
      Aes.bytesAt m' data len.toNat = cs ∧ Aes.bytesAt m' iv 16 = next (Aes.bytesAt m iv 16) cs)
    (stack := stack)

/-- For `rounds` of 10, 12 or 14, with the key schedule `w` in the first
`16 (rounds + 1)` bytes at `schedule`: replaces the `len` bytes at `data`
with their CFB8 decryption (§6.3) by AES with `w`, from the input block at
`iv`, and that block with the input block of the next byte, its last
`16 - len` bytes followed by the last `len` (up to 16) bytes at `data` on
entry (unchanged if `len = 0`). -/
def aesDecryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  aesSig.contract A
    (pre := fun _schedule rounds _iv _data _len _scratch _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun schedule rounds iv data len _scratch m m' _ =>
      let ciph := Cbc.aesWith rounds.toNat (Aes.bytesAt m schedule (16 * (rounds.toNat + 1)))
      let cs := Aes.bytesAt m data len.toNat
      Aes.bytesAt m' data len.toNat = decrypt ciph (Aes.bytesAt m iv 16) cs ∧
        Aes.bytesAt m' iv 16 = next (Aes.bytesAt m iv 16) cs)
    (stack := stack)

/-- `vg_aes_cfb8_encrypt` on every target. -/
def aesEncryptApi : Api where
  module := "aes_cfb8"
  name := "vg_aes_cfb8_encrypt"
  sig := aesSig
  contracts := some fun A stack => aesEncryptContract A stack
  summary := "AES-CFB8 encryption (NIST SP 800-38A §6.3, with 8-bit segments), in place: \
    replaces the `len` bytes `P#₁ … P#ₙ` at `data` with `C#ⱼ = P#ⱼ ⊕ MSB₈(CIPH_K(Iⱼ))`, where \
    `I₁` is the block at `*iv` and `Iⱼ₊₁` is `Iⱼ` without its first byte, followed by `C#ⱼ`, \
    and `*iv` with `Iₙ₊₁` (leaving it unchanged if `len = 0`), so that a further call \
    continues the message. `CIPH_K` is AES (FIPS 197) with `rounds` rounds and the key \
    schedule in the first `16 * (rounds + 1)` bytes of `*schedule`, as `vg_aes_expand_key` \
    writes it.\n\n\
    Contract: `VG.Spec.Cfb8.aesEncryptContract`. Constant time: only the pointers, `rounds` \
    and `len` may affect timing, not the key schedule, the input block or the data."
  safety := Cbc.aesSafety

/-- `vg_aes_cfb8_decrypt` on every target. -/
def aesDecryptApi : Api where
  module := "aes_cfb8"
  name := "vg_aes_cfb8_decrypt"
  sig := aesSig
  contracts := some fun A stack => aesDecryptContract A stack
  summary := "AES-CFB8 decryption (NIST SP 800-38A §6.3, with 8-bit segments), in place: \
    replaces the `len` bytes `C#₁ … C#ₙ` at `data` with `P#ⱼ = C#ⱼ ⊕ MSB₈(CIPH_K(Iⱼ))`, where \
    `I₁` is the block at `*iv` and `Iⱼ₊₁` is `Iⱼ` without its first byte, followed by `C#ⱼ`, \
    and `*iv` with `Iₙ₊₁` (leaving it unchanged if `len = 0`), so that a further call \
    continues the message. `CIPH_K` is AES (FIPS 197) with `rounds` rounds and the key \
    schedule in the first `16 * (rounds + 1)` bytes of `*schedule`, as `vg_aes_expand_key` \
    writes it.\n\n\
    Contract: `VG.Spec.Cfb8.aesDecryptContract`. Constant time: only the pointers, `rounds` \
    and `len` may affect timing, not the key schedule, the input block or the data."
  safety := Cbc.aesSafety

end VG.Spec.Cfb8
