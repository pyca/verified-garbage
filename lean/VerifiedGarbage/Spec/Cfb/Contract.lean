module

public import VerifiedGarbage.Spec.Cfb
public import VerifiedGarbage.Spec.Cbc.Contract

/-!
# AES-CFB128: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of
`vg_aes_cfb128_encrypt` and `vg_aes_cfb128_decrypt`, in terms of
`Spec/Cfb.lean`, for any target: `A` is the target's calling convention.
The signatures (CBC's, `Spec/Cbc/Contract.lean`) fix where the arguments
are, the memory each function may access, disjointness, and that the
pointers, the number of rounds and the number of blocks are public (see
`TCB/Sig.lean`). The key schedule, the chaining value and the data are
secret.

Each reads the AES key schedule that `vg_aes_expand_key`
(`VG.Spec.Aes.expandKeyContract`) writes, `16 (rounds + 1)` bytes, at the
start of a 240-byte buffer, and transforms `n` whole blocks in place, from
the block in `iv`, which it replaces with the one to continue from, the
last ciphertext block (`Cbc.next`): so a caller may encrypt or decrypt a
message in pieces of whole blocks, keeping `iv` between calls. A partial
last segment is the caller's.

Each takes CBC's `scratch` buffer: room for the working space of
`vg_aes_encrypt_blocks` (`[u64; 256]`) and 128 bytes more. `stack` is the
number of bytes of stack below the stack pointer that an implementation's
calls and frames use (see `Sig.contract`).
-/

@[expose] public section

namespace VG.Spec.Cfb

/-- `vg_aes_cfb128_encrypt(schedule: *const [u8; 240], rounds: usize, iv: *mut [u8; 16], data: *mut [u8; 16], n: usize, scratch: *mut [u64; 272])`,
and `vg_aes_cfb128_decrypt` with the same signature. `rounds` is public;
`scratch` is working space. -/
def aesSig : Sig := Cbc.aesSig

/-- For `rounds` of 10, 12 or 14, with the key schedule `w` in the first
`16 (rounds + 1)` bytes at `schedule`: replaces the `n` blocks at `data`
with their CFB128 encryption (§6.3) by AES with `w`, from the block at
`iv`, and that block with the last ciphertext block (unchanged if
`n = 0`). -/
def aesEncryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  aesSig.contract A
    (pre := fun _schedule rounds _iv _data _n _scratch _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun schedule rounds iv data n _scratch m m' _ =>
      let ciph := Cbc.aesWith rounds.toNat (Aes.bytesAt m schedule (16 * (rounds.toNat + 1)))
      let cs := encrypt ciph (Aes.bytesAt m iv 16) (Cbc.blocksAt m data n.toNat)
      Cbc.blocksAt m' data n.toNat = cs ∧ Aes.bytesAt m' iv 16 = Cbc.next (Aes.bytesAt m iv 16) cs)
    (stack := stack)

/-- For `rounds` of 10, 12 or 14, with the key schedule `w` in the first
`16 (rounds + 1)` bytes at `schedule`: replaces the `n` blocks at `data`
with their CFB128 decryption (§6.3) by AES with `w`, from the block at
`iv`, and that block with the last ciphertext block, the last block at
`data` on entry (unchanged if `n = 0`). -/
def aesDecryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  aesSig.contract A
    (pre := fun _schedule rounds _iv _data _n _scratch _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun schedule rounds iv data n _scratch m m' _ =>
      let ciph := Cbc.aesWith rounds.toNat (Aes.bytesAt m schedule (16 * (rounds.toNat + 1)))
      let cs := Cbc.blocksAt m data n.toNat
      Cbc.blocksAt m' data n.toNat = decrypt ciph (Aes.bytesAt m iv 16) cs ∧
        Aes.bytesAt m' iv 16 = Cbc.next (Aes.bytesAt m iv 16) cs)
    (stack := stack)

/-- `vg_aes_cfb128_encrypt` on every target. -/
def aesEncryptApi : Api where
  module := "aes_cfb"
  name := "vg_aes_cfb128_encrypt"
  sig := aesSig
  contracts := some fun A stack => aesEncryptContract A stack
  summary := "AES-CFB128 encryption (NIST SP 800-38A §6.3, with 128-bit segments) of whole \
    blocks, in place: replaces the `n` 16-byte blocks `P₁ … Pₙ` at `data` with \
    `Cⱼ = Pⱼ ⊕ CIPH_K(Cⱼ₋₁)`, where `C₀` is the block at `*iv`, and `*iv` with `Cₙ` (leaving \
    it unchanged if `n = 0`), so that a further call continues the message. `CIPH_K` is AES \
    (FIPS 197) with `rounds` rounds and the key schedule in the first `16 * (rounds + 1)` \
    bytes of `*schedule`, as `vg_aes_expand_key` writes it.\n\n\
    Contract: `VG.Spec.Cfb.aesEncryptContract`. Constant time: only the pointers, `rounds` \
    and `n` may affect timing, not the key schedule, the chaining value or the data."
  safety := Cbc.aesSafety

/-- `vg_aes_cfb128_decrypt` on every target. -/
def aesDecryptApi : Api where
  module := "aes_cfb"
  name := "vg_aes_cfb128_decrypt"
  sig := aesSig
  contracts := some fun A stack => aesDecryptContract A stack
  summary := "AES-CFB128 decryption (NIST SP 800-38A §6.3, with 128-bit segments) of whole \
    blocks, in place: replaces the `n` 16-byte blocks `C₁ … Cₙ` at `data` with \
    `Pⱼ = Cⱼ ⊕ CIPH_K(Cⱼ₋₁)`, where `C₀` is the block at `*iv`, and `*iv` with `Cₙ`, the last \
    block at `data` on entry (leaving it unchanged if `n = 0`), so that a further call \
    continues the message. `CIPH_K` is AES (FIPS 197) with `rounds` rounds and the key \
    schedule in the first `16 * (rounds + 1)` bytes of `*schedule`, as `vg_aes_expand_key` \
    writes it.\n\n\
    Contract: `VG.Spec.Cfb.aesDecryptContract`. Constant time: only the pointers, `rounds` \
    and `n` may affect timing, not the key schedule, the chaining value or the data."
  safety := Cbc.aesSafety

end VG.Spec.Cfb
