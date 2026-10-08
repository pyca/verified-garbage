import VerifiedGarbage.Impl.AesCbc.AArch64

/-!
# XTS-AES: AArch64 implementation

`vg_aes_xts_encrypt(schedule = x0, rounds = x1, tweak = x2, data = x3, n = x4, scratch = x5)`
and `vg_aes_xts_decrypt` with the same arguments (see
`VG.Spec.Xts.aesEncryptContract` and `aesDecryptContract`), composed of
calls of the verified `vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` on
one block at a time, in place. They are generic over the implementation
they call (`Blocks`): each is emitted once for each implementation (e.g.
`vg_aes_xts_encrypt_aes` calls `vg_aes_encrypt_blocks_aes`).

They are built from AES-CBC's pieces (`Impl/AesCbc/AArch64.lean`), whose
arguments are the same: the registers saved in the scratch buffer and the
arguments kept in `x19` (schedule), `x20` (rounds), `x21` (the tweak), `x22`
(the next block), `x23` (blocks left) and `x24` (scratch). Each block, the
tweak is XORed into the data block, which is enciphered (or deciphered) in
place, the tweak is XORed in again, and the tweak is multiplied by `α`: its
two words, little-endian, shifted left by `adds` and `adcs` (carrying the low
word's top bit into the high word), and `0x87` XORed into the low word if
the high word's top bit was set, chosen by `csel` on the carry.

Only the pointers, `rounds` and `n` can affect timing.
-/

namespace VG.Impl.AesXts.AArch64

open VG.AArch64
open VG.Impl.Aes.AArch64 (Blocks)
open VG.Impl.AesCbc.AArch64 (xorInto callArgs advance whole)

/-- The tweak at `x21` times `α`. -/
def mulA : List Instr :=
  [.ldr .x .x9 .x21 0, .ldr .x .x10 .x21 8, .adds .x .x9 .x9 .x9, .adcs .x .x10 .x10 .x10,
   .movz .x .x11 0x87 0, .movz .x .x12 0 0, .csel .x .x11 .x11 .x12, .logic .eor .x .x9 .x9 .x11,
   .str .x .x9 .x21 0, .str .x .x10 .x21 8]

/-- One block: the tweak XORed in, enciphered (or deciphered) by `b`, the
tweak XORed in again, and the tweak times `α`. -/
def body (b : Blocks) : Prog isa :=
  .seq (.block (xorInto ++ callArgs)) (.seq (.call b.name b.code) (.block (xorInto ++ mulA ++ advance)))

def encrypt (b : Blocks) : Prog isa := whole (body b)

def decrypt (b : Blocks) : Prog isa := whole (body b)

end VG.Impl.AesXts.AArch64
