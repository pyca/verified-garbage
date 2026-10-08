import VerifiedGarbage.Impl.AesCbc.AArch64

/-!
# XTS-AES: AArch64 implementation

`vg_aes_xts_encrypt(schedule = x0, rounds = x1, tweak = x2, data = x3, n = x4, scratch = x5)`
and `vg_aes_xts_decrypt` with the same arguments (see
`VG.Spec.Xts.aesEncryptContract` and `aesDecryptContract`), composed of
one call of the verified `vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks`
on all the blocks, in place. They are generic over the implementation they
call (`Blocks`): each is emitted once for each implementation (e.g.
`vg_aes_xts_encrypt_aes` calls `vg_aes_encrypt_blocks_aes`).

They are built from AES-CBC's pieces (`Impl/AesCbc/AArch64.lean`), whose
arguments are the same: the registers saved in the scratch buffer and the
arguments kept in `x19` (schedule), `x20` (rounds), `x21` (the tweak), `x22`
(the next block), `x23` (blocks left) and `x24` (scratch). The tweak `T` is
saved at `scratch + 2048`; a pass over the blocks XORs each block's tweak
into it, multiplying the tweak by `α` after each (`pass`); `T` is restored,
the block function enciphers (or deciphers) all the blocks in place, and a
second pass XORs the tweaks in again, leaving the tweak after the last
block. The first pass keeps the data pointer and the number of blocks in
`x14` and `x15`. The tweak is multiplied by `α` as its two words,
little-endian, shifted left by `adds` and `adcs` (carrying the low word's top
bit into the high word), and `0x87` XORed into the low word if the high
word's top bit was set, chosen by `csel` on the carry.

Only the pointers, `rounds` and `n` can affect timing.
-/

namespace VG.Impl.AesXts.AArch64

open VG.AArch64
open VG.Impl.Aes.AArch64 (Blocks)
open VG.Impl.AesCbc.AArch64 (mov save setup restore xorInto copy cOff advance)

/-- The tweak at `x21` times `α`. -/
def mulA : List Instr :=
  [.ldr .x .x9 .x21 0, .ldr .x .x10 .x21 8, .adds .x .x9 .x9 .x9, .adcs .x .x10 .x10 .x10,
   .movz .x .x11 0x87 0, .movz .x .x12 0 0, .csel .x .x11 .x11 .x12, .logic .eor .x .x9 .x9 .x11,
   .str .x .x9 .x21 0, .str .x .x10 .x21 8]

/-- One block: the tweak XORed in, and the tweak times `α`. -/
def passBody : List Instr := xorInto ++ mulA ++ advance

/-- Each block from `x22` on (`x23` of them, at least one) with its tweak
XORed in. -/
def pass : Prog isa := .loop (.block passBody) (.nonzero .x .x23)

/-- `T` saved, and the data pointer and number of blocks kept. -/
def saveT : List Instr := copy .x24 cOff .x21 0 ++ [mov .x14 .x22, mov .x15 .x23]

/-- The data pointer and number of blocks back, `T` restored, and the
arguments of the block function on all the blocks. -/
def callArgs : List Instr :=
  [mov .x22 .x14, mov .x23 .x15] ++ copy .x21 0 .x24 cOff ++
  [mov .x0 .x19, mov .x1 .x20, mov .x2 .x22, mov .x3 .x23, mov .x4 .x24]

/-- The blocks (at least one): the tweaks XORed in, enciphered (or
deciphered) by `b`, and the tweaks XORed in again. -/
def batch (b : Blocks) : Prog isa :=
  .seq (.block saveT) (.seq pass (.seq (.block callArgs) (.seq (.call b.name b.code) pass)))

def crypt (b : Blocks) : Prog isa :=
  .seq (.block (save ++ setup)) (.seq (.ite (.zero .x .x23) (.block []) (batch b)) (.block restore))

def encrypt (b : Blocks) : Prog isa := crypt b

def decrypt (b : Blocks) : Prog isa := crypt b

end VG.Impl.AesXts.AArch64
