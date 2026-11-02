module

public import VerifiedGarbage.Impl.AesCbc.RISCV64

/-!
# XTS-AES: RISC-V implementation

`vg_aes_xts_encrypt(schedule = a0, rounds = a1, tweak = a2, data = a3, n = a4, scratch = a5)`
and `vg_aes_xts_decrypt` with the same arguments (see
`VG.Proof.Xts.aesEncryptContract` and `aesDecryptContract`): each a call of
the wide XTS encryption or decryption (`Impl.Aes.RISCV64.xtsEncWide`,
`xtsDecWide`, `Impl/Aes/RISCV64/Wide.lean`), which take the same arguments
and the first 2048 bytes of the scratch buffer, bitslice the round keys once
and process four blocks at a time, wrapped as AES-CBC's
(`Impl.AesCbc.RISCV64.chainWrapped`): each block, the tweak is XORed into
the data block, which is enciphered (or deciphered) in place, the tweak is
XORed in again, and the tweak is multiplied by `α`; the last tweak is
written back.

`mulA` multiplies the tweak at `s3` by `α`, for the data-unit functions
(`Impl/AesXts/RISCV64Unit.lean`), as on ARMv7 (`VG.Impl.AesXts.Arm`): its
four 32-bit words, little-endian, loaded, each stored shifted left by one
bit with the top bit of the word before it shifted in, and the first XORed
with `0x87` if the last word's top bit was set (a mask from
`0 − (w₃ >> 31)`). The contracts state no alignment for the tweak, so its
words are loaded and stored a byte at a time (`loadLE32`, `storeLE32`, which
stores the low 32 bits of each shifted word).

Only the pointers, `rounds` and `n` can affect timing: the only branches are
on `n`.
-/

@[expose] public section

namespace VG.Impl.AesXts.RISCV64

open VG.RISCV64 VG.Impl.Words.RISCV64
open VG.Impl.AesCbc.RISCV64 (chainWrapped)

/-- Word `j` of the tweak times `α`, from the word in `w` and the word
before it in `p`, stored at `off(s3)`. -/
def mulWord (w p : Reg) (off : Nat) : List Instr :=
  [.shift .sll .d .a6 w 1, .shift .srl .d .t6 p 31, .logic .or .a6 .a6 .t6] ++ storeLE32 .a6 .t2 .s3 off

/-- The tweak at `s3` times `α`. -/
def mulA : List Instr :=
  loadLE32 .t1 .t2 .s3 0 ++ loadLE32 .t3 .t2 .s3 4 ++ loadLE32 .t4 .t2 .s3 8 ++ loadLE32 .t5 .t2 .s3 12 ++
  ([.shift .srl .d .t6 .t5 31, .li .t2 0, .sub .t6 .t2 .t6, .li .t2 0x87, .logic .and .t6 .t6 .t2,
    .shift .sll .d .a6 .t1 1, .logic .xor .a6 .a6 .t6] : List Instr) ++ storeLE32 .a6 .t2 .s3 0 ++
  mulWord .t3 .t1 4 ++ mulWord .t4 .t3 8 ++ mulWord .t5 .t4 12

/-- Four blocks at a time, by the wide XTS encryption
(`Impl.Aes.RISCV64.xtsEncWide`), which bitslices the round keys once. -/
def encrypt : Prog isa := chainWrapped Impl.Aes.RISCV64.xtsEncWideCall

/-- Four blocks at a time, by the wide XTS decryption
(`Impl.Aes.RISCV64.xtsDecWide`). -/
def decrypt : Prog isa := chainWrapped Impl.Aes.RISCV64.xtsDecWideCall

end VG.Impl.AesXts.RISCV64
