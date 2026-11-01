module

public import VerifiedGarbage.Impl.AesCbc.PPC64LE

/-!
# XTS-AES: PPC64LE implementation

`vg_aes_xts_encrypt(schedule = r3, rounds = r4, tweak = r5, data = r6, n = r7, scratch = r8)`
and `vg_aes_xts_decrypt` with the same arguments (see
`VG.Proof.Xts.aesEncryptContract` and `aesDecryptContract`), composed of
calls of the verified `vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` on
one block at a time, in place, as on ARMv7 (`VG.Impl.AesXts.Arm`).

They are built from AES-CBC's pieces (`Impl/AesCbc/PPC64LE.lean`), whose
arguments are the same: the registers saved in the scratch buffer and the
arguments kept in `r14` (schedule), `r15` (rounds), `r16` (the tweak),
`r17` (the next block), `r18` (blocks left) and `r19` (scratch). Each block,
the tweak is XORed into the data block, which is enciphered (or deciphered)
in place, the tweak is XORed in again, and the tweak is multiplied by `α`
(`mulA`): its two words, little-endian, loaded, the low word shifted left by
one bit and XORed with `0x87` if the high word's top bit was set (a mask
from `0 − (hi >> 63)`), and the high word shifted left with the low word's
top bit shifted in.

Only the pointers, `rounds` and `n` can affect timing: the only branches are
on `n`.
-/

@[expose] public section

namespace VG.Impl.AesXts.PPC64LE

open VG.PPC64LE
open VG.Impl.AesCbc.PPC64LE (xorInto callArgs advance whole encCall decCall)

/-- The tweak at `r16` times `α`. -/
def mulA : List Instr :=
  [.load .d .r9 .r16 0, .load .d .r10 .r16 8,
   .lsr .d .r11 .r10 63, .li .r12 0, .sub .r11 .r12 .r11, .li .r12 0x87, .logic .and .r11 .r11 .r12,
   .lsr .d .r12 .r9 63, .lsl .r9 .r9 1, .logic .xor .r9 .r9 .r11,
   .lsl .r10 .r10 1, .logic .or .r10 .r10 .r12,
   .store .d .r9 .r16 0, .store .d .r10 .r16 8]

/-- The tweak XORed into the data block, and the arguments of the call. -/
def pre : List Instr := xorInto .r17 .r16 ++ callArgs

/-- The tweak XORed in again, the tweak times `α`, and on to the next block. -/
def post : List Instr := xorInto .r17 .r16 ++ mulA ++ advance

def encBody : Prog isa := .seq (.block pre) (.seq encCall (.block post))

def decBody : Prog isa := .seq (.block pre) (.seq decCall (.block post))

def encrypt : Prog isa := whole encBody

def decrypt : Prog isa := whole decBody

end VG.Impl.AesXts.PPC64LE
