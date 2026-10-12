module

public import VerifiedGarbage.Impl.AesCbc.Arm

/-!
# XTS-AES: ARMv7 implementation

`vg_aes_xts_encrypt(schedule = r0, rounds = r1, tweak = r2, data = r3, n, scratch)`
and `vg_aes_xts_decrypt` with the same arguments (the last two on the stack;
see `VG.Spec.Xts.aesEncryptContract` and `aesDecryptContract`), composed of
calls of the verified `vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` on
one block at a time, in place.

They are built from AES-CBC's pieces (`Impl/AesCbc/Arm.lean`), whose
arguments are the same: the registers saved in the scratch buffer and the
arguments kept in `r4` (schedule), `r5` (rounds), `r6` (the tweak), `r7`
(the next block), `r8` (blocks left) and `r10` (scratch). Each block, the
tweak is XORed into the data block, which is enciphered (or deciphered) in
place, the tweak is XORed in again, and the tweak is multiplied by `α`: its
four words, little-endian, loaded, each stored shifted left by one bit with
the top bit of the word before it shifted in (`lsl #1`, `orr` with
`lsr #31`), and the first XORed with `0x87` if the last word's top bit was
set (a mask from `0 − (w₃ lsr #31)`).

Only the pointers, `rounds` and `n` can affect timing: the only branches are
on `n`.
-/

@[expose] public section

namespace VG.Impl.AesXts.Arm

open VG.Arm
open VG.Impl.CmacAes.Arm (advance xor4)
open VG.Impl.AesCbc.Arm (whole encFrame decFrame callArgs)

/-- The tweak at `r6` times `α`. -/
def mulA : List Instr :=
  [.ldr .r0 .r6 0, .ldr .r1 .r6 4, .ldr .r2 .r6 8, .ldr .r3 .r6 12,
   .mov .r12 (.imm 0), .dp .sub .r12 .r12 (.shifted .r3 .lsr 31), .dp .and .r12 .r12 (.imm 0x87),
   .mov .lr (.shifted .r0 .lsl 1), .dp .eor .lr .lr (.reg .r12), .str .lr .r6 0,
   .mov .lr (.shifted .r1 .lsl 1), .dp .orr .lr .lr (.shifted .r0 .lsr 31), .str .lr .r6 4,
   .mov .lr (.shifted .r2 .lsl 1), .dp .orr .lr .lr (.shifted .r1 .lsr 31), .str .lr .r6 8,
   .mov .lr (.shifted .r3 .lsl 1), .dp .orr .lr .lr (.shifted .r2 .lsr 31), .str .lr .r6 12]

/-- The tweak XORed into the data block, and the arguments of the call. -/
def pre : List Instr := xor4 .r7 .r6 .r7 0 0 0 ++ callArgs

/-- The tweak XORed in again, the tweak times `α`, and on to the next block. -/
def post : List Instr := xor4 .r7 .r6 .r7 0 0 0 ++ mulA ++ advance

def encrypt : Prog isa := whole (.seq (.block pre) (.seq encFrame (.block post)))

def decrypt : Prog isa := whole (.seq (.block pre) (.seq decFrame (.block post)))

end VG.Impl.AesXts.Arm
