module

public import VerifiedGarbage.Impl.AesCbc.Arm

/-!
# AES-CTR: ARMv7 implementation

`vg_aes_ctr(schedule = r0, rounds = r1, ctr = r2, data = r3, n, scratch)`
(the last two on the stack; see `VG.Spec.Ctr.aesContract`), composed of
calls of the verified `vg_aes_encrypt_blocks` on one block at a time.

It is built from AES-CBC's pieces (`Impl/AesCbc/Arm.lean`), whose arguments
are the same: the registers saved in the scratch buffer and the arguments
kept in `r4` (schedule), `r5` (rounds), `r6` (the counter block), `r7` (the
next block), `r8` (blocks left) and `r10` (scratch). Each block, the counter
block is copied to the scratch buffer (at 2048, where CBC's decryption keeps
a block) and enciphered there, giving the next output block, which is XORed
into the data block; then the counter block is incremented as a 128-bit
big-endian number: its four words loaded and byte-reversed (`rev`), the last
plus 1 with `adds`, the carry taken into `r12` with `adc` and added to the
next word with `adds`, the first plus the last carry with `adc`, and each
reversed again and stored.

Only the pointers, `rounds` and `n` can affect timing: the only branches are
on `n`.
-/

@[expose] public section

namespace VG.Impl.AesCtr.Arm

open VG.Arm
open VG.Impl.CmacAes.Arm (mov xor4 advance)
open VG.Impl.AesCbc.Arm (cOff whole encFrame zero4)

/-- The counter block copied to `r10 + cOff`, and the arguments of the block
function for the copy: the schedule, the rounds, the copy, `n = 1`, and the
working space. -/
def pre : List Instr :=
  zero4 .r10 cOff ++ xor4 .r10 .r6 .r10 cOff 0 cOff ++
  [mov .r0 .r4, mov .r1 .r5, .dp .add .r2 .r10 (.imm 2048), .mov .r3 (.imm 1), mov .r12 .r10]

/-- The counter block at `r6` plus 1, modulo `2¹²⁸`, big-endian. -/
def incr : List Instr :=
  [.ldr .r0 .r6 12, .rev .r0 .r0, .ldr .r1 .r6 8, .rev .r1 .r1, .ldr .r2 .r6 4, .rev .r2 .r2,
   .ldr .r3 .r6 0, .rev .r3 .r3,
   .adds .r0 .r0 (.imm 1), .mov .r12 (.imm 0), .adc .r12 .r12 (.imm 0),
   .adds .r1 .r1 (.reg .r12), .mov .r12 (.imm 0), .adc .r12 .r12 (.imm 0),
   .adds .r2 .r2 (.reg .r12), .adc .r3 .r3 (.imm 0),
   .rev .r0 .r0, .str .r0 .r6 12, .rev .r1 .r1, .str .r1 .r6 8, .rev .r2 .r2, .str .r2 .r6 4,
   .rev .r3 .r3, .str .r3 .r6 0]

/-- The output block XORed into the data block, the counter block
incremented, and on to the next block. -/
def post : List Instr := xor4 .r7 .r10 .r7 0 cOff 0 ++ incr ++ advance

/-- One block. -/
def body : Prog isa := .seq (.block pre) (.seq encFrame (.block post))

def crypt : Prog isa := whole body

end VG.Impl.AesCtr.Arm
