import VerifiedGarbage.Impl.AesCbc.AArch64

/-!
# AES-CTR: AArch64 implementation

`vg_aes_ctr(schedule = x0, rounds = x1, ctr = x2, data = x3, n = x4, scratch = x5)`
(see `VG.Spec.Ctr.aesContract`), composed of calls of the verified
`vg_aes_encrypt_blocks` on one block at a time. It is generic over the
implementation it calls (`Blocks`): it is emitted once for each
implementation (e.g. `vg_aes_ctr_aes` calls `vg_aes_encrypt_blocks_aes`).

It is built from AES-CBC's pieces (`Impl/AesCbc/AArch64.lean`), whose
arguments are the same: the registers saved in the scratch buffer and the
arguments kept in `x19` (schedule), `x20` (rounds), `x21` (the counter
block), `x22` (the next block), `x23` (blocks left) and `x24` (scratch).
Each block, the counter block is copied to the scratch buffer (at 2048,
where CBC's decryption keeps a block) and enciphered there, giving the next
output block, which is XORed into the data block; then the counter block is
incremented as a 128-bit big-endian number: its two halves loaded,
byte-reversed (`rev`), added to with `adds` and `adc`, reversed again and
stored.

Only the pointers, `rounds` and `n` can affect timing.
-/

namespace VG.Impl.AesCtr.AArch64

open VG.AArch64
open VG.Impl.Aes.AArch64 (Blocks)
open VG.Impl.AesCbc.AArch64 (mov cOff copy advance whole)

/-- The counter block copied to `x24 + cOff`, and the arguments of the block
function for the copy: the schedule, the rounds, the copy, `n = 1`, and the
working space. -/
def pre : List Instr :=
  copy .x24 cOff .x21 0 ++ [mov .x0 .x19, mov .x1 .x20, .addImm .x .x2 .x24 2048, .movz .x .x3 1 0, mov .x4 .x24]

/-- The output block, in the scratch buffer, XORed into the data block. -/
def xorOut : List Instr :=
  [.ldr .x .x9 .x22 0, .ldr .x .x10 .x24 cOff, .logic .eor .x .x9 .x9 .x10, .str .x .x9 .x22 0,
   .ldr .x .x9 .x22 8, .ldr .x .x10 .x24 (cOff + 8), .logic .eor .x .x9 .x9 .x10, .str .x .x9 .x22 8]

/-- The counter block plus 1, modulo `2¹²⁸`, big-endian. -/
def incr : List Instr :=
  [.ldr .x .x9 .x21 8, .rev .x9 .x9, .ldr .x .x10 .x21 0, .rev .x10 .x10, .movz .x .x11 1 0,
   .movz .x .x12 0 0, .adds .x .x9 .x9 .x11, .adc .x .x10 .x10 .x12, .rev .x9 .x9, .rev .x10 .x10,
   .str .x .x9 .x21 8, .str .x .x10 .x21 0]

/-- One block. -/
def body (b : Blocks) : Prog isa :=
  .seq (.block pre) (.seq (.call b.name b.code) (.block (xorOut ++ incr ++ advance)))

def crypt (b : Blocks) : Prog isa := whole (body b)

end VG.Impl.AesCtr.AArch64
