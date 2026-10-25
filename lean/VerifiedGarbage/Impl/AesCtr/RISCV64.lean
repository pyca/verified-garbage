module

public import VerifiedGarbage.Impl.AesCbc.RISCV64
public import VerifiedGarbage.Impl.Aes.RISCV64.Ctr32
public import VerifiedGarbage.Impl.Words.RISCV64.Word64

/-!
# AES-CTR: RISC-V implementation

`vg_aes_ctr(schedule = a0, rounds = a1, ctr = a2, data = a3, n = a4, scratch = a5)`
(see `VG.Spec.Ctr.aesContract`), composed of calls of the verified
`vg_aes_ctr32` on as many blocks as it can take at once, as on PPC64LE
(`VG.Impl.AesCtr.PPC64LE`).

It is built from AES-CBC's pieces (`Impl/AesCbc/RISCV64.lean`), whose
arguments are the same: the registers and the return address saved in the
scratch buffer and the arguments kept in `s1` (schedule), `s2` (rounds),
`s3` (the counter block), `s4` (the next block), `s5` (blocks left) and
`s6` (scratch).

`vg_aes_ctr32` increments only the last 32 bits of the counter block. So,
as OpenSSL's `CRYPTO_ctr128_encrypt_ctr32` does, each call takes
`m = min(left, 2³² − c)` blocks, with `c` the last 32 bits of the counter
block (`count`, kept in the scratch buffer at `sv`, where CBC's decryption
saves its block, across the call). The minimum is selected by a mask made
from `sltu`. The call leaves the counter block `m` further on in those
bits, and if they wrapped around to 0, the first 96 bits are incremented
(`carry`: the second half plus `2³²`, and the first half plus the carry out
of it, `1` iff the sum is below `2³²`). The contracts state no alignment for
the counter block, so its words are loaded and stored a byte at a time,
big-endian.

Only the pointers, `rounds`, `n` and the last 32 bits of the counter block
can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesCtr.RISCV64

open VG.RISCV64 VG.Impl.Words.RISCV64
open VG.Impl.AesCbc.RISCV64 (mov savePtr whole)

/-- The blocks of this call, `m = min(left, 2³² − c)`, in `t2` and saved at
`sv`. -/
def count : List Instr :=
  loadBE32 .t1 .t2 .s3 12 ++
  [.li .t2 1, .shift .sll .d .t2 .t2 32, .sub .t2 .t2 .t1,
   .sltu .t3 .s5 .t2, .li .t4 0, .sub .t3 .t4 .t3,
   .logic .xor .t4 .s5 .t2, .logic .and .t4 .t4 .t3, .logic .xor .t2 .t2 .t4] ++
  savePtr .s6 ++ [.store .d .t2 .t0 0]

/-- The arguments of `vg_aes_ctr32` on them: the schedule, the rounds, the
counter block, the blocks, their number and the working space. -/
def args : List Instr :=
  [mov .a0 .s1, mov .a1 .s2, mov .a2 .s3, mov .a3 .s4, mov .a4 .t2, mov .a5 .s6]

/-- On past them, with the last 32 bits of the counter block in `t1`. -/
def adv : List Instr :=
  savePtr .s6 ++
  [.load .d .t1 .t0 0, .sub .s5 .s5 .t1, .shift .sll .d .t1 .t1 4, .add .s4 .s4 .t1] ++
  loadBE32 .t1 .t2 .s3 12

/-- The first 96 bits of the counter block plus 1: its second half plus
`2³²`, with the carry into the first, big-endian. -/
def carry : List Instr :=
  loadBE64 .t1 .t2 .s3 8 ++
  [.li .t2 1, .shift .sll .d .t2 .t2 32, .add .t1 .t1 .t2] ++
  storeBE 8 .t1 .t3 .s3 8 ++
  [.sltu .t3 .t1 .t2] ++
  loadBE64 .t1 .t2 .s3 0 ++
  [.add .t1 .t1 .t3] ++
  storeBE 8 .t1 .t2 .s3 0

/-- A call of `vg_aes_ctr32`. -/
def ctrCall : Prog isa := .call "vg_aes_ctr32" Impl.Aes.RISCV64.ctr32

/-- One call: the blocks it takes, the call, on past them, and the carry if
the counter wrapped around. -/
def body : Prog isa :=
  .seq (.block (count ++ args)) (.seq ctrCall (.seq (.block adv)
    (.ite (.zero .t1) (.block carry) (.block []))))

def crypt : Prog isa := whole body

end VG.Impl.AesCtr.RISCV64
