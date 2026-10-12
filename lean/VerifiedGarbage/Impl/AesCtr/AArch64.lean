module

public import VerifiedGarbage.Impl.AesCbc.AArch64

/-!
# AES-CTR: AArch64 implementation

`vg_aes_ctr(schedule = x0, rounds = x1, ctr = x2, data = x3, n = x4, scratch = x5)`
(see `VG.Spec.Ctr.aesContract`), composed of calls of the verified
`vg_aes_ctr32` on as many blocks as it can take at once. It is generic over
the implementation it calls (`Ctr32`): it is emitted once for each
implementation (e.g. `vg_aes_ctr_aes` calls `vg_aes_ctr32_aes`).

It is built from AES-CBC's pieces (`Impl/AesCbc/AArch64.lean`), whose
arguments are the same: the registers saved in the scratch buffer and the
arguments kept in `x19` (schedule), `x20` (rounds), `x21` (the counter
block), `x22` (the next block), `x23` (blocks left) and `x24` (scratch).

`vg_aes_ctr32` increments only the last 32 bits of the counter block. So,
as OpenSSL's `CRYPTO_ctr128_encrypt_ctr32` does, each call takes
`m = min(left, 2³² − c)` blocks, with `c` the last 32 bits of the counter
block (`count`, kept at `scratch + 2048` across the call); the call leaves
the counter block `m` further on in those bits, and if they wrapped around
to 0 (`cbz`), the first 96 bits are incremented (`carry`: the second half
plus `2³²`, with the carry into the first, both byte-reversed with `rev`).

Only the pointers, `rounds`, `n` and the last 32 bits of the counter block
can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesCtr.AArch64

open VG.AArch64
open VG.Impl.Aes.AArch64 (Ctr32)
open VG.Impl.AesCbc.AArch64 (mov cOff whole)

/-- The blocks of this call, `m = min(left, 2³² − c)`, in `x10` and saved in
the scratch buffer: `subs` sets C if `left ≥ 2³² − c`, and `csel` (`hs`)
then takes `2³² − c`. -/
def count : List Instr :=
  [.ldr .w .x9 .x21 12, .rev32 .x9 .x9, .movz .x .x10 1 2, .sub .x .x10 .x10 .x9,
   .subs .x .x11 .x23 .x10, .csel .x .x10 .x10 .x23, .str .x .x10 .x24 cOff]

/-- The arguments of `vg_aes_ctr32` on them: the schedule, the rounds, the
counter block, the blocks, their number and the working space. -/
def args : List Instr :=
  [mov .x0 .x19, mov .x1 .x20, mov .x2 .x21, mov .x3 .x22, mov .x4 .x10, mov .x5 .x24]

/-- On past them, and the last 32 bits of the counter block in `w9`, which
are 0 if they wrapped around. -/
def adv : List Instr :=
  [.ldr .x .x9 .x24 cOff, .sub .x .x23 .x23 .x9, .lsl .x .x9 .x9 4, .add .x .x22 .x22 .x9,
   .ldr .w .x9 .x21 12]

/-- The first 96 bits of the counter block plus 1: its second half plus
`2³²`, with the carry into the first, big-endian. -/
def carry : List Instr :=
  [.ldr .x .x9 .x21 8, .rev .x9 .x9, .ldr .x .x10 .x21 0, .rev .x10 .x10, .movz .x .x11 1 2,
   .movz .x .x12 0 0, .adds .x .x9 .x9 .x11, .adc .x .x10 .x10 .x12, .rev .x9 .x9, .rev .x10 .x10,
   .str .x .x9 .x21 8, .str .x .x10 .x21 0]

/-- One call: the blocks it takes, the call, on past them, and the carry if
the counter wrapped around. -/
def body (c : Ctr32) : Prog isa :=
  .seq (.block (count ++ args)) (.seq (.call c.name c.code)
    (.seq (.block adv) (.ite (.zero .w .x9) (.block carry) (.block []))))

def crypt (c : Ctr32) : Prog isa := whole (body c)

end VG.Impl.AesCtr.AArch64
