module

public import VerifiedGarbage.Impl.AesCbc.Arm
public import VerifiedGarbage.Impl.Aes.Arm.Ctr32

/-!
# AES-CTR: ARMv7 implementation

`vg_aes_ctr(schedule = r0, rounds = r1, ctr = r2, data = r3, n, scratch)`
(the last two on the stack; see `VG.Spec.Ctr.aesContract`), composed of
calls of the verified `vg_aes_ctr32` on as many blocks as it can take at
once.

It is built from AES-CBC's pieces (`Impl/AesCbc/Arm.lean`), whose arguments
are the same: the registers saved in the scratch buffer and the arguments
kept in `r4` (schedule), `r5` (rounds), `r6` (the counter block), `r7` (the
next block), `r8` (blocks left) and `r10` (scratch).

`vg_aes_ctr32` increments only the last 32 bits of the counter block. So,
as OpenSSL's `CRYPTO_ctr128_encrypt_ctr32` does, each call takes
`m = min(left, 2³² − c)` blocks, with `c` the last 32 bits of the counter
block (`count`, kept in `r9` across the call); the call leaves the counter
block `m` further on in those bits, and if they wrapped around to 0, the
first 96 bits are incremented (`carry`: three words loaded and
byte-reversed with `rev`, the last plus 1 with `adds`, the carry taken into
`r12` with `adc` and added to the next with `adds`, the first plus the last
carry with `adc`, and each reversed again and stored).

Only the pointers, `rounds`, `n` and the last 32 bits of the counter block
can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesCtr.Arm

open VG.Arm
open VG.Impl.CmacAes.Arm (mov)
open VG.Impl.AesCbc.Arm (whole)

/-- The blocks of this call, `m = min(left, 2³² − c)`, in `r9`, as
`min(left − 1, 2³² − 1 − c) + 1`, neither of which wraps around:
`2³² − 1 − c` is `mvn` of `c`, `subs` sets C if `left − 1` is not below it,
`adc` takes C into `r2`, which `0 − r2` makes a mask, and the mask selects
between the two. -/
def count : List Instr :=
  [.ldr .r0 .r6 12, .rev .r0 .r0, .mvn .r0 (.reg .r0), .dp .sub .r1 .r8 (.imm 1),
   .subs .r2 .r1 (.reg .r0), .mov .r2 (.imm 0), .adc .r2 .r2 (.imm 0), .mov .r3 (.imm 0),
   .dp .sub .r2 .r3 (.reg .r2), .dp .eor .r3 .r1 (.reg .r0), .dp .and .r3 .r3 (.reg .r2),
   .dp .eor .r1 .r1 (.reg .r3), .dp .add .r9 .r1 (.imm 1)]

/-- The arguments of `vg_aes_ctr32` on them: the schedule, the rounds, the
counter block, the blocks, and in `r12` and `lr`, to push, their number and
the working space. -/
def args : List Instr :=
  [mov .r0 .r4, mov .r1 .r5, mov .r2 .r6, mov .r3 .r7, mov .r12 .r9, mov .lr .r10]

/-- `vg_aes_ctr32`, with `n` in `r12` and the working space in `lr` pushed as
its stack arguments. -/
def ctrFrame : Prog isa :=
  .frame (.push [.r12, .lr]) (.call "vg_aes_ctr32" Impl.Aes.Arm.ctr32) (.pop .r12 8)

/-- On past them, and Z set if the last 32 bits of the counter block
wrapped around to 0. -/
def adv : List Instr :=
  [.dp .sub .r8 .r8 (.reg .r9), .dp .add .r7 .r7 (.shifted .r9 .lsl 4), .ldr .r0 .r6 12,
   .cmp .r0 (.imm 0)]

/-- The first 96 bits of the counter block plus 1, big-endian. -/
def carry : List Instr :=
  [.ldr .r0 .r6 8, .rev .r0 .r0, .ldr .r1 .r6 4, .rev .r1 .r1, .ldr .r2 .r6 0, .rev .r2 .r2,
   .adds .r0 .r0 (.imm 1), .mov .r12 (.imm 0), .adc .r12 .r12 (.imm 0),
   .adds .r1 .r1 (.reg .r12), .adc .r2 .r2 (.imm 0),
   .rev .r0 .r0, .str .r0 .r6 8, .rev .r1 .r1, .str .r1 .r6 4, .rev .r2 .r2, .str .r2 .r6 0]

/-- Z set if no blocks are left. -/
def test : List Instr := [.cmp .r8 (.imm 0)]

/-- One call: the blocks it takes, the call, on past them, the carry if the
counter wrapped around, and whether blocks are left. -/
def body : Prog isa :=
  .seq (.block (count ++ args)) (.seq ctrFrame
    (.seq (.block adv) (.seq (.ite .eq (.block carry) (.block [])) (.block test))))

def crypt : Prog isa := whole body

end VG.Impl.AesCtr.Arm
