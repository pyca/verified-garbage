module

public import VerifiedGarbage.Impl.AesCbc.PPC64LE
public import VerifiedGarbage.Impl.Aes.PPC64LE.Ctr32

/-!
# AES-CTR: PPC64LE implementation

`vg_aes_ctr(schedule = r3, rounds = r4, ctr = r5, data = r6, n = r7, scratch = r8)`
(see `VG.Spec.Ctr.aesContract`), composed of calls of the verified
`vg_aes_ctr32` on as many blocks as it can take at once, as on x86-64
(`VG.Impl.AesCtr.X86_64`).

It is built from AES-CBC's pieces (`Impl/AesCbc/PPC64LE.lean`), whose
arguments are the same: the registers and the return address saved in the
scratch buffer and the arguments kept in `r14` (schedule), `r15` (rounds),
`r16` (the counter block), `r17` (the next block), `r18` (blocks left) and
`r19` (scratch).

`vg_aes_ctr32` increments only the last 32 bits of the counter block. So,
as OpenSSL's `CRYPTO_ctr128_encrypt_ctr32` does, each call takes
`m = min(left, 2³² − c)` blocks, with `c` the last 32 bits of the counter
block (`count`, kept at `scratch + 2048` across the call). The model has no
compare instructions: `left < 2³² − c` is the sign of their difference
(both are below `2⁶³`), and the minimum is selected by a mask made from it.
The call leaves the counter block `m` further on in those bits, and if they
wrapped around to 0, the first 96 bits are incremented (`carry`: the second
half plus `2³²`, and the first half plus the carry out of it, `1` iff the
sum's upper half is 0, both through byte-reversing loads and stores).

Only the pointers, `rounds`, `n` and the last 32 bits of the counter block
can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesCtr.PPC64LE

open VG.PPC64LE
open VG.Impl.AesCbc.PPC64LE (mov cOff whole)

/-- The blocks of this call, `m = min(left, 2³² − c)`, in `r10` and saved in
the scratch buffer. -/
def count : List Instr :=
  [.li .r10 12, .loadRev .w .r9 .r16 .r10, .li .r10 1, .lsl .r10 .r10 32, .sub .r10 .r10 .r9,
   .sub .r11 .r18 .r10, .lsr .d .r11 .r11 63, .li .r12 0, .sub .r11 .r12 .r11,
   .logic .xor .r12 .r18 .r10, .logic .and .r12 .r12 .r11, .logic .xor .r10 .r10 .r12,
   .store .d .r10 .r19 cOff]

/-- The arguments of `vg_aes_ctr32` on them: the schedule, the rounds, the
counter block, the blocks, their number and the working space. -/
def args : List Instr :=
  [mov .r3 .r14, mov .r4 .r15, mov .r5 .r16, mov .r6 .r17, mov .r7 .r10, mov .r8 .r19]

/-- On past them, with the last 32 bits of the counter block in `r9`. -/
def adv : List Instr :=
  [.load .d .r9 .r19 cOff, .sub .r18 .r18 .r9, .lsl .r9 .r9 4, .add .r17 .r17 .r9,
   .li .r10 12, .loadRev .w .r9 .r16 .r10]

/-- The first 96 bits of the counter block plus 1: its second half plus
`2³²`, with the carry into the first, big-endian. -/
def carry : List Instr :=
  [.li .r10 8, .loadRev .d .r9 .r16 .r10, .li .r11 1, .lsl .r11 .r11 32, .add .r9 .r9 .r11,
   .storeRev .d .r9 .r16 .r10, .lsr .d .r9 .r9 32, .subi .r9 .r9 1, .lsr .d .r9 .r9 63,
   .li .r10 0, .loadRev .d .r11 .r16 .r10, .add .r11 .r11 .r9, .storeRev .d .r11 .r16 .r10]

/-- A call of `vg_aes_ctr32`. -/
def ctrCall : Prog isa := .call "vg_aes_ctr32" Impl.Aes.PPC64LE.ctr32

/-- One call: the blocks it takes, the call, on past them, and the carry if
the counter wrapped around. -/
def body : Prog isa :=
  .seq (.block (count ++ args)) (.seq ctrCall (.seq (.block adv)
    (.ite (.zero .d .r9) (.block carry) (.block []))))

def crypt : Prog isa := whole body

end VG.Impl.AesCtr.PPC64LE
