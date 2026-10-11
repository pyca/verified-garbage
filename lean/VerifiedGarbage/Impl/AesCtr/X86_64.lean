module

public import VerifiedGarbage.Impl.AesCbc.X86_64
public import VerifiedGarbage.Impl.Aes.X86_64.Callee

/-!
# AES-CTR: x86-64 implementation

`vg_aes_ctr(schedule = rdi, rounds = rsi, ctr = rdx, data = rcx, n = r8, scratch = r9)`
(see `VG.Spec.Ctr.aesContract`), composed of calls of the verified
`vg_aes_ctr32` on as many blocks as it can take at once. It is generic over
the implementation it calls (`Ctr32`): it is emitted once for each
implementation (e.g. `vg_aes_ctr_aesni` calls `vg_aes_ctr32_aesni`).

It is built from AES-CBC's pieces (`Impl/AesCbc/X86_64.lean`), whose
arguments are the same: the registers saved in the scratch buffer and the
arguments kept in `rbx` (schedule), `rbp` (rounds), `r12` (the counter
block), `r13` (the next block), `r14` (blocks left) and `r15` (scratch).

`vg_aes_ctr32` increments only the last 32 bits of the counter block. So,
as OpenSSL's `CRYPTO_ctr128_encrypt_ctr32` does, each call takes
`m = min(left, 2³² − c)` blocks, with `c` the last 32 bits of the counter
block (`count`, kept at `scratch + 2048` across the call); the call leaves
the counter block `m` further on in those bits, and if they wrapped around
to 0, the first 96 bits are incremented (`carry`: the second half plus
`2³²`, with the carry into the first, both byte-reversed with `bswap`).

Only the pointers, `rounds`, `n` and the last 32 bits of the counter block
can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesCtr.X86_64

open VG.X86_64
open VG.Impl.Aes.X86_64 (Ctr32)
open VG.Impl.AesCbc.X86_64 (save setup restore at_ cOff)

/-- The blocks of this call, `m = min(left, 2³² − c)`, in `rcx` and saved in
the scratch buffer. -/
def count : List Instr :=
  [.mov32 .rax (.mem (at_ .r12 12)), .bswap32 .rax, .movImm64 .rcx 0x100000000,
   .alu .sub .rcx (.reg .rax), .alu .cmp .r14 (.reg .rcx), .cmov .b .rcx (.reg .r14),
   .store (at_ .r15 cOff) .rcx]

/-- The arguments of `vg_aes_ctr32` on them: the schedule, the rounds, the
counter block, the blocks, their number and the working space. -/
def args : List Instr :=
  [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r12), .mov .r8 (.reg .rcx),
   .mov .rcx (.reg .r13), .mov .r9 (.reg .r15)]

/-- On past them, and ZF set if the last 32 bits of the counter block
wrapped around to 0. -/
def adv : List Instr :=
  [.mov .rax (.mem (at_ .r15 cOff)), .alu .sub .r14 (.reg .rax), .shift .shl .rax 4,
   .alu .add .r13 (.reg .rax), .mov32 .rax (.mem (at_ .r12 12)), .alu32 .test .rax (.reg .rax)]

/-- The first 96 bits of the counter block plus 1: its second half plus
`2³²`, with the carry into the first, big-endian. -/
def carry : List Instr :=
  [.mov .rax (.mem (at_ .r12 8)), .bswap .rax, .mov .rcx (.mem (at_ .r12 0)), .bswap .rcx,
   .movImm64 .rdx 0x100000000, .alu .add .rax (.reg .rdx), .alu .adc .rcx (.imm 0),
   .bswap .rax, .bswap .rcx, .store (at_ .r12 8) .rax, .store (at_ .r12 0) .rcx]

/-- One call: the blocks it takes, the call, on past them, the carry if the
counter wrapped around, and ZF set if no blocks are left. -/
def body (c : Ctr32) : Prog isa :=
  .seq (.block (count ++ args)) (.seq (.call c.name c.code) (.seq (.block adv)
    (.seq (.ite .e (.block carry) (.block [])) (.block [.alu .test .r14 (.reg .r14)]))))

def crypt (c : Ctr32) : Prog isa :=
  .seq (.block (save ++ setup)) (.seq (.ite .e (.block []) (.loop (body c) .ne)) (.block restore))

end VG.Impl.AesCtr.X86_64
