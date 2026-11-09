module

public import VerifiedGarbage.Impl.AesCtr.X86_64
public import VerifiedGarbage.Impl.AesCfb.X86_64.Final

/-!
# AES-CTR of a message's last piece: x86-64 implementation

`cryptFinal c sfx` (schedule = rdi, rounds = rsi, ctr = rdx, data = rcx,
len = r8, scratch = r9, save = `[rsp + 8]`): the code of `vg_aes_ctr_final`,
whose registration frames it with a buffer of its own on the stack, `save`,
the seventh argument, of 64 bytes: the caller's callee-saved registers, then
a block of the code's own. It is generic over the implementation of
`vg_aes_ctr32` that the whole-block function calls (`c`, whose callers'
names end in `sfx`, e.g. `_aesni`):

1. the registers saved in `save`, and the arguments kept in `rbx`
   (schedule), `rbp` (rounds), `r12` (ctr), `r13` (the data after its whole
   blocks), `r14` (`u = len mod 16`, the bytes after them) and `r15`
   (scratch), as AES-CFB's final functions do
   (`Impl/AesCfb/X86_64/Final.lean`);
2. a call of the whole-block function of the same implementation
   (`vg_aes_ctr` and its variants, `Impl/AesCtr/X86_64.lean`) on the
   `len / 16` whole blocks, which leaves `Tₙ₊₁` in `ctr`;
3. if `u ≠ 0`, the block after the registers in `save` zeroed, a call of the
   same function on that one block, which leaves `CIPH_K(Tₙ₊₁)` there and
   `Tₙ₊₂` in `ctr`, and the first `u` bytes of the block XORed into the `u`
   bytes left, a byte at a time (the modes' `xorByte`);
4. the registers restored.

The registration's frame zeroes `save`, the block included, on return.

Only the pointers, `rounds`, `len` and the last 32 bits of the counter block
can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesCtr.X86_64

open VG.X86_64
open VG.Impl.Aes.X86_64 (Ctr32)
open VG.Impl.AesCfb.X86_64 (loadSave finalSetup finalRestore)
open VG.Impl.Modes.X86_64 (xorByte)

/-- The two quadwords of the block after the registers in `save`, each
zeroed from `r10`. -/
def zeroSlots : List (Reg × Nat) := [(.r10, 48), (.r10, 56)]

/-- The arguments of the whole-block function on that block: the schedule,
the rounds, the counter block, the block, `n = 1`, and the working space. -/
def tailMoves : List Instr :=
  [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r12), .mov .rcx (.reg .rax),
   .alu .add .rcx (.imm 48), .mov32 .r8 (.imm 1), .mov .r9 (.reg .r15)]

/-- The block, from `save` in `rax`, zeroed, and the arguments of the
whole-block function on it. -/
def tailArgs : List Instr :=
  .mov32 .r10 (.imm 0) :: (zeroSlots.map fun p => .store { base := .rax, disp := p.2 } p.1) ++ tailMoves

/-- The block's address, from `save` in `rax`. -/
def tailKey : List Instr := [.alu .add .rax (.imm 48)]

/-- The partial last block: the output block `CIPH_K(Tₙ₊₁)` in the block of
`save`, by a call of the whole-block function `name`, `whole`, on it, and its
first `u` bytes XORed into the data. -/
def finalTail (name : String) (whole : Prog isa) : Prog isa :=
  .seq (.block loadSave) (.seq (.block tailArgs) (.seq (.call name whole)
    (.seq (.block loadSave) (.seq (.block tailKey) (.loop (.block (xorByte .r13 .r14)) .ne)))))

/-- The whole function, around calls of the whole-block function `name`,
`whole`. -/
def final (name : String) (whole : Prog isa) : Prog isa :=
  .seq (.block loadSave) (.seq (.block finalSetup) (.seq (.call name whole)
    (.seq (.block [.alu .test .r14 (.reg .r14)]) (.seq (.ite .e (.block []) (finalTail name whole))
      (.seq (.block loadSave) (.block finalRestore))))))

/-- `vg_aes_ctr_final`, calling `vg_aes_ctr` with `vg_aes_ctr32`'s
implementation `c`, whose callers' names end in `sfx`. -/
def cryptFinal (c : Ctr32) (sfx : String) : Prog isa := final ("vg_aes_ctr" ++ sfx) (crypt c)

end VG.Impl.AesCtr.X86_64
