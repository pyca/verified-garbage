module

public import VerifiedGarbage.Impl.AesCtr.RISCV64
public import VerifiedGarbage.Impl.AesCfb.RISCV64.Final

/-!
# AES-CTR of a message's last piece: RISC-V implementation

`cryptFinal` (schedule = a0, rounds = a1, ctr = a2, data = a3, len = a4,
scratch = a5, save = a6): the code of `vg_aes_ctr_final`, whose
registration frames it with a buffer of its own on the stack, `save`, the
seventh argument, of 80 bytes: the return address and the caller's
callee-saved registers, then a block of the code's own.

1. the registers saved in `save`, and the arguments kept in `s1`
   (schedule), `s4` (rounds), `s5` (ctr), `s6` (scratch), `s2` (the data
   after its whole blocks), `s3` (`u = len mod 16`, the bytes after them) and
   `s7` (`save`), as AES-CFB's final functions do
   (`Impl/AesCfb/RISCV64/Final.lean`);
2. a call of the whole-block function `vg_aes_ctr`
   (`Impl/AesCtr/RISCV64.lean`) on the `len / 16` whole blocks, which leaves
   `Tₙ₊₁` in `ctr`;
3. if `u ≠ 0`, the block after the registers in `save` zeroed, a call of the
   same function on that one block, which leaves `CIPH_K(Tₙ₊₁)` there and
   `Tₙ₊₂` in `ctr`, and the first `u` bytes of the block XORed into the `u`
   bytes left, a byte at a time (the modes' `xorStep`, from `t2`, the block,
   into `s2`, `s3` bytes);
4. the registers restored.

The registration's frame zeroes `save`, the block included, on return.

Only the pointers, `rounds`, `len` and the last 32 bits of the counter block
can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesCtr.RISCV64

open VG.RISCV64
open VG.Impl.AesCbc.RISCV64 (mov)
open VG.Impl.AesCfb.RISCV64 (finalSetup finalRestore)
open VG.Impl.Modes.RISCV64 (xorStep)

/-- The two doublewords of the block after the registers in `save`, each
zeroed from `t0`. -/
def zeroSlots : List (Reg × Nat) := [(.t0, 64), (.t0, 72)]

/-- The arguments of the whole-block function on that block: the schedule,
the rounds, the counter block, the block, `n = 1`, and the working space. -/
def tailMoves : List Instr :=
  [mov .a0 .s1, mov .a1 .s4, mov .a2 .s5, .addi .a3 .s7 64, .li .a4 1, mov .a5 .s6]

/-- The block, from `save` in `s7`, zeroed, and the arguments of the
whole-block function on it. -/
def tailArgs : List Instr :=
  .li .t0 0 :: (zeroSlots.map fun p => .store .d p.1 .s7 p.2) ++ tailMoves

/-- The block's address, from `save` in `s7`, for the XOR. -/
def tailKey : List Instr := [.addi .t2 .s7 64]

/-- The partial last block: the output block `CIPH_K(Tₙ₊₁)` in the block of
`save`, by a call of `vg_aes_ctr` on it, and its first `u` bytes XORed into
the data. -/
def finalTail : Prog isa :=
  .seq (.block tailArgs) (.seq (.call "vg_aes_ctr" crypt)
    (.seq (.block tailKey) (.loop (.block xorStep) (.nonzero .s3))))

/-- `vg_aes_ctr_final`, calling `vg_aes_ctr`. -/
def cryptFinal : Prog isa :=
  .seq (.block finalSetup) (.seq (.call "vg_aes_ctr" crypt)
    (.seq (.ite (.zero .s3) (.block []) finalTail) (.block finalRestore)))

end VG.Impl.AesCtr.RISCV64
