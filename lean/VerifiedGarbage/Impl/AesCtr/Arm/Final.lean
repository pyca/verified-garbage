module

public import VerifiedGarbage.Impl.AesCtr.Arm
public import VerifiedGarbage.Impl.AesCfb.Arm.Final

/-!
# AES-CTR of a message's last piece: 32-bit ARM implementation

`cryptFinal` (schedule = r0, rounds = r1, ctr = r2, data = r3, len = `[sp]`,
scratch = `[sp + 4]`, save = `[sp + 8]`): the code of `vg_aes_ctr_final`,
whose registration frames it with a buffer of its own on the stack, `save`,
the seventh argument, of 56 bytes: the caller's callee-saved registers and
its return address, then, at 40, a block of the code's own:

1. the registers saved in `save`, and the arguments kept in `r4`
   (schedule), `r5` (rounds), `r6` (ctr), `r7` (the data after its whole
   blocks), `r8` (`u = len mod 16`, the bytes after them) and `r10`
   (scratch), as AES-CFB's final functions do
   (`Impl/AesCfb/Arm/Final.lean`);
2. a call of `vg_aes_ctr` (`Impl/AesCtr/Arm.lean`) on the `len / 16` whole
   blocks, in a frame that pushes its stack arguments, which leaves `Tₙ₊₁`
   in `ctr`;
3. if `u ≠ 0`, the block at `save + 40` zeroed, a call of `vg_aes_ctr` on
   that one block, which leaves `CIPH_K(Tₙ₊₁)` there and `Tₙ₊₂` in `ctr`, and
   the first `u` bytes of the block XORed into the `u` bytes left, a byte at
   a time (the modes' `xorByte`);
4. the registers restored from `save`, whose address is reloaded from the
   stack.

The registration's frame zeroes `save`, the block included, on return.
Only the pointers, `rounds` and `len` can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesCtr.Arm

open VG.Arm
open VG.Impl.CmacAes.Arm (mov)
open VG.Impl.AesCfb.Arm (loadSave finalSetup wholeFrame finalEnd)
open VG.Impl.Modes.Arm (xorByte)

/-- The block at `save + 40` zeroed, through `r0`. -/
def zeroArgs : List Instr :=
  [.mov .r0 (.imm 0), .str .r0 .r12 40, .str .r0 .r12 44, .str .r0 .r12 48, .str .r0 .r12 52]

/-- The arguments of the whole-block function on that block: the schedule,
the rounds, the counter block, the block, and in `r12` and `lr`, to push,
`n = 1` and the scratch buffer. -/
def oneArgs : List Instr :=
  [mov .r0 .r4, mov .r1 .r5, mov .r2 .r6, .dp .add .r3 .r12 (.imm 40),
   .mov .r12 (.imm 1), mov .lr .r10]

/-- `save` loaded, the block zeroed, and the arguments on it. -/
def tailArgs : List Instr := loadSave ++ zeroArgs ++ oneArgs

/-- The arguments of the XOR: the block (`r0`), the data after the whole
blocks (`r6`) and the bytes left (`r7`). -/
def xorArgs : List Instr :=
  loadSave ++ [.dp .add .r0 .r12 (.imm 40), mov .r6 .r7, mov .r7 .r8]

/-- The partial last block: the output block `CIPH_K(Tₙ₊₁)` in the block of
`save`, by a call of the whole-block function `name`, `whole`, on it, and its
first `u` bytes XORed into the data. -/
def finalTail (name : String) (whole : Prog isa) : Prog isa :=
  .seq (.block tailArgs) (.seq (wholeFrame name whole) (.seq (.block xorArgs) (.loop (.block xorByte) .ne)))

/-- The whole function, around calls of the whole-block function `name`,
`whole`. -/
def final (name : String) (whole : Prog isa) : Prog isa :=
  .seq (.block finalSetup) (.seq (wholeFrame name whole)
    (.seq (.block [.cmp .r8 (.imm 0)]) (.seq (.ite .eq (.block []) (finalTail name whole)) (.block finalEnd))))

/-- `vg_aes_ctr_final`, calling `vg_aes_ctr`. -/
def cryptFinal : Prog isa := final "vg_aes_ctr" crypt

end VG.Impl.AesCtr.Arm
