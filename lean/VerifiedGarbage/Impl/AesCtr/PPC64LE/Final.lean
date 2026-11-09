module

public import VerifiedGarbage.Impl.AesCtr.PPC64LE
public import VerifiedGarbage.Impl.AesCfb.PPC64LE.Final

/-!
# AES-CTR of a message's last piece: PPC64LE implementation

`cryptFinal` (schedule = r3, rounds = r4, ctr = r5, data = r6, len = r7,
scratch = r8, save = r9): the code of `vg_aes_ctr_final`, whose registration
frames it with a buffer of its own on the stack, `save`, the seventh
argument, of 80 bytes: the return address and the caller's callee-saved
registers, then a block of the code's own.

1. the return address (through `r0`) and the registers saved in `save`, and
   the arguments kept in `r14` (schedule), `r15` (rounds), `r16` (ctr),
   `r19` (scratch), `r31` (the data after its whole blocks), `r30`
   (`u = len mod 16`, the bytes after them) and `r20` (`save`), as AES-CFB's
   final functions do (`Impl/AesCfb/PPC64LE/Final.lean`);
2. a call of the whole-block function `vg_aes_ctr`
   (`Impl/AesCtr/PPC64LE.lean`) on the `len / 16` whole blocks, which leaves
   `Tₙ₊₁` in `ctr`;
3. if `u ≠ 0`, the block after the registers in `save` zeroed, a call of
   the same function on that one block, which leaves `CIPH_K(Tₙ₊₁)` there and
   `Tₙ₊₂` in `ctr`, and the first `u` bytes of the block XORed into the `u`
   bytes left, a byte at a time (the modes' `tailByte`, from `r8`, the
   block, into `r31`, `r30` bytes);
4. the registers and the return address restored.

The registration's frame zeroes `save`, the block included, on return.

Only the pointers, `rounds`, `len` and the last 32 bits of the counter block
can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesCtr.PPC64LE

open VG.PPC64LE
open VG.Impl.AesCbc.PPC64LE (mov)
open VG.Impl.AesCfb.PPC64LE (finalSetup finalRestore)
open VG.Impl.Modes.PPC64LE (tailByte)

/-- The two doublewords of the block after the registers in `save`, each
zeroed from `r9`. -/
def zeroSlots : List (Reg × Nat) := [(.r9, 64), (.r9, 72)]

/-- The arguments of the whole-block function on that block: the schedule,
the rounds, the counter block, the block, `n = 1`, and the working space. -/
def tailMoves : List Instr :=
  [mov .r3 .r14, mov .r4 .r15, mov .r5 .r16, .addi .r6 .r20 64, .li .r7 1, mov .r8 .r19]

/-- The block, from `save` in `r20`, zeroed, and the arguments of the
whole-block function on it. -/
def tailArgs : List Instr :=
  .li .r9 0 :: (zeroSlots.map fun p => .store .d p.1 .r20 p.2) ++ tailMoves

/-- The block's address, from `save` in `r20`, for the XOR. -/
def tailKey : List Instr := [.addi .r8 .r20 64]

/-- A call of the whole-block function. -/
def wholeCall : Prog isa := .call "vg_aes_ctr" crypt

/-- The partial last block: the output block `CIPH_K(Tₙ₊₁)` in the block of
`save`, by a call of the whole-block function on it, and its first `u`
bytes XORed into the data. -/
def finalTail : Prog isa :=
  .seq (.block tailArgs) (.seq wholeCall
    (.seq (.block tailKey) (.loop (.block tailByte) (.nonzero .d .r30))))

/-- `vg_aes_ctr_final`, calling `vg_aes_ctr`. -/
def cryptFinal : Prog isa :=
  .seq (.block finalSetup) (.seq wholeCall
    (.seq (.ite (.zero .d .r30) (.block []) finalTail) (.block finalRestore)))

end VG.Impl.AesCtr.PPC64LE
