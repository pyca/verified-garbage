module

public import VerifiedGarbage.Impl.AesCtr.AArch64
public import VerifiedGarbage.Impl.AesCfb.AArch64.Final
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.Impl.Residue.AArch64.Union

/-!
# AES-CTR of a message's last piece: AArch64 implementation

`cryptFinal c sfx` (schedule = x0, rounds = x1, ctr = x2, data = x3,
len = x4, scratch = x5, save = x6): the code of `vg_aes_ctr_final`, whose
registration frames it with a buffer of its own on the stack, `save`, the
seventh argument, of 80 bytes: the caller's callee-saved registers and the
return address, then a block of the code's own. It is generic over the
implementation of `vg_aes_ctr32` that the whole-block function calls (`c`,
whose callers' names end in `sfx`, e.g. `_aes`):

1. the registers saved in `save`, and the arguments kept in `x19`
   (schedule), `x20` (rounds), `x21` (ctr), `x22` (the data after its whole
   blocks), `x23` (`u = len mod 16`, the bytes after them), `x24` (scratch)
   and `x25` (`save`), as AES-CFB's final functions do
   (`Impl/AesCfb/AArch64/Final.lean`);
2. a call of the whole-block function of the same implementation
   (`vg_aes_ctr` and its variants, `Impl/AesCtr/AArch64.lean`) on the
   `len / 16` whole blocks, which leaves `Tₙ₊₁` in `ctr`;
3. if `u ≠ 0`, the block after the registers in `save` zeroed, a call of the
   same function on that one block, which leaves `CIPH_K(Tₙ₊₁)` there and
   `Tₙ₊₂` in `ctr`, and the first `u` bytes of the block XORed into the `u`
   bytes left, a byte at a time (the modes' `xorByte`);
4. the registers restored.

The function as emitted zeroes `save`, the block included, on return.

Only the pointers, `rounds`, `len` and the last 32 bits of the counter block
can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesCtr.AArch64

open VG.AArch64
open VG.Impl.Aes.AArch64 (Ctr32)
open VG.Impl.AesCbc.AArch64 (mov)
open VG.Impl.AesCfb.AArch64 (finalSetup finalRestore)
open VG.Impl.Modes.AArch64 (xorByte)

/-- The two doublewords of the block after the registers in `save`, each
zeroed from `x9`. -/
def zeroSlots : List (Reg × Nat) := [(.x9, 64), (.x9, 72)]

/-- The arguments of the whole-block function on that block: the schedule,
the rounds, the counter block, the block, `n = 1`, and the working space. -/
def tailMoves : List Instr :=
  [mov .x0 .x19, mov .x1 .x20, mov .x2 .x21, .addImm .x .x3 .x25 64, .movz .x .x4 1 0, mov .x5 .x24]

/-- The block, from `save` in `x25`, zeroed, and the arguments of the
whole-block function on it. -/
def tailArgs : List Instr :=
  .movz .x .x9 0 0 :: (zeroSlots.map fun p => .str .x p.1 .x25 p.2) ++ tailMoves

/-- The block's address, from `save` in `x25`, for the XOR. -/
def tailKey : List Instr := [.addImm .x .x9 .x25 64]

/-- The partial last block: the output block `CIPH_K(Tₙ₊₁)` in the block of
`save`, by a call of the whole-block function `name`, `whole`, on it, and its
first `u` bytes XORed into the data. -/
def finalTail (name : String) (whole : Prog isa) : Prog isa :=
  .seq (.block tailArgs) (.seq (.call name whole)
    (.seq (.block tailKey) (.loop (.block (xorByte .x22 .x23)) (.nonzero .x .x23))))

/-- The whole function, around calls of the whole-block function `name`,
`whole`. -/
def final (name : String) (whole : Prog isa) : Prog isa :=
  .seq (.block finalSetup) (.seq (.call name whole)
    (.seq (.ite (.zero .x .x23) (.block []) (finalTail name whole)) (.block finalRestore)))

/-- `vg_aes_ctr_final`, calling `vg_aes_ctr`'s code with `vg_aes_ctr32`'s
implementation `c`, whose callers' names end in `sfx`, as an internal
function of its own, `vg_aes_ctr<sfx>_core`: `vg_aes_ctr` also clears the
registers it leaves (`Proof.Aes.AArch64.ModesScrub.ctrOk`). -/
def cryptFinal (c : Ctr32) (sfx : String) : Prog isa := final ("vg_aes_ctr" ++ sfx ++ "_core") (crypt c)

/-! ## The functions, as emitted

Each function is its code, then its cleanup
(`Impl.Residue.AArch64.scrubAll`): the registers it writes that the calling
convention does not preserve are cleared, and the stack it uses is zeroed,
so that it returns without secret residue. The registers are those its own
instructions write, stated here, and those the implementation of
`vg_aes_ctr32` it calls states it writes (`c.clear`). -/

namespace Fn

open VG.Impl.Residue.AArch64 (Clear scrubAll)

/-- The registers `vg_aes_ctr`'s own instructions write. -/
def cryptOwn : Clear := ⟨[.x1, .x2, .x3, .x4, .x5, .x9, .x10, .x11, .x12, .x16, .x17], [], []⟩

/-- `vg_aes_ctr`: `crypt`, its registers cleared; it uses no stack. -/
def crypt (c : Ctr32) : Prog isa :=
  scrubAll 0 0 (cryptOwn.union c.clear) (AesCtr.AArch64.crypt c)

/-- The registers `vg_aes_ctr_final`'s own instructions write. -/
def cryptFinalOwn : Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x9, .x10, .x11, .x12, .x16, .x17], [], []⟩

/-- `vg_aes_ctr_final`: `cryptFinal` with `save` in its frame, its registers
cleared and its 80 bytes of stack zeroed. -/
def cryptFinal (c : Ctr32) (sfx : String) : Prog isa :=
  scrubAll 80 0 (cryptFinalOwn.union c.clear)
    (Impl.StackScratch.AArch64.withStackScratchWiped 80 .x6 10 (AesCtr.AArch64.cryptFinal c sfx))

end Fn

end VG.Impl.AesCtr.AArch64
