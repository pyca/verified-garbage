module

public import VerifiedGarbage.Impl.Modes.AArch64.Cbc

/-!
# ECB on AArch64, for any block cipher with blocks of 8 or 16 bytes

`ecb core data n scr` (SP 800-38A §6.1) over a block cipher's core (`Core`,
as for CTR and CBC decryption), whose `crypt` applies the cipher, or its
inverse, to the `G` blocks of its buffer: each group of up to `G` blocks is
copied to the buffer (`copyBlocks`), `core.crypt` runs there, and the group
is copied back. For a core of one block this is a call's blocks one at a
time, which a short call takes when the cipher's batch costs more.

* The scratch buffer moves to `sb`, the callee-saved registers to the
  mode's slots, the data's address and `n` to `dataReg` and `leftReg`.
* `core.prepare` makes the key ready.

Only the pointers and `n` (and what is computed from them) are public; no
address or branch depends on the key or the data.
-/

@[expose] public section

namespace VG.Impl.Modes.AArch64

open VG.AArch64 VG.Impl.Aes.AArch64

namespace Core

variable (c : Core)

/-- The data's address to `x14`, the buffer's to `x15`, the count to `x17`. -/
def backArgs : List Instr :=
  [movR .x15 sb, .addImm .x .x15 .x15 (8 * c.buf), movR .x14 c.dataReg, movR .x17 .x16]

/-- On past the group's blocks, from `x14`. -/
def ecbAdvance : List Instr := [movR c.dataReg .x14, .sub .x c.leftReg c.leftReg .x16]

/-- One group: its blocks to the buffer, the cipher, and back to the data. -/
def ecbGroup : Prog isa :=
  .seq c.groupCount (.seq (.block c.xorArgs) (.seq c.copyBlocks (.seq c.crypt
    (.seq c.groupCount (.seq (.block c.backArgs) (.seq c.copyBlocks (.block c.ecbAdvance)))))))

/-- The registers of ECB's arguments, as the modes' (it has no IV). -/
def ecbRegs (data n scr : Reg) : CtrRegs := ⟨scr, data, n, scr⟩

/-- ECB of the `n` blocks at `data`, with the working space at `scr`. -/
def ecb (data n scr : Reg) : Prog isa :=
  .seq (.block (c.ctrEntry (ecbRegs data n scr) ++ c.ctrArgs (ecbRegs data n scr)))
    (.seq c.prepare
      (.seq (.ite (.zero .x c.leftReg) (.block []) (.loop c.ecbGroup (.nonzero .x c.leftReg)))
        (.block c.restoreRegs)))

end Core

end VG.Impl.Modes.AArch64
