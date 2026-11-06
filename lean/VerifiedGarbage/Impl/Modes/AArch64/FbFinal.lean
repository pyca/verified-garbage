module

public import VerifiedGarbage.Impl.Modes.AArch64.Fb

/-!
# OFB and CFB of a message's last piece on AArch64, for any block cipher

`fbFinal core mode regs iv`: `fb` (`Fb.lean`) over the `len` bytes at the
data, in segments of a block, `L = 8 bw` bytes, the last of which may be
shorter, as on x86-64 (`Impl/Modes/X86_64/FbFinal.lean`). The number in
`leftReg` is the bytes left, not the blocks. Each segment's input block is
enciphered in the buffer (`crypt`), giving `Oⱼ`; then, if a whole block is
left, `fb`'s step (`fbOp`) and on by `L` bytes; if fewer, `r`, the first `r`
bytes of `Oⱼ` are XORed into the data a byte at a time (`xorByte`) and none
are left. After a partial segment the buffer holds `Oⱼ`, the block to
continue from, which replaces the IV as after a whole one; the core is
called once per segment, so its code appears once.

AArch64 branches only on whether a register is zero, so "fewer than `L`
bytes left" is `leftReg >> lg = 0` (`fbLg`, `L = 2 ^ lg` for blocks of one
or two words), in `x8`.
-/

@[expose] public section

namespace VG.Impl.Modes.AArch64

open VG.AArch64 VG.Impl.Aes.AArch64
open VG.Impl.Modes (FbMode)

/-- The byte at `x9` XORed into the byte at `Rd`, through `x6` and `x7`;
both on to the next byte, and one fewer left in `Rl`. -/
def xorByte (Rd Rl : Reg) : List Instr :=
  [.ldrb .x6 .x9 0, .ldrb .x7 Rd 0, eorR .x7 .x7 .x6, .strb .x7 Rd 0, .addImm .x .x9 .x9 1,
    .addImm .x Rd Rd 1, .subImm .x Rl Rl 1]

namespace Core

variable (c : Core)

/-- `lg` with `8 bw = 2 ^ lg`, for blocks of one or two words. -/
def fbLg : Nat := 2 + c.bw

/-- The buffer's first block's address, to `x9`. -/
def fbTailStart : List Instr := [.addImm .x .x9 sb (8 * c.buf)]

/-- On to the next segment, a whole block. -/
def fbNextBytes : List Instr :=
  [.addImm .x c.dataReg c.dataReg (8 * c.bw), .subImm .x c.leftReg c.leftReg (8 * c.bw)]

/-- After `crypt` and `x8 := leftReg >> lg`: if fewer bytes than a block are
left (`x8` zero), `Oⱼ`'s first ones XORed into them, none left; otherwise
`fb`'s step and on to the next segment. -/
def fbSegOp (m : FbMode) : Prog isa :=
  .ite (.zero .x .x8)
    (.seq (.block c.fbTailStart) (.loop (.block (xorByte c.dataReg c.leftReg)) (.nonzero .x c.leftReg)))
    (.block (c.fbOp m ++ c.fbNextBytes))

/-- One segment: its input block enciphered in the buffer, then `fbSegOp`. -/
def fbSeg (m : FbMode) : Prog isa :=
  .seq c.crypt (.seq (.block [.lsr .x .x8 c.leftReg c.fbLg]) (c.fbSegOp m))

/-- The whole function: `fb`'s, over segments. -/
def fbFinal (m : FbMode) (r : CtrRegs) (iv : Reg) : Prog isa :=
  .seq (.block (c.fbEntry r iv))
    (.seq c.prepare
      (.seq (.block (c.fbLoad iv))
        (.seq (.ite (.zero .x c.leftReg) (.block []) (.loop (c.fbSeg m) (.nonzero .x c.leftReg)))
          (.block (c.fbStore iv ++ c.restoreRegs)))))

end Core

end VG.Impl.Modes.AArch64
