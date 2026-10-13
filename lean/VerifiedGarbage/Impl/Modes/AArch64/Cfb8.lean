module

public import VerifiedGarbage.Impl.Modes.AArch64.Fb

/-!
# CFB8 on AArch64, for any block cipher with blocks of 8 or 16 bytes

`cfb8 core enc regs iv`: CFB with 8-bit segments (SP 800-38A §6.3),
encryption (`enc`) or decryption, over a block cipher's core (`Core`, as
for CTR), whose `crypt` applies the forward cipher `CIPH_K` to the `G`
blocks of its buffer. As on x86-64 (`Impl/Modes/X86_64/Cfb8.lean`): each
byte needs the input block shifted by the byte before it, so each call of
`crypt` enciphers one block, in the buffer's first, and the other `G - 1`
are wasted.

The input block is kept in place at the IV, whose address `iv` holds (as for
OFB and CFB, `Impl/Modes/AArch64/Fb.lean`): for each byte, it is copied to
the buffer and enciphered there, the output's first byte is XORed into the
data's byte, and the input block is shifted left by a byte in place, with
the ciphertext byte (the output when encrypting, the input when decrypting)
shifted in. After the last byte it is the input block to continue from.

Only the pointers and the length (and what is computed from them) are
public; no address or branch depends on the key, the IV or the data.
-/

@[expose] public section

namespace VG.Impl.Modes.AArch64

open VG.AArch64 VG.Impl.Aes.AArch64

namespace Core

variable (c : Core)

/-- The output's first byte XORed into the byte at `dataReg`; the
ciphertext byte is left in `x6`. -/
def cfb8Xor (enc : Bool) : List Instr :=
  [.ldrb .x6 c.dataReg 0, .ldrb .x7 sb (8 * c.buf),
    if enc then eorR .x6 .x6 .x7 else eorR .x7 .x7 .x6,
    .strb (if enc then .x6 else .x7) c.dataReg 0]

/-- Byte `i + 1` of the input block at `iv` to byte `i`, through `x7`. -/
def shiftByte (iv : Reg) (i : Nat) : List Instr := [.ldrb .x7 iv (i + 1), .strb .x7 iv i]

/-- The input block, at the IV, shifted left by a byte, with the low byte of
`x6` shifted in. -/
def cfb8Shift (iv : Reg) : List Instr :=
  (List.range (8 * c.bw - 1)).flatMap (shiftByte iv) ++ ([.strb .x6 iv (8 * c.bw - 1)] : List Instr)

/-- On to the next byte. -/
def cfb8Next : List Instr := [.addImm .x c.dataReg c.dataReg 1, .subImm .x c.leftReg c.leftReg 1]

/-- One byte: the input block to the buffer and enciphered, its first byte
XORed into the data, and the input block shifted. -/
def cfb8Block (enc : Bool) (iv : Reg) : Prog isa :=
  .seq (.block (c.fbLoad iv)) (.seq c.crypt (.block (c.cfb8Xor enc ++ c.cfb8Shift iv ++ c.cfb8Next)))

/-- The whole function: the entry, the key, then the bytes. -/
def cfb8 (enc : Bool) (r : CtrRegs) (iv : Reg) : Prog isa :=
  .seq (.block (c.fbEntry r iv))
    (.seq c.prepare
      (.seq (.ite (.zero .x c.leftReg) (.block []) (.loop (c.cfb8Block enc iv) (.nonzero .x c.leftReg)))
        (.block c.restoreRegs)))

end Core

end VG.Impl.Modes.AArch64
