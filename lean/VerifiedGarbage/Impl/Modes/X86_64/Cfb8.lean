import VerifiedGarbage.Impl.Modes.X86_64.Fb

/-!
# CFB8 on x86-64, for any block cipher with blocks of 8 or 16 bytes

`cfb8 core enc regs`: CFB with 8-bit segments (SP 800-38A §6.3), encryption
(`enc`) or decryption, over a block cipher's core (`Core`, as for CTR),
whose `crypt` applies the forward cipher `CIPH_K` to the `G` blocks of its
buffer. Each byte needs the input block shifted by the byte before it, so
each call of `crypt` enciphers one block, in the buffer's first, and the
other `G - 1` are wasted.

The input block is kept in place in the IV's buffer, whose address the
mode's `hiSlot` holds (as for OFB and CFB, `Impl/Modes/X86_64/Fb.lean`):
for each byte, it is copied to the buffer and enciphered there, the
output's first byte is XORed into the data's byte, and the input block is
shifted left by a byte in place, with the ciphertext byte (the output when
encrypting, the input when decrypting) shifted in. After the last byte it
is the input block to continue from.

Only the pointers and the length (and what is computed from them) are
public; no address or branch depends on the key, the IV or the data.
-/

namespace VG.Impl.Modes.X86_64

open VG.X86_64 VG.Impl.Aes.X86_64

namespace Core

variable (c : Core)

/-- The output's first byte XORed into the byte at `dataReg`; the
ciphertext byte is left in `rax`. -/
def cfb8Xor (enc : Bool) : List Instr :=
  [.movzx8 .rax (at_ c.dataReg 0), .movzx8 .rbp (at_ sb (8 * c.buf)),
    if enc then .alu .xor .rax (.reg .rbp) else .alu .xor .rbp (.reg .rax),
    .store8 (at_ c.dataReg 0) (if enc then .rax else .rbp)]

/-- Byte `i + 1` of the input block at `rcx` to byte `i`, through `rbp`. -/
def shiftByte (i : Nat) : List Instr := [.movzx8 .rbp (at_ .rcx (i + 1)), .store8 (at_ .rcx i) .rbp]

/-- The input block, at the IV, shifted left by a byte, with `al` shifted
in. -/
def cfb8Shift : List Instr :=
  ([movS .rcx c.hiSlot] : List Instr) ++ (List.range (8 * c.bw - 1)).flatMap shiftByte ++
    ([.store8 (at_ .rcx (8 * c.bw - 1)) .rax] : List Instr)

/-- On to the next byte; ZF is set when none is left. -/
def cfb8Next : List Instr := [.alu .add c.dataReg (.imm 1), .alu .sub c.leftReg (.imm 1)]

/-- One byte: the input block to the buffer and enciphered, its first byte
XORed into the data, and the input block shifted. -/
def cfb8Block (enc : Bool) : Prog isa :=
  .seq (.block c.fbLoad) (.seq c.crypt (.block (c.cfb8Xor enc ++ c.cfb8Shift ++ c.cfb8Next)))

/-- The whole function: the entry, the key, then the bytes. -/
def cfb8 (enc : Bool) (r : CtrRegs) : Prog isa :=
  .seq (.block (c.fbEntry r))
    (.seq c.prepare
      (.seq (.block [.alu .test c.leftReg (.reg c.leftReg)])
        (.seq (.ite .e (.block []) (.loop (c.cfb8Block enc) .ne)) (.block c.restoreRegs))))

end Core

end VG.Impl.Modes.X86_64
