module

public import VerifiedGarbage.Impl.Modes.X86_64.Fb

/-!
# OFB and CFB of a message's last piece on x86-64, for any block cipher

`fbFinal core mode regs`: `fb` (`Fb.lean`) over the `len` bytes at the
data, in segments of a block, `L = 8 bw` bytes, the last of which may be
shorter (SP 800-38A §6.4 for OFB, whose last block may be partial; for CFB
with segments of a whole block, the same extension of §6.3). The number in
`leftReg` is the bytes left, not the blocks. Each segment's input block is
enciphered in the buffer (`crypt`), giving `Oⱼ`; then, if a whole block is
left, `fb`'s step (`fbOp`) and on by `L` bytes; if fewer, `r`, the first `r`
bytes of `Oⱼ` are XORed into the data a byte at a time (`xorByte`) and none
are left. After a partial segment the buffer holds `Oⱼ`, the block to
continue from, which replaces the IV as after a whole one; the core is
called once per segment, so its code appears once.
-/

@[expose] public section

namespace VG.Impl.Modes.X86_64

open VG.X86_64 VG.Impl.Aes.X86_64
open VG.Impl.Modes (FbMode)

/-- The byte at `rax` XORed into the byte at `Rd`, through `r10` and `rcx`;
both on to the next byte, and one fewer left in `Rl`, ZF set after the
last. -/
def xorByte (Rd Rl : Reg) : List Instr :=
  [.movzx8 .r10 { base := .rax }, .movzx8 .rcx { base := Rd }, .alu .xor .rcx (.reg .r10),
    .store8 { base := Rd } .rcx, .alu .add .rax (.imm 1), .alu .add Rd (.imm 1), .alu .sub Rl (.imm 1)]

namespace Core

variable (c : Core)

/-- The buffer's first block's address, to `rax`. -/
def fbTailStart : List Instr := [.mov .rax (.reg sb), .alu .add .rax (.imm (BitVec.ofNat 32 (8 * c.buf)))]

/-- On to the next segment, a whole block; ZF is set when no byte is left. -/
def fbNextBytes : List Instr :=
  [.alu .add c.dataReg (.imm (BitVec.ofNat 32 (8 * c.bw))), .alu .sub c.leftReg (.imm (BitVec.ofNat 32 (8 * c.bw)))]

/-- After `crypt`: if fewer bytes than a block are left (CF, from `cmp`),
`Oⱼ`'s first ones XORed into them, none left; otherwise `fb`'s step and on
to the next segment. -/
def fbSegOp (m : FbMode) : Prog isa :=
  .ite .b (.seq (.block c.fbTailStart) (.loop (.block (xorByte c.dataReg c.leftReg)) .ne))
    (.block (c.fbOp m ++ c.fbNextBytes))

/-- One segment: its input block enciphered in the buffer, then `fbSegOp`. -/
def fbSeg (m : FbMode) : Prog isa :=
  .seq c.crypt (.seq (.block [.alu .cmp c.leftReg (.imm (BitVec.ofNat 32 (8 * c.bw)))]) (c.fbSegOp m))

/-- The whole function: `fb`'s, over segments. -/
def fbFinal (m : FbMode) (r : CtrRegs) : Prog isa :=
  .seq (.block (c.fbEntry r))
    (.seq c.prepare
      (.seq (.block (c.fbLoad ++ ([.alu .test c.leftReg (.reg c.leftReg)] : List Instr)))
        (.seq (.ite .e (.block []) (.loop (c.fbSeg m) .ne)) (.block (c.fbStore ++ c.restoreRegs)))))

end Core

end VG.Impl.Modes.X86_64
