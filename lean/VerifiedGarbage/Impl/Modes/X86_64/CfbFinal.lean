module

public import VerifiedGarbage.TCB.X86_64.Isa

/-!
# CFB of a message's last piece on x86-64, for any block cipher

`cfbFinal a whole enc`: a final function (`Spec/Cfb/Final.lean`) built from
two of a cipher's verified whole-block CFB functions, inlined: `whole`, the
direction's (encryption or decryption), and `enc`, encryption. Its
arguments are the whole-block functions', in the registers `a.regs`, but for
the data's length, which is `len` bytes rather than `n` blocks of
`2 ^ a.lg` bytes.

* The arguments are saved in callee-saved registers (`saved`), which the
  inlined functions keep, in a frame (`pushRegs`) that holds the caller's
  values of those registers and a block of working space at `rsp + 8`: the eight bytes at `rsp` stand for the return address of the
  inlined functions, which their contracts keep out of their buffers, and
  `rsp` is 8 modulo 16 for them, as on a call.
* `whole` runs on the `n = len >> lg` whole blocks; it leaves the last
  ciphertext block `c` in the IV.
* The register that saved the data's address now holds the address of the
  rest, `data + (len & −2^lg)`, and the one that saved the length the
  number of bytes left, `r = len & (2^lg − 1)`.
* If `r ≠ 0`: the block at `rsp + 8` is zeroed and `enc` runs on it, one block,
  leaving `CIPH_K(c)` both there and in the IV; its first `r` bytes are
  XORed into the rest of the data, a byte at a time, and the block is zeroed
  again. The XOR loop walks the block from `rsp + 8` in `rax` and the rest in
  the register that holds its address, counting down the bytes left.

Only the pointers and `len` (and what is computed from them) are public: the
only branches are on `r` and the inlined functions' own, on `n`.
-/

@[expose] public section

namespace VG.Impl.Modes.X86_64

open VG.X86_64

/-- Where a cipher's whole-block CFB functions take their arguments: the
argument registers, in order, the indices among them of the data and of the
number of blocks, and the block size, `2 ^ lg` bytes. -/
structure FinalArgs where
  regs : List Reg
  dataIx : Nat
  lenIx : Nat
  lg : Nat

namespace FinalArgs

variable (a : FinalArgs)

/-- The callee-saved registers that save the arguments, in order. -/
def savedRegs : List Reg := [.rbx, .rbp, .r12, .r13, .r14, .r15]

/-- The register saving argument `i`. -/
def saved (i : Nat) : Reg := savedRegs.getD i .rbx

/-- The register of argument `i`. -/
def arg (i : Nat) : Reg := a.regs.getD i .rax

/-- The block size in bytes. -/
def blk : Nat := 2 ^ a.lg

/-- The frame's push: the caller's six callee-saved registers, then four
words (of `rax`) more, 80 bytes: from `rsp`, eight bytes, the working block
at `rsp + 8`, eight bytes, and the caller's registers, `savedRegs[i]` at
`rsp + 72 − 8i`. -/
def pushRegs : List Reg := savedRegs ++ [.rax, .rax, .rax, .rax]

/-- Where the caller's value of `savedRegs[i]` is, from `rsp`. -/
def savedOff (i : Nat) : Nat := 72 - 8 * i

/-- An operand at `rsp + off`. -/
def blockOp (off : Nat) : MemOp := { base := .rsp, disp := (off : Int) }

/-- The arguments to the callee-saved registers, which the frame's push
saved. -/
def entry : List Instr := (List.range a.regs.length).map fun i => .mov (saved i) (.reg (a.arg i))

/-- The number of whole blocks, in the length's register. -/
def toBlocks : List Instr := [.shift .shr (a.arg a.lenIx) a.lg]

/-- The arguments back from the registers that save them. -/
def reload : List Instr := (List.range a.regs.length).map fun i => .mov (a.arg i) (.reg (saved i))

/-- The rest's address and length, in the registers that saved the data's
address and the length: `data + (len & −2^lg)` and `len & (2^lg − 1)`. -/
def rest : List Instr :=
  [.mov .rax (.reg (saved a.lenIx)),
    .alu .and .rax (.imm (BitVec.ofInt 32 (-(a.blk : Int)))),
    .alu .add (saved a.dataIx) (.reg .rax),
    .alu .and (saved a.lenIx) (.imm (BitVec.ofNat 32 (a.blk - 1))),
    .alu .test (saved a.lenIx) (.reg (saved a.lenIx))]

/-- Zeroes the working block, through `rax`. -/
def zeroBlock : List Instr :=
  .mov32 .rax (.imm 0) :: (List.range (a.blk / 8)).map fun k => .store (blockOp (8 + 8 * k)) .rax

/-- The arguments for one block at `rsp + 8`: those of the call, but the
data's address, `rsp + 8`, and the number of blocks, 1. -/
def oneBlock : List Instr :=
  a.reload ++ [.mov (a.arg a.dataIx) (.reg .rsp), .alu .add (a.arg a.dataIx) (.imm 8), .mov (a.arg a.lenIx) (.imm 1)]

/-- The byte at `rax` (in the working block) XORed into the byte at the rest's
address; both on to the next byte, and one byte fewer left, ZF set after
the last. -/
def xorByte : List Instr :=
  [.movzx8 .r10 { base := .rax },
    .movzx8 .r11 { base := saved a.dataIx },
    .alu .xor .r11 (.reg .r10),
    .store8 { base := saved a.dataIx } .r11,
    .alu .add .rax (.imm 1),
    .alu .add (saved a.dataIx) (.imm 1),
    .alu .sub (saved a.lenIx) (.imm 1)]

/-- The caller's callee-saved registers back from the frame. -/
def exit : List Instr := (List.range 6).map fun i => .mov (saved i) (.mem (blockOp (savedOff i)))

/-- The partial last segment: `CIPH_K(c)` in the working block (`enc` on a
zero block), its first `r` bytes XORed into the rest, and the block zeroed. -/
def tail (enc : Prog isa) : Prog isa :=
  .seq (.block (a.zeroBlock ++ a.oneBlock)) (.seq enc
    (.seq (.block [.mov .rax (.reg .rsp), .alu .add .rax (.imm 8)]) (.seq (.loop (.block a.xorByte) .ne) (.block a.zeroBlock))))

end FinalArgs

/-- The final function from the inlined whole-block functions `whole` and
`enc`, with their arguments as `a` says (see above). -/
def cfbFinal (a : FinalArgs) (whole enc : Prog isa) : Prog isa :=
  .frame (.push FinalArgs.pushRegs)
    (.seq (.block (a.entry ++ a.toBlocks)) (.seq whole
      (.seq (.block a.rest) (.seq (.ite .e (.block []) (a.tail enc)) (.block FinalArgs.exit)))))
    (.pop .rax 10)

end VG.Impl.Modes.X86_64
