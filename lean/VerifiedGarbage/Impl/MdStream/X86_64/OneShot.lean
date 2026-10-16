module

public import VerifiedGarbage.Impl.MdStream.X86_64
public import VerifiedGarbage.Impl.StackScratch.X86_64

/-!
# One-shot Merkle–Damgård digests: x86-64 implementation

`digest(data = rdi, len = rsi, out = rdx)` hashes a message in memory in one
call, as the AArch64 one does (`Impl/MdStream/AArch64/OneShot.lean`), in a
scratch buffer on its stack (`withStackScratch`; `body` is the code given its
address, in `rcx`, which it keeps in `r15`):

* `[0, N)`: the hash value, and `[N, N + B)`: the last block or two, laid out
  as a streaming state, so that each hash function's `Params.len` and
  `Params.out` (which address them through `rbx`) write the length field and
  the digest;
* `[scO, scO + so)`: the compression function's scratch space;
* at `slO`: our caller's `rbx`, `rbp` and `r12`–`r15`.

It runs the initial hash value's code `init` (at `rdi`), compresses every
whole block straight from `data` with one call, then builds the last block in
the buffer: it zeroes it 16 bytes at a time, copies the bytes left sixteen at
a time and then one at a time, appends the `0x80` byte, compresses it and
zeroes it again if the length field does not fit after them, stores the
length field (`P.len`) and compresses it. It writes the digest (`P.out`),
zeroes the hash value and the block, and restores the registers.

`data` is in `rbx` until the last block is built (then `rbx` is the hash
value's address, as `P.len` and `P.out` expect), `out` in `rbp`, `len` in
`r12`, the bytes left in `r13`, and the counters in `r10`, `r14` and `rax`;
every other address is `r15` plus a constant (the compression function gets
its scratch space in `rcx` and keeps it there). The frame is 8 more than a
multiple of 16 bytes, so the buffer is 16-byte aligned, as are the block's
16-byte stores, and so is `rsp` at the calls, as the ABI has it.
-/

@[expose] public section

namespace VG.Impl.MdStream.X86_64.OneShot

open VG.X86_64

variable (P : Params)

/-- Where the scratch space is in the frame: after the hash value and the
block, at a multiple of 16. -/
def scO : Nat := (P.N + P.B + 15) / 16 * 16

/-- Where our caller's registers are saved. -/
def slO : Nat := scO P + P.so

/-- The scratch buffer's size. -/
def scratchBytes : Nat := slO P + 48

/-- The frame's size: the buffer, 8 bytes for `withStackScratch`'s
stand-in for the return address, and up to 8 more, for `rsp` to be 16-byte
aligned at the calls. -/
def frameBytes : Nat := (scratchBytes P + 8 + 15) / 16 * 16 + 8

/-- The callee-saved registers, in their slots. -/
def saves : List Reg := [.rbx, .rbp, .r12, .r13, .r14, .r15]

/-- Save our caller's registers, keep `data`, `len` and `out`, and point `rdi`
at the hash value for `init`. -/
def setup : List Instr :=
  (List.range 6).map (fun k => .store (at_ .rcx (slO P + 8 * k)) (saves.getD k .rbx)) ++
    [.mov .r15 (.reg .rcx), .mov .rbx (.reg .rdi), .mov .rbp (.reg .rdx), .mov .r12 (.reg .rsi),
      .mov .rdi (.reg .r15)]

/-- Restore them. -/
def restore : List Instr :=
  (List.range 6).map fun k => .mov (saves.getD k .rbx) (.mem (at_ .r15 (slO P + 8 * k)))

/-- Call the compression function on the hash value, with `blocks` setting
`rsi` and `rdx` to the blocks and their number. -/
def compressWith (blocks : List Instr) (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block (.mov .rdi (.reg .r15) :: blocks ++
      [.mov .rcx (.reg .r15), .alu .add .rcx (.imm (BitVec.ofNat 32 (scO P)))]))
    (.seq (.call name code)
      (.block [.mov .r15 (.reg .rcx), .alu .sub .r15 (.imm (BitVec.ofNat 32 (scO P)))]))

/-- Compress the frame's block once. -/
def compressBuf : String → Prog isa → Prog isa :=
  compressWith P [.mov .rsi (.reg .r15), .alu .add .rsi (.imm (BitVec.ofNat 32 P.N)), .mov32 .rdx (.imm 1)]

/-- Every whole block of the message, straight from `data` (in `rbx`), which
then points past them. -/
def whole (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block [.mov .r13 (.reg .r12), .shift .shr .r13 (Nat.log2 P.B), .alu .test .r13 (.reg .r13)])
    (.ite .e (.block [])
      (.seq (compressWith P [.mov .rsi (.reg .rbx), .mov .rdx (.reg .r13)] name code)
        (.block [.mov .rax (.reg .r13), .shift .shl .rax (Nat.log2 P.B), .alu .add .rbx (.reg .rax)])))

/-- Zero the block, 16 bytes at a time, through `xmm0`. -/
def zeroBuf : List Instr :=
  .xop (.bin .pxor .xmm0 .xmm0) :: (List.range (P.B / 16)).map fun k => .movdquStore (at_ .r15 (P.N + 16 * k)) .xmm0

/-- Byte `r10` of the block. -/
def blkByte : MemOp := { base := .r15, index := some .r10, scale := 1, disp := P.N }

/-- Copy sixteen bytes from `rbx` to the block at `r10`, advancing both. -/
def copy16 : List Instr :=
  [.movdquLoad .xmm1 { base := .rbx }, .movdquStore (blkByte P) .xmm1, .alu .add .rbx (.imm 16),
    .alu .add .r10 (.imm 16), .alu .sub .r14 (.imm 1)]

/-- Copy a byte from `rbx` to the block at `r10`, advancing both. -/
def copy1 : List Instr :=
  [.movzx8 .r9 { base := .rbx }, .store8 (blkByte P) .r9, .alu .add .rbx (.imm 1), .alu .add .r10 (.imm 1),
    .alu .sub .rax (.imm 1)]

/-- Copy the `len mod B` bytes left (counted in `r13`) to the block, sixteen
at a time (`r14` of them), then one at a time (`rax`), and append the `0x80`
byte. -/
def copyTail : Prog isa :=
  .seq (.block [.mov .r13 (.reg .r12), .alu .and .r13 (.imm (BitVec.ofNat 32 (P.B - 1))), .mov32 .r10 (.imm 0),
      .mov .r14 (.reg .r13), .shift .shr .r14 4])
  (.seq (.ite .e (.block []) (.loop (.block (copy16 P)) .ne))
  (.seq (.block [.mov .rax (.reg .r13), .alu .and .rax (.imm 15)])
  (.seq (.ite .e (.block []) (.loop (.block (copy1 P)) .ne))
    (.block [.mov32 .r9 (.imm 0x80), .store8 (blkByte P) .r9]))))

/-- The last block or two: the bytes left, `0x80`, zeros and the length field.
It takes two blocks iff `len mod B ≥ B - L`. -/
def tail (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block (zeroBuf P))
  (.seq (copyTail P)
  (.seq (.block [.alu .cmp .r13 (.imm (BitVec.ofNat 32 (P.B - P.L)))])
  (.seq (.ite .ae (.seq (compressBuf P name code) (.block (zeroBuf P))) (.block []))
  (.seq (.block (.mov .rbx (.reg .r15) :: P.len))
    (compressBuf P name code)))))

/-- Zero the hash value and the block, 16 bytes at a time, through `xmm0`. -/
def wipe : List Instr :=
  .xop (.bin .pxor .xmm0 .xmm0) ::
    (List.range ((P.N + P.B + 15) / 16)).map fun k => .movdquStore (at_ .r15 (16 * k)) .xmm0

/-- Write the digest to `out`, zero the frame's hash value and block and
restore the registers. -/
def finish : List Instr := P.out ++ wipe P ++ restore P

/-- The body, inside the frame. -/
def body (init : Prog isa) (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block (setup P)) (.seq init (.seq (whole P name code) (.seq (tail P name code)
    (.block (finish P)))))

/-- The one-shot digest: `init` stores the initial hash value at `rdi` (using
only `rax`), `P` is the hash function's sizes, length field and digest; its
scratch buffer (`body`'s fourth argument) is on the stack. -/
def digest (init : Prog isa) (name : String) (code : Prog isa) : Prog isa :=
  StackScratch.X86_64.withStackScratch (frameBytes P) .rcx (body P init name code)

end VG.Impl.MdStream.X86_64.OneShot
