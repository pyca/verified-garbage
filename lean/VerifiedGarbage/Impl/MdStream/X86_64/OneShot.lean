module

public import VerifiedGarbage.Impl.MdStream.X86_64
public import VerifiedGarbage.Impl.StackScratch.X86_64

/-!
# One-shot Merkle–Damgård digests: x86-64 implementation

`digest(data = rdi, len = rsi, out = rdx)` hashes a message in memory in one
call, as the AArch64 one does (`Impl/MdStream/AArch64/OneShot.lean`), in a
scratch buffer on its stack (`withStackScratch`; `body` is the code given its
address, in `rcx`):

* `[0, N)`: the hash value, and `[N, N + B)`: the last block or two, laid out
  as a streaming state, so that each hash function's `Params.len` and
  `Params.out` write the length field and the digest;
* `[scO, scO + so + 48)`: the scratch space of the streaming code: the
  compression function's, and our caller's `rbx`, `rbp` and `r12`–`r15`
  (`save`, `restore`).

It keeps the streaming code's registers (`rbx` = the state, `r15` = the
scratch space, `rbp` = `out`, `r12` = `len`), so that it calls the
compression function as that code does (`compressN`, `compressAt`), and
`data` in `r13`. It runs the initial hash value's code `init` (at `rdi`),
compresses every whole block straight from `data` with one call, then builds
the last block in the buffer: it zeroes it 16 bytes at a time, copies the
bytes left sixteen at a time and then one at a time, appends the `0x80`
byte, compresses it and zeroes it again if the length field does not fit
after them, stores the length field (`P.len`) and compresses it. It writes
the digest (`P.out`), zeroes the hash value and the block, and restores the
registers.

The frame is 8 more than a multiple of 16 bytes, so the buffer is 16-byte
aligned, as are the block's 16-byte stores, and so is `rsp` at the calls, as
the ABI has it.
-/

@[expose] public section

namespace VG.Impl.MdStream.X86_64.OneShot

open VG.X86_64

variable (P : Params)

/-- Where the scratch space is in the buffer: after the hash value and the
block, at a multiple of 16. -/
def scO : Nat := (P.N + P.B + 15) / 16 * 16

/-- The scratch buffer's size. -/
def scratchBytes : Nat := scO P + P.so + 48

/-- The frame's size: the buffer, 8 bytes for `withStackScratch`'s
stand-in for the return address, and up to 8 more, for `rsp` to be 16-byte
aligned at the calls. -/
def frameBytes : Nat := (scratchBytes P + 8 + 15) / 16 * 16 + 8

/-- Save our caller's registers in the scratch space, set up ours, and point
`rdi` at the hash value for `init`. -/
def setup : List Instr :=
  .alu .add .rcx (.imm (BitVec.ofNat 32 (scO P))) :: save P .rcx ++
    [.mov .r15 (.reg .rcx), .mov .rbx (.reg .rcx), .alu .sub .rbx (.imm (BitVec.ofNat 32 (scO P))),
      .mov .r13 (.reg .rdi), .mov .r12 (.reg .rsi), .mov .rbp (.reg .rdx), .mov .rdi (.reg .rbx)]

/-- `rsi` = the block. -/
def blkArg : List Instr := [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 P.N))]

/-- The number of whole blocks of the message, in `r14`, and whether it is 0. -/
def wholeHead : List Instr :=
  [.mov .r14 (.reg .r12), .shift .shr .r14 (Nat.log2 P.B), .alu .test .r14 (.reg .r14)]

/-- `data` (in `r13`) past the whole blocks. -/
def wholeEnd : List Instr :=
  [.mov .rax (.reg .r14), .shift .shl .rax (Nat.log2 P.B), .alu .add .r13 (.reg .rax)]

/-- Every whole block of the message (`r14` of them), straight from `data`
(in `r13`), which then points past them. -/
def whole (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block (wholeHead P))
    (.ite .e (.block [])
      (.seq (.block [.mov .rsi (.reg .r13)]) (.seq (compressN name code) (.block (wholeEnd P)))))

/-- Zero the block, 16 bytes at a time, through `xmm0`. -/
def zeroBuf : List Instr :=
  .xop (.bin .pxor .xmm0 .xmm0) :: (List.range (P.B / 16)).map fun k => .movdquStore (at_ .rbx (P.N + 16 * k)) .xmm0

/-- Byte `r11` of the block. -/
def blkByte : MemOp := { base := .rbx, index := some .r11, scale := 1, disp := P.N }

/-- Copy sixteen bytes from `r13` to the block at `r11`, advancing both. -/
def copy16 : List Instr :=
  [.movdquLoad .xmm1 { base := .r13 }, .movdquStore (blkByte P) .xmm1, .alu .add .r13 (.imm 16),
    .alu .add .r11 (.imm 16), .alu .sub .r9 (.imm 1)]

/-- Copy a byte from `r13` to the block at `r11`, advancing both. -/
def copy1 : List Instr :=
  [.movzx8 .r8 { base := .r13 }, .store8 (blkByte P) .r8, .alu .add .r13 (.imm 1), .alu .add .r11 (.imm 1),
    .alu .sub .rax (.imm 1)]

/-- Store `xmm1` as the 16 bytes of the block at `r11`. -/
def storeChunk : Instr := .movdquStore (blkByte P) .xmm1

/-- When the bytes left end at a multiple of 16: the 16 bytes at `r11` are
`0x80` and zeros, one 16-byte store. -/
def mark16 : List Instr := [.mov32 .r8 (.imm 0x80), .xop (.movq .xmm1 .r8), storeChunk P]

/-- The last `r = rax` bytes left (at `r13`), `0 < r < 8`, then `0x80` and
zeros, as the 16 bytes at `r11`: the 8 bytes of the message that end with
them, shifted right by the `8 - r` before them, and `0x80` shifted to byte
`r`, in `r8`, then zeros. (A message of at least 8 bytes has those 8.) -/
def partLo : List Instr :=
  [.mov .r8 (.mem { base := .r13, index := some .rax, disp := -8 }), .mov32 .rcx (.imm 8),
    .alu .sub .rcx (.reg .rax), .shift .shl .rcx 3, .shiftCl .shr .r8,
    .mov .rcx (.reg .rax), .shift .shl .rcx 3, .mov32 .r9 (.imm 0x80), .shiftCl .shl .r9,
    .alu .or .r8 (.reg .r9), .xop (.movq .xmm1 .r8), storeChunk P]

/-- As `partLo`, for `8 ≤ r < 16`: the first 8 bytes left in `r8`; in `r9`,
the 8 bytes of the message that end with them, shifted right by the
`16 - r` before the last `r - 8` (by `8 (15 - r)` then 8, so that `r = 8`
leaves none), with `0x80` shifted to byte `r - 8`. -/
def partHi : List Instr :=
  [.mov .r8 (.mem { base := .r13 }), .mov .r9 (.mem { base := .r13, index := some .rax, disp := -8 }),
    .mov32 .rcx (.imm 15), .alu .sub .rcx (.reg .rax), .shift .shl .rcx 3, .shiftCl .shr .r9,
    .shift .shr .r9 8, .mov .rcx (.reg .rax), .alu .sub .rcx (.imm 8), .shift .shl .rcx 3,
    .mov32 .rdx (.imm 0x80), .shiftCl .shl .rdx, .alu .or .r9 (.reg .rdx), .xop (.movq .xmm1 .r8),
    .xop (.movq .xmm2 .r9), .xop (.bin .punpcklqdq .xmm1 .xmm2), storeChunk P]

/-- Fewer than 8 bytes left in a message shorter than 8: one at a time
(`rax` of them), then the `0x80` byte. -/
def bytesTail : Prog isa :=
  .seq (.block [.alu .test .rax (.reg .rax)])
  (.seq (.ite .e (.block []) (.loop (.block (copy1 P)) .ne))
    (.block [.mov32 .r8 (.imm 0x80), .store8 (blkByte P) .r8]))

/-- Copy the `len mod B` bytes left (counted in `r10`) to the block, sixteen
at a time (`r9` of them), and the 16 bytes holding the last of them and the
`0x80` byte with one 16-byte store (`mark16`, `partLo`, `partHi`): the
compression function reads the block 16 bytes at a time, and a 16-byte load
of bytes that narrower stores wrote cannot take them from those stores (it
waits until they reach the cache). Only a message shorter than 8 bytes is
copied a byte at a time (`bytesTail`). -/
def copyTail : Prog isa :=
  .seq (.block [.mov .r10 (.reg .r12), .alu .and .r10 (.imm (BitVec.ofNat 32 (P.B - 1))), .mov32 .r11 (.imm 0),
      .mov .r9 (.reg .r10), .shift .shr .r9 4])
  (.seq (.ite .e (.block []) (.loop (.block (copy16 P)) .ne))
  (.seq (.block [.mov .rax (.reg .r10), .alu .and .rax (.imm 15)])
    (.ite .e (.block (mark16 P))
      (.seq (.block [.alu .cmp .r12 (.imm 8)])
        (.ite .b (bytesTail P)
          (.seq (.block [.alu .cmp .rax (.imm 8)])
            (.ite .b (.block (partLo P)) (.block (partHi P)))))))))

/-- The length field, into the block's last 16 bytes, whose last `L` are
zeros: `P.lenV` builds them in `xmm7`, or'd into those 16 bytes, loaded and
stored again 16 at a time, so that both that load and the compression
function's take them from a single 16-byte store. -/
def lenVec : List Instr :=
  P.lenV ++ [.movdquLoad .xmm0 (at_ .rbx (P.N + P.B - 16)), .xop (.bin .por .xmm0 .xmm7),
    .movdquStore (at_ .rbx (P.N + P.B - 16)) .xmm0]

/-- Whether the length field fits after the bytes left and `0x80`. -/
def cmpLen : List Instr := [.alu .cmp .r10 (.imm (BitVec.ofNat 32 (P.B - P.L)))]

/-- The last block or two: the bytes left, `0x80`, zeros and the length field.
It takes two blocks iff `len mod B ≥ B - L`. -/
def tail (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block (zeroBuf P))
  (.seq (copyTail P)
  (.seq (.block (cmpLen P))
  (.seq (.ite .ae (.seq (.block (blkArg P)) (.seq (compressAt name code) (.block (zeroBuf P)))) (.block []))
  (.seq (.block (lenVec P ++ blkArg P))
    (compressAt name code)))))

/-- Zero the hash value and the block, 16 bytes at a time, through `xmm0`. -/
def wipe : List Instr :=
  .xop (.bin .pxor .xmm0 .xmm0) ::
    (List.range ((P.N + P.B + 15) / 16)).map fun k => .movdquStore (at_ .rbx (16 * k)) .xmm0

/-- Write the digest to `out`, zero the hash value and the block and
restore the registers. -/
def finish : List Instr := P.out ++ wipe P ++ restore P

/-- The body, given the scratch buffer. -/
def body (init : Prog isa) (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block (setup P)) (.seq init (.seq (whole P name code) (.seq (tail P name code)
    (.block (finish P)))))

/-- The one-shot digest: `init` stores the initial hash value at `rdi` (using
only `rax`), `P` is the hash function's sizes, length field and digest; its
scratch buffer (`body`'s fourth argument) is on the stack. -/
def digest (init : Prog isa) (name : String) (code : Prog isa) : Prog isa :=
  StackScratch.X86_64.withStackScratch (frameBytes P) .rcx (body P init name code)

end VG.Impl.MdStream.X86_64.OneShot
