module

public import VerifiedGarbage.Impl.Sha512.RISCV64

/-!
# Streaming SHA-512: RISC-V implementation

The streaming state (192 bytes at `state`) is the hash value followed by a
128-byte buffer (see `VG.Spec.Sha512.Repr`). The structure of the PPC64LE
implementation (`Impl/Sha512/PPC64LE/Stream.lean`) and of SHA-256's on RISC-V
(`Impl/Sha256/RISCV64/Stream.lean`):

* `initWith iv (state = a0)` stores the initial hash value `iv`.
* `update(state = a0, count = a1, data = a2, len = a3)` processes one block
  per iteration: straight from `data` while the buffer is empty and a whole
  block remains, otherwise by copying bytes into the buffer, compressing it
  once it is full.
* `finalize(state = a0, count = a1, out = a2)` pads the buffered bytes (one or
  two blocks), compresses them and writes the final hash value; SHA-384's,
  SHA-512/256's and SHA-512/224's `finalize` write its first 48, 32 and 28
  bytes.

`update` and `finalize` run in a frame of `frameBytes` bytes on the stack
(`alloc`), whose first 144 bytes are the scratch space of the compression
function (`vg_sha512_compress`, which they call), and in which they save the
return address, which each call replaces, and our caller's values of the
callee-saved registers we use, `s1`–`s6`, which the compression function
preserves: our own variables live there (`s1` = `state`, `s2` = the frame).
The stack pointer is 16-byte aligned, so the saves and restores are aligned
doubleword accesses.

Every argument buffer (`state`, `data`, `out`) is accessed a byte at a time,
since its alignment is not stated: byte `r` of the buffer is addressed as
`64(t3)` with `t3 = state + r` computed just before the access, and `data`
is consumed through a pointer that advances. Every comparison is a shift
(`len ≥ 128` iff `len >> 7 ≠ 0`) or a subtraction tested against zero. Every
address and branch depends only on the pointers, `count` and `len`.
-/

@[expose] public section

namespace VG.Impl.Sha512.RISCV64.Stream

open VG.RISCV64
open VG.Impl.Words.RISCV64
open VG.Impl.Words64.RISCV64 (loadLE64 storeLE64)
open VG.Impl.Sha512.RISCV64 (compress)

/-- `mv d, n` (`addi d, n, 0`). -/
def mov (d n : Reg) : Instr := .addi d n 0

/-- `init` storing the initial hash value `iv`. -/
def initWith (iv : Spec.Sha512.HashValue) : Prog isa :=
  .block ((List.range 8).flatMap fun k => li64 .t0 .t1 iv[k]! ++ storeLE64 .t0 .t1 .t2 .a0 (8 * k))

/-- The bytes of the frame: the compression function's scratch space (144
bytes), then the saved registers. -/
def frameBytes : Nat := 288

/-- The registers we save, and where in the frame. -/
def saved : List (Reg × Nat) :=
  [(.ra, 224), (.s1, 232), (.s2, 240), (.s3, 248), (.s4, 256), (.s5, 264), (.s6, 272)]

/-- Save them, with the frame's address in `t0`. -/
def save : List Instr := .addSp .t0 0 :: saved.map fun (r, d) => .store .d r .t0 d

/-- Restore them from the frame at `s2` (`s2`, the base, last). -/
def restore : List Instr :=
  (saved.filter (·.1 != .s2)).map (fun (r, d) => .load .d r .s2 d) ++ [.load .d .s2 .s2 240]

/-- Compress the block at `a1` into the hash value at `s1`, with scratch
space `s2`. -/
def compressAt : Prog isa :=
  .seq (.block [mov .a0 .s1, .li .a2 1, mov .a3 .s2]) (.call "vg_sha512_compress" compress)

/-! ## `update`

Registers: `s3` = `data`, `s4` = bytes of `data` left, `s5` = bytes in the
buffer (`r`), `t0` = whether this iteration compresses a block (at `a1`).
The loop runs while `s4 ≠ 0`, so each iteration starts with `s4 ≥ 1` and
`s5 < 128`. -/

/-- A whole block straight from `data`. -/
def direct : List Instr :=
  [mov .a1 .s3, .addi .s3 .s3 128, .addi .s4 .s4 (-128), .li .t0 1]

/-- The byte copy loop's body. -/
def copyBody : List Instr :=
  [.load .b .t1 .s3 0, .add .t3 .s1 .s5, .store .b .t1 .t3 64, .addi .s3 .s3 1,
    .addi .s5 .s5 1, .addi .t2 .t2 (-1)]

/-- Copy `n = min(128 - r, len) ≥ 1` bytes of `data` into the buffer; if that
fills it, compress it. -/
def fill : Prog isa :=
  -- t2 := 128 - r; if len < 128 and len + r < 128 (i.e. len < 128 - r), t2 := len.
  .seq (.block [.li .t2 128, .sub .t2 .t2 .s5, .shift .srl .d .t1 .s4 7])
  (.seq (.ite (.zero .t1)
      (.seq (.block [.add .t1 .s4 .s5, .shift .srl .d .t1 .t1 7])
        (.ite (.zero .t1) (.block [mov .t2 .s4]) (.block [])))
      (.block []))
  (.seq (.block [.sub .s4 .s4 .t2])
  (.seq (.loop (.block copyBody) (.nonzero .t2))
  -- Full: compress the buffer.
  (.seq (.block [.addi .t1 .s5 (-128)])
    (.ite (.zero .t1) (.block [.addi .a1 .s1 64, .li .s5 0, .li .t0 1])
      (.block []))))))

def updateBody : Prog isa :=
  .seq (.block [.li .t0 0])
  (.seq (.ite (.zero .s5)
      (.seq (.block [.shift .srl .d .t1 .s4 7]) (.ite (.zero .t1) fill (.block direct)))
      fill)
    (.ite (.zero .t0) (.block []) compressAt))

/-- `update`, in its frame. -/
def updateMain : Prog isa :=
  .seq (.block (save ++ [mov .s1 .a0, mov .s2 .t0, mov .s3 .a2, mov .s4 .a3,
      .logicImm .and .s5 .a1 127]))
  (.seq (.ite (.zero .s4) (.block []) (.loop updateBody (.nonzero .s4)))
    (.block restore))

def update : Prog isa := .frame (.alloc frameBytes) updateMain (.free frameBytes)

/-! ## `finalize`

Registers: `s3` = `out`, `s4` = `count`, `s5` = bytes in the buffer (`r`),
`s6` = 1 while the block being padded is not the last one (then 0). -/

/-- The zeroing loop's body. -/
def zeroBody : List Instr :=
  [.add .t3 .s1 .s5, .store .b .t1 .t3 64, .addi .s5 .s5 1, .addi .t2 .t2 (-1)]

/-- The message length in bits as a 128-bit big-endian integer, at the end of
the buffer: `count >> 61`, then `count << 3` (modulo 2⁶⁴). -/
def lenStore : List Instr :=
  .shift .srl .d .t1 .s4 61 :: storeBE 8 .t1 .t3 .s1 176 ++
    .shift .sll .d .t1 .s4 3 :: storeBE 8 .t1 .t3 .s1 184

def finalizeBody : Prog isa :=
  -- Zero the buffer from `r` to 128, or to 112 in the last block.
  .seq (.block [.li .t2 128])
  (.seq (.ite (.zero .s6) (.block [.li .t2 112]) (.block []))
  (.seq (.block [.li .t1 0, .sub .t2 .t2 .s5])
  (.seq (.ite (.zero .t2) (.block []) (.loop (.block zeroBody) (.nonzero .t2)))
  -- In the last block, the message length.
  (.seq (.ite (.zero .s6) (.block lenStore) (.block []))
  (.seq (.block [.addi .a1 .s1 64])
  (.seq compressAt
    (.block [.li .s5 0, .addi .s6 .s6 (-1)])))))))

/-- Word `k` of the final hash value to `out`, big-endian. -/
def outW (k : Nat) : List Instr := loadLE64 .t1 .t2 .t4 .s1 (8 * k) ++ storeBE 8 .t1 .t2 .s3 (8 * k)

/-- The high half of word `k` (at offset `8 k + 4`, little-endian) to `out`,
big-endian: the last 4 bytes of SHA-512/224's digest, for `k = 3`. -/
def outHi (k : Nat) : List Instr := loadLE32 .t1 .t2 .s1 (8 * k + 4) ++ storeBE 4 .t1 .t2 .s3 (8 * k)

/-- `finalize` writing the digest with `o`, in its frame. -/
def finalizeMainWith (o : List Instr) : Prog isa :=
  .seq (.block (save ++ [mov .s1 .a0, mov .s2 .t0, mov .s3 .a2, mov .s4 .a1,
      .logicImm .and .s5 .s4 127,
      -- The `0x80` byte.
      .li .t1 0x80, .add .t3 .s1 .s5, .store .b .t1 .t3 64, .addi .s5 .s5 1,
      -- Two blocks iff that leaves fewer than 16 bytes for the length (r ≥ 113).
      .addi .s6 .s5 15, .shift .srl .d .s6 .s6 7]))
  (.seq (.loop finalizeBody (.zero .s6))
    (.block (o ++ restore)))

/-- `finalize` writing the digest with `o`. -/
def finalizeWith (o : List Instr) : Prog isa :=
  .frame (.alloc frameBytes) (finalizeMainWith o) (.free frameBytes)

/-- SHA-512's: all of the final hash value, 8 words. -/
def finalize : Prog isa := finalizeWith ((List.range 8).flatMap outW)

/-! ## The truncated digests

SHA-384's and SHA-512/256's `finalize` write the first 6 and 4 words of the
final hash value, SHA-512/224's the first 3 and the high half of the fourth
(28 bytes). -/

def finalize384 : Prog isa := finalizeWith ((List.range 6).flatMap outW)
def finalize512_256 : Prog isa := finalizeWith ((List.range 4).flatMap outW)
def finalize512_224 : Prog isa := finalizeWith ((List.range 3).flatMap outW ++ outHi 3)

end VG.Impl.Sha512.RISCV64.Stream
