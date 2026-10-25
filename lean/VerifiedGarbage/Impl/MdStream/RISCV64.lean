module

public import VerifiedGarbage.Impl.Words.RISCV64

/-!
# Streaming Merkle–Damgård hash functions: RISC-V implementation

The streaming `update` and `finalize` of the hash functions with 64-byte
blocks and a 64-bit length field (MD5, SHA-1, SM3), which differ only in
the size of their hash value, in how they store the length field and output
the digest, and in the compression function they call (`Params`). Each hash
function's `Impl/<Alg>/RISCV64/Stream.lean` instantiates them. The algorithm
of SHA-256's RISC-V streaming code (`Impl/Sha256/RISCV64/Stream.lean`).

The streaming state (`N + 64` bytes at `state`) is the hash value (`N` bytes)
followed by a 64-byte buffer.

* `init(state = a0)` stores the initial hash value, as 32-bit words
  (`initWords`), a byte at a time.
* `update(state = a0, count = a1, data = a2, len = a3)` processes one block
  per iteration: straight from `data` while the buffer is empty and a whole
  block remains, otherwise by copying bytes into the buffer, compressing it
  once it is full.
* `finalize(state = a0, count = a1, out = a2)` pads the buffered bytes (one or
  two blocks), compresses them and writes the digest.

`update` and `finalize` run in a frame of `frameBytes` bytes on the stack
(`alloc`), whose first 80 bytes are the scratch space of the compression
function (`name`, `code`, which they call), and in which they save the
return address, which each call replaces, and our caller's values of the
callee-saved registers we use, `s1`–`s6`, which the compression function
preserves: our own variables live there (`s1` = `state`, `s2` = the frame).
The stack pointer is 16-byte aligned, so the saves and restores are aligned
doubleword accesses.

Every argument buffer (`state`, `data`, `out`) is accessed a byte at a time,
since its alignment is not stated: byte `r` of the buffer is addressed as
`N(t3)` with `t3 = state + r` computed just before the access, and `data`
is consumed through a pointer that advances. Every comparison is a shift
(`len ≥ 64` iff `len >> 6 ≠ 0`) or a subtraction tested against zero. Every
address and branch depends only on the pointers, `count` and `len`.
-/

@[expose] public section

namespace VG.Impl.MdStream.RISCV64

open VG.RISCV64
open VG.Impl.Words.RISCV64

/-- `init` storing the words `iv`, little-endian. -/
def initWords (iv : List (BitVec 32)) : Prog isa :=
  .block ((List.range iv.length).flatMap fun k => li32 .t0 iv[k]! ++ storeLE32 .t0 .t1 .a0 (4 * k))

/-- `mv d, n` (`addi d, n, 0`). -/
def mov (d n : Reg) : Instr := .addi d n 0

/-- What distinguishes one hash function's streaming code from another's. -/
structure Params where
  /-- The size of the hash value, where the buffer starts. -/
  N : Nat
  /-- Stores the length field, from `count` in `s4`, at `s1 + N + 56`;
  writes only `t1` and `t3`. -/
  len : List Instr
  /-- Writes the digest, from the hash value at `s1`, to `s3`; writes only
  `t1` and `t2`. -/
  out : List Instr

variable (P : Params) (name : String) (code : Prog isa)

/-- The bytes of the frame: the compression function's scratch space (80
bytes), then the saved registers. -/
def frameBytes : Nat := 144

/-- The registers we save, and where in the frame. -/
def saved : List (Reg × Nat) :=
  [(.ra, 80), (.s1, 88), (.s2, 96), (.s3, 104), (.s4, 112), (.s5, 120), (.s6, 128)]

/-- Save them, with the frame's address in `t0`. -/
def save : List Instr := .addSp .t0 0 :: saved.map fun (r, d) => .store .d r .t0 d

/-- Restore them from the frame at `s2` (`s2`, the base, last). -/
def restore : List Instr :=
  (saved.filter (·.1 != .s2)).map (fun (r, d) => .load .d r .s2 d) ++ [.load .d .s2 .s2 96]

/-- Compress the block at `a1` into the hash value at `s1`, with scratch
space `s2`. -/
def compressAt : Prog isa :=
  .seq (.block [mov .a0 .s1, .li .a2 1, mov .a3 .s2]) (.call name code)

/-! ## `update`

Registers: `s3` = `data`, `s4` = bytes of `data` left, `s5` = bytes in the
buffer (`r`), `t0` = whether this iteration compresses a block (at `a1`).
The loop runs while `s4 ≠ 0`, so each iteration starts with `s4 ≥ 1` and
`s5 < 64`. -/

/-- A whole block straight from `data`. -/
def direct : List Instr :=
  [mov .a1 .s3, .addi .s3 .s3 64, .addi .s4 .s4 (-64), .li .t0 1]

/-- The byte copy loop's body. -/
def copyBody : List Instr :=
  [.load .b .t1 .s3 0, .add .t3 .s1 .s5, .store .b .t1 .t3 P.N, .addi .s3 .s3 1,
    .addi .s5 .s5 1, .addi .t2 .t2 (-1)]

/-- Copy `n = min(64 - r, len) ≥ 1` bytes of `data` into the buffer; if that
fills it, compress it. -/
def fill : Prog isa :=
  -- t2 := 64 - r; if len < 64 and len + r < 64 (i.e. len < 64 - r), t2 := len.
  .seq (.block [.li .t2 64, .sub .t2 .t2 .s5, .shift .srl .d .t1 .s4 6])
  (.seq (.ite (.zero .t1)
      (.seq (.block [.add .t1 .s4 .s5, .shift .srl .d .t1 .t1 6])
        (.ite (.zero .t1) (.block [mov .t2 .s4]) (.block [])))
      (.block []))
  (.seq (.block [.sub .s4 .s4 .t2])
  (.seq (.loop (.block (copyBody P)) (.nonzero .t2))
  -- Full: compress the buffer.
  (.seq (.block [.addi .t1 .s5 (-64)])
    (.ite (.zero .t1) (.block [.addi .a1 .s1 P.N, .li .s5 0, .li .t0 1])
      (.block []))))))

def updateBody : Prog isa :=
  .seq (.block [.li .t0 0])
  (.seq (.ite (.zero .s5)
      (.seq (.block [.shift .srl .d .t1 .s4 6]) (.ite (.zero .t1) (fill P) (.block direct)))
      (fill P))
    (.ite (.zero .t0) (.block []) (compressAt name code)))

/-- `update`, in its frame. -/
def updateMain : Prog isa :=
  .seq (.block (save ++ [mov .s1 .a0, mov .s2 .t0, mov .s3 .a2, mov .s4 .a3,
      .logicImm .and .s5 .a1 63]))
  (.seq (.ite (.zero .s4) (.block []) (.loop (updateBody P name code) (.nonzero .s4)))
    (.block restore))

def update : Prog isa := .frame (.alloc frameBytes) (updateMain P name code) (.free frameBytes)

/-! ## `finalize`

Registers: `s3` = `out`, `s4` = `count`, `s5` = bytes in the buffer (`r`),
`s6` = 1 while the block being padded is not the last one (then 0). -/

/-- The zeroing loop's body. -/
def zeroBody : List Instr :=
  [.add .t3 .s1 .s5, .store .b .t1 .t3 P.N, .addi .s5 .s5 1, .addi .t2 .t2 (-1)]

def finalizeBody : Prog isa :=
  -- Zero the buffer from `r` to 64, or to 56 in the last block.
  .seq (.block [.li .t2 64])
  (.seq (.ite (.zero .s6) (.block [.li .t2 56]) (.block []))
  (.seq (.block [.li .t1 0, .sub .t2 .t2 .s5])
  (.seq (.ite (.zero .t2) (.block []) (.loop (.block (zeroBody P)) (.nonzero .t2)))
  -- In the last block, the message length.
  (.seq (.ite (.zero .s6) (.block P.len) (.block []))
  (.seq (.block [.addi .a1 .s1 P.N])
  (.seq (compressAt name code)
    (.block [.li .s5 0, .addi .s6 .s6 (-1)])))))))

/-- `finalize`, in its frame. -/
def finalizeMain : Prog isa :=
  .seq (.block (save ++ [mov .s1 .a0, mov .s2 .t0, mov .s3 .a2, mov .s4 .a1,
      .logicImm .and .s5 .s4 63,
      -- The `0x80` byte.
      .li .t1 0x80, .add .t3 .s1 .s5, .store .b .t1 .t3 P.N, .addi .s5 .s5 1,
      -- Two blocks iff that leaves fewer than 8 bytes for the length (r ≥ 57).
      .addi .s6 .s5 7, .shift .srl .d .s6 .s6 6]))
  (.seq (.loop (finalizeBody P name code) (.zero .s6))
    (.block (P.out ++ restore)))

def finalize : Prog isa := .frame (.alloc frameBytes) (finalizeMain P name code) (.free frameBytes)

end VG.Impl.MdStream.RISCV64
