module

public import VerifiedGarbage.Impl.MdStream.AArch64

/-!
# One-shot Merkle–Damgård digests: AArch64 implementation

`digest(data = x0, len = x1, out = x2)` hashes a message in memory in one
call, in a frame of its own (`frameBytes P` bytes at `sp`):

* `[0, N)`: the hash value, and `[N, N + B)`: the last block or two, laid out
  as a streaming state, so that each hash function's `Params.len` and
  `Params.out` (which address them through `x19`) write the length field and
  the digest;
* `[scO, scO + so)`: the compression function's scratch space;
* at `slO`: our caller's `x19`, `x21`, `x22`, `x25`–`x28` and `x30`.

It runs the initial hash value's code `init` on the hash value, compresses
every whole block straight from `data` with one call, then builds the last
block in the frame: it zeroes it (`zeroBuf`), copies the bytes left sixteen at
a time and then one at a time, appends the `0x80` byte, compresses it and
zeroes it again if the length field does not fit after them, stores the
length field (`P.len`) and compresses it. It writes the digest (`P.out`),
zeroes the hash value and the block, and restores the registers.

Every block the compression function reads from the frame is written there
by sixteen-byte stores at the sixteen-byte offsets it loads from, but for the
one holding the last bytes and the `0x80` byte.

`len` is in `x25`, `out` in `x26`, the message's next byte in `x27` and the
number of blocks or bytes being handled in `x28`, which no compression
function writes, so they survive its calls in registers; every other address
is `sp` plus a constant. Every address and branch depends only on `data`,
`len`, `out` and `sp`.
-/

@[expose] public section

namespace VG.Impl.MdStream.AArch64.OneShot

open VG.AArch64

variable (P : Params)

/-- Where the scratch space is in the frame: after the hash value and the
block, at a multiple of 16. -/
def scO : Nat := (P.N + P.B + 15) / 16 * 16

/-- Where our caller's registers are saved. -/
def slO : Nat := scO P + P.so

/-- The frame's size, a multiple of 16. -/
def frameBytes : Nat := (slO P + 64 + 15) / 16 * 16

/-- Save our caller's `x19`, `x21`, `x22`, `x25`–`x28` and `x30`, keep `data`,
`len` and `out`, and point `x0` at the hash value for `init`. -/
def setup : List Instr :=
  [.addSp .x10 (slO P), .stp .x19 .x21 .x10 0, .stp .x22 .x25 .x10 16, .stp .x26 .x27 .x10 32,
    .stp .x28 .x30 .x10 48, mov .x25 .x1, mov .x26 .x2, mov .x27 .x0, .addSp .x0 0]

/-- Restore them, through `x16`. -/
def restore : List Instr :=
  [.addSp .x16 (slO P), .ldp .x19 .x21 .x16 0, .ldp .x22 .x25 .x16 16, .ldp .x26 .x27 .x16 32,
    .ldp .x28 .x30 .x16 48]

/-- Call the compression function on the hash value, with `blocks` setting
`x1` and `x2` to the blocks and their number. -/
def compressWith (blocks : List Instr) (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block (.addSp .x0 0 :: blocks ++ [.addSp .x3 (scO P)])) (.call name code)

/-- Compress the frame's block once. -/
def compressBuf : String → Prog isa → Prog isa :=
  compressWith P [.addSp .x1 P.N, .movz .x .x2 1 0]

/-- Every whole block of the message, straight from `data` (in `x27`), which
then points past them. -/
def whole (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block [.lsr .x .x28 .x25 (lg P)])
    (.ite (.zero .x .x28) (.block [])
      (.seq (compressWith P [mov .x1 .x27, mov .x2 .x28] name code)
        (.block [.lsl .x .x9 .x28 (lg P), .add .x .x27 .x27 .x9])))

/-- Zero the block, through `x12` (which is left pointing at it), with `x9 = 0`. -/
def zeroBuf : List Instr :=
  [.movz .x .x9 0 0, .addSp .x12 P.N] ++ (List.range (P.B / 16)).map fun k => .stp .x9 .x9 .x12 (16 * k)

/-- Copy sixteen bytes from `x27` to `x12`, advancing both. -/
def copy16 : List Instr :=
  [.ldp .x9 .x10 .x27 0, .stp .x9 .x10 .x12 0, .addImm .x .x27 .x27 16, .addImm .x .x12 .x12 16,
    .subImm .x .x13 .x13 1]

/-- Copy a byte from `x27` to `x12`, advancing both. -/
def copy1 : List Instr :=
  [.ldrb .x9 .x27 0, .strb .x9 .x12 0, .addImm .x .x27 .x27 1, .addImm .x .x12 .x12 1,
    .subImm .x .x11 .x11 1]

/-- Copy the `len mod B` bytes left (counted in `x28`) to the block at `x12`,
sixteen at a time (`x13` of them), then one at a time (`x11`), and append the
`0x80` byte. -/
def copyTail : Prog isa :=
  .seq (.block [.movz .x .x9 (BitVec.ofNat 16 (P.B - 1)) 0, .logic .and .x .x28 .x25 .x9,
      .lsr .x .x13 .x28 4])
  (.seq (.ite (.zero .x .x13) (.block []) (.loop (.block copy16) (.nonzero .x .x13)))
  (.seq (.block [.movz .x .x9 15 0, .logic .and .x .x11 .x28 .x9])
  (.seq (.ite (.zero .x .x11) (.block []) (.loop (.block copy1) (.nonzero .x .x11)))
    (.block [.movz .x .x9 0x80 0, .strb .x9 .x12 0]))))

/-- The last block or two: the bytes left, `0x80`, zeros and the length field.
It takes two blocks iff `len mod B + 1 > B - L`, that is iff
`(len mod B + L) >> log₂ B ≠ 0`. -/
def tail (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block (zeroBuf P))
  (.seq (copyTail P)
  (.seq (.block [.addImm .x .x9 .x28 P.L, .lsr .x .x9 .x9 (lg P)])
  (.seq (.ite (.zero .x .x9) (.block []) (.seq (compressBuf P name code) (.block (zeroBuf P))))
  (.seq (.block ([.addSp .x19 0, mov .x22 .x25] ++ P.len))
    (compressBuf P name code)))))

/-- Zero the hash value and the block, through `x16` (`sp`) and `x17` (zero). -/
def wipe : List Instr :=
  [.addSp .x16 0, .movz .x .x17 0 0] ++
    (List.range ((P.N + P.B + 15) / 16)).map fun k => .stp .x17 .x17 .x16 (16 * k)

/-- Write the digest to `out`, zero the frame's hash value and block and
restore the registers. -/
def finish : List Instr := [.addSp .x19 0, mov .x21 .x26] ++ P.out ++ wipe P ++ restore P

/-- The body, inside the frame. -/
def body (init : Prog isa) (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block (setup P)) (.seq init (.seq (whole P name code) (.seq (tail P name code)
    (.block (finish P)))))

/-- The one-shot digest: `init` stores the initial hash value at `x0` (using
only `x9` and `x10`), `P` is the hash function's sizes, length field and digest. -/
def digest (init : Prog isa) (name : String) (code : Prog isa) : Prog isa :=
  .frame (.alloc (frameBytes P)) (body P init name code) (.free (frameBytes P))

end VG.Impl.MdStream.AArch64.OneShot
