module

public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# Streaming Merkle–Damgård hash functions: PPC64LE implementation

The streaming `update` and `finalize` of MD5, SHA-1, SHA-256 and the SHA-512
family, which differ only in their sizes, in how they store the message
length and output the digest, and in the compression function they call
(`Params`). Each hash function's `Impl/<Alg>/PPC64LE/Stream.lean`
instantiates them. The same algorithm as on AArch64
(`Impl/MdStream/AArch64.lean`).

The streaming state (`N + B` bytes at `state`) is the hash value (`N` bytes)
followed by a `B`-byte buffer.

* `update(state = r3, count = r4, data = r5, len = r6, scratch = r7)`
  compresses, in each iteration, every whole block left in `data` with one
  call if the buffer is empty (so that implementations that process several
  blocks at once can), and otherwise copies data into the buffer (eight
  bytes at a time, then one at a time), compressing it once it is full.
* `finalize(state = r3, count = r4, out = r5, scratch = r6)` pads the
  buffered bytes (one or two blocks, zeroing eight bytes at a time),
  compresses them and writes the digest.

`update` and `finalize` call the compression function (`name`, `code`) with
`scratch[0..so)` as its scratch space. It preserves `r14`–`r31`, so our own
variables live in `r26`–`r31` (`r26` = `state`, `r27` = `scratch`), and our
caller's values of those registers are saved in `scratch[so..so+48)`. Our
return address (the link register), which each call replaces, is moved to
`r0` and saved in a stack frame around the whole function.

Only register-plus-displacement addressing is used (and register-plus-register
for the byte-reversed stores), so byte `r` of the buffer is addressed as
`N(r11)` with `r11 = state + r` computed just before the access, and `data`
is consumed through a pointer that advances. Every comparison is a shift
(`len ≥ B` iff `len >> log₂ B ≠ 0`) or a subtraction tested against zero.
Every address and branch depends only on the pointers, `count` and `len`.
-/

@[expose] public section

namespace VG.Impl.MdStream.PPC64LE

open VG.PPC64LE

/-- `mr d, n` (as `addi d, n, 0`; `n` is not `r0`). -/
def mov (d n : Reg) : Instr := .addi d n 0

/-- What distinguishes one hash function's streaming code from another's. -/
structure Params where
  /-- The size of the hash value, where the buffer starts. -/
  N : Nat
  /-- The block size, a power of two. -/
  B : Nat
  /-- The size of the length field at the end of the last block. -/
  L : Nat
  /-- Where our caller's registers are saved in the scratch space, after the
  compression function's own. -/
  so : Nat
  /-- Stores the length field, from `count` in `r29`, at `r26 + N + B - L`;
  writes only `r8` and `r11`. -/
  len : List Instr
  /-- Writes the digest, from the hash value at `r26`, to `r28`; writes only
  `r8` and `r11`. -/
  out : List Instr

variable (P : Params)

/-- `log₂ B`, the shift that divides by the block size. -/
def lg : Nat := Nat.log2 P.B

/-- The nonvolatile registers we use, and where they are saved in `scratch`. -/
def saved : List (Reg × Nat) :=
  [(.r26, P.so), (.r27, P.so + 8), (.r28, P.so + 16), (.r29, P.so + 24), (.r30, P.so + 32),
    (.r31, P.so + 40)]

/-- Save them, with `scratch` in `b`. -/
def save (b : Reg) : List Instr := (saved P).map fun (r, d) => .store .d r b d

/-- Restore them from `scratch` in `r27` (`r27`, the base, last). -/
def restore : List Instr :=
  [.load .d .r26 .r27 P.so, .load .d .r28 .r27 (P.so + 16), .load .d .r29 .r27 (P.so + 24),
    .load .d .r30 .r27 (P.so + 32), .load .d .r31 .r27 (P.so + 40), .load .d .r27 .r27 (P.so + 8)]

/-- Compress the blocks at `r4` into the hash value at `r26`, with scratch
space `r27`, by calling the compression function `name` (whose code is
`code`), after `n` sets their number in `r5`. -/
def compressWith (n : Instr) (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block [mov .r3 .r26, n, mov .r6 .r27]) (.call name code)

/-- Compress one block. -/
def compressAt : String → Prog isa → Prog isa := compressWith (.li .r5 1)

/-- Compress `r9` blocks. -/
def compressN : String → Prog isa → Prog isa := compressWith (mov .r5 .r9)

/-! ## `update`

Registers: `r28` = `data`, `r29` = bytes of `data` left, `r30` = bytes in the
buffer (`r`), `r9` = the number of blocks this iteration compresses (at
`r4`).
The loop runs while `r29 ≠ 0`, so each iteration starts with `r29 ≥ 1` and
`r30 < B`. -/

/-- Every whole block left, straight from `data`: `len >> log₂ B` blocks,
`(len >> log₂ B) << log₂ B` bytes. -/
def direct : List Instr :=
  [mov .r4 .r28, .lsr .d .r9 .r29 (lg P), .lsl .r8 .r9 (lg P), .add .r28 .r28 .r8,
    .sub .r29 .r29 .r8]

/-- Store `r8` as the eight buffer bytes from `r` (in `r30`), through `r11 =
state + r`: with the offset `N` in the store if it is a multiple of 4 (as
`std`'s displacement must be), and added to `r11` first otherwise. -/
def storeWord : List Instr :=
  if P.N % 4 = 0 then [.add .r11 .r26 .r30, .store .d .r8 .r11 P.N]
  else [.add .r11 .r26 .r30, .addi .r11 .r11 P.N, .store .d .r8 .r11 0]

/-- The eight-byte copy loop's body. -/
def copyWordBody : List Instr :=
  [.load .d .r8 .r28 0] ++ storeWord P ++
    [.addi .r28 .r28 8, .addi .r30 .r30 8, .subi .r10 .r10 8, .lsr .d .r12 .r10 3]

/-- The byte copy loop's body. -/
def copyBody : List Instr :=
  [.lbz .r8 .r28 0, .add .r11 .r26 .r30, .stb .r8 .r11 P.N, .addi .r28 .r28 1,
    .addi .r30 .r30 1, .subi .r10 .r10 1]

/-- Copy `r10` bytes of `data` into the buffer at `r`: eight at a time (`r12 =
r10 >> 3` of them), then one at a time. -/
def copy : Prog isa :=
  .seq (.block [.lsr .d .r12 .r10 3])
  (.seq (.ite (.zero .d .r12) (.block []) (.loop (.block (copyWordBody P)) (.nonzero .d .r12)))
    (.ite (.zero .d .r10) (.block []) (.loop (.block (copyBody P)) (.nonzero .d .r10))))

/-- Copy `n = min(B - r, len) ≥ 1` bytes of `data` into the buffer; if that
fills it, compress it. -/
def fill : Prog isa :=
  -- r10 := B - r; if len < B and len + r < B (i.e. len < B - r), r10 := len.
  .seq (.block [.li .r10 P.B, .sub .r10 .r10 .r30, .lsr .d .r8 .r29 (lg P)])
  (.seq (.ite (.zero .d .r8)
      (.seq (.block [.add .r8 .r29 .r30, .lsr .d .r8 .r8 (lg P)])
        (.ite (.zero .d .r8) (.block [mov .r10 .r29]) (.block [])))
      (.block []))
  (.seq (.block [.sub .r29 .r29 .r10])
  (.seq (copy P)
  -- Full: compress the buffer.
  (.seq (.block [.subi .r8 .r30 P.B])
    (.ite (.zero .d .r8) (.block [.addi .r4 .r26 P.N, .li .r30 0, .li .r9 1])
      (.block []))))))

def updateBody (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block [.li .r9 0])
  (.seq (.ite (.zero .d .r30)
      (.seq (.block [.lsr .d .r8 .r29 (lg P)]) (.ite (.zero .d .r8) (fill P) (.block (direct P))))
      (fill P))
    (.ite (.zero .d .r9) (.block []) (compressN name code)))

/-- Save registers and set up ours. -/
def updateStart : List Instr :=
  save P .r7 ++ [mov .r26 .r3, mov .r27 .r7, mov .r28 .r5, mov .r29 .r6,
    .li .r8 (P.B - 1), .logic .and .r30 .r4 .r8]

/-- `update`, but for saving the link register. -/
def updateMain (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block (updateStart P))
  (.seq (.ite (.zero .d .r29) (.block []) (.loop (updateBody P name code) (.nonzero .d .r29)))
    (.block (restore P)))

def update (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block [.mflr .r0])
    (.seq (.frame (.push .r0) (updateMain P name code) (.pop .r0)) (.block [.mtlr .r0]))

/-! ## `finalize`

Registers: `r28` = `out`, `r29` = `count`, `r30` = bytes in the buffer (`r`),
`r31` = 1 while the block being padded is not the last one (then 0). -/

/-- The eight-byte zeroing loop's body. -/
def zeroWordBody : List Instr :=
  storeWord P ++ [.addi .r30 .r30 8, .subi .r10 .r10 8, .lsr .d .r12 .r10 3]

/-- The byte zeroing loop's body. -/
def zeroBody : List Instr :=
  [.add .r11 .r26 .r30, .stb .r8 .r11 P.N, .addi .r30 .r30 1, .subi .r10 .r10 1]

/-- Zero `r10` buffer bytes from `r` (`r8 = 0`): eight at a time (`r12 = r10 >>
3` of them), then one at a time. -/
def zero : Prog isa :=
  .seq (.block [.lsr .d .r12 .r10 3])
  (.seq (.ite (.zero .d .r12) (.block []) (.loop (.block (zeroWordBody P)) (.nonzero .d .r12)))
    (.ite (.zero .d .r10) (.block []) (.loop (.block (zeroBody P)) (.nonzero .d .r10))))

def finalizeBody (name : String) (code : Prog isa) : Prog isa :=
  -- Zero the buffer from `r` to `B`, or to `B - L` in the last block.
  .seq (.block [.li .r10 P.B])
  (.seq (.ite (.zero .d .r31) (.block [.li .r10 (P.B - P.L)]) (.block []))
  (.seq (.block [.li .r8 0, .sub .r10 .r10 .r30])
  (.seq (zero P)
  -- In the last block, the length field.
  (.seq (.ite (.zero .d .r31) (.block P.len) (.block []))
  (.seq (.block [.addi .r4 .r26 P.N])
  (.seq (compressAt name code)
    (.block [.li .r30 0, .subi .r31 .r31 1])))))))

/-- Save registers, append the `0x80` byte and choose the number of blocks. -/
def finalizeStart : List Instr :=
  save P .r6 ++ [mov .r26 .r3, mov .r27 .r6, mov .r28 .r5, mov .r29 .r4,
    .li .r8 (P.B - 1), .logic .and .r30 .r29 .r8,
    -- The `0x80` byte.
    .li .r8 0x80, .add .r11 .r26 .r30, .stb .r8 .r11 P.N, .addi .r30 .r30 1,
    -- Two blocks iff that leaves fewer than `L` bytes for the length (r > B - L).
    .addi .r31 .r30 (P.L - 1), .lsr .d .r31 .r31 (lg P)]

/-- `finalize`, but for saving the link register. -/
def finalizeMain (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block (finalizeStart P))
  (.seq (.loop (finalizeBody P name code) (.zero .d .r31))
    (.block (P.out ++ restore P)))

def finalize (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block [.mflr .r0])
    (.seq (.frame (.push .r0) (finalizeMain P name code) (.pop .r0)) (.block [.mtlr .r0]))

/-! ## Length fields and digests

The `len` and `out` of the hash functions here. -/

/-- The length in bits, `8 · count` (modulo 2⁶⁴, from `count` in `r29`), as 8
bytes at `r26 + d`, big-endian (`stdbrx`, at the offset in `r11`) if `be`
and little-endian otherwise. A little-endian store at an offset that is not
a multiple of 4 is addressed through `r11`. -/
def len64 (d : Nat) (be : Bool) : List Instr :=
  [.add .r8 .r29 .r29, .add .r8 .r8 .r8, .add .r8 .r8 .r8] ++
    (if be then [.li .r11 d, .storeRev .d .r8 .r26 .r11]
    else if d % 4 = 0 then [.store .d .r8 .r26 d] else [.addi .r11 .r26 d, .store .d .r8 .r11 0])

/-- The `n` 32-bit words at `r26`, written to `r28`, big-endian (`stwbrx`, at
the offset in `r11`) if `be` and little-endian otherwise. -/
def out32 (n : Nat) (be : Bool) : List Instr :=
  (List.range n).flatMap fun k =>
    [.load .w .r8 .r26 (4 * k)] ++
      (if be then [.li .r11 (4 * k), .storeRev .w .r8 .r28 .r11] else [.store .w .r8 .r28 (4 * k)])

/-- The `n` 64-bit words at `r26`, written to `r28` big-endian. -/
def out64 (n : Nat) : List Instr :=
  (List.range n).flatMap fun k =>
    [.load .d .r8 .r26 (8 * k), .li .r11 (8 * k), .storeRev .d .r8 .r28 .r11]

/-- The length in bits as a 16-byte big-endian integer at `r26 + d`:
`count >> 61`, then `8 · count` (modulo 2⁶⁴). -/
def len128 (d : Nat) : List Instr :=
  [.lsr .d .r8 .r29 61, .li .r11 d, .storeRev .d .r8 .r26 .r11] ++ len64 (d + 8) true

end VG.Impl.MdStream.PPC64LE
