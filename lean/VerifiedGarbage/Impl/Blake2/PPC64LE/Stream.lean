module

public import VerifiedGarbage.Impl.Blake2.PPC64LE

/-!
# Streaming BLAKE2: PPC64LE implementation

`init`, `update` and `finalize` for words of `w` bits (`Spec.Blake2.b` or
`Spec.Blake2.s`), on the streaming state of `Spec.Blake2.Repr`, as on AArch64
(`Impl/Blake2/AArch64/Stream.lean`): the hash value (`N = 8 · w/8` bytes)
followed by a `B`-byte buffer (`B = 16 · w/8`) holding the last block of the
data so far, 1 to `B` bytes of it (none for empty data). The caller keeps the
byte count, `count`, from which the number of buffered bytes follows.

* `init(state = r3, outlen = r4, key = r5, keylen = r6)` stores the initial
  hash value and, for a key, the key block in the buffer.
* `update(state = r3, count = r4, data = r5, len = r6, scratch = r7)` fills
  the buffer; if more data follows, compresses it, compresses every block of
  `data` but the last straight from `data`, and copies that last one (1 to
  `B` bytes) to the buffer.
* `finalize(state = r3, count = r4, out = r5, scratch = r6)` pads the
  buffered block with zeros, compresses it as the last block, and writes the
  hash value to `out`.

The compression function (`compress`, `Impl/Blake2/PPC64LE.lean`) is called
with `scratch` as its scratch space; it never writes `r24`–`r31`, so our own
variables live in `r26`–`r31` (`r26` = `state`, `r27` = `scratch`, `r28` =
`data` or `out`, `r29` = bytes of `data` left, `r30` = bytes in the buffer,
`r31` = the byte count), and our caller's values of those registers are
saved in `scratch[512..560)`. Our return address (the link register), which
each call replaces, is moved to `r0` and saved in a stack frame around the
whole function.

Only register-plus-displacement addressing is used, so byte `r` of the
buffer is addressed as `N(r12)` with `r12 = state + r` computed just before
the access, and `data` is consumed through a pointer that advances. Every
comparison is a shift or a subtraction tested against zero. Every address and
branch depends only on the pointers, `count`, `len`, `outlen` and `keylen`.
-/

@[expose] public section

namespace VG.Impl.Blake2.PPC64LE.Stream

open VG.PPC64LE
open VG.Impl.Blake2.PPC64LE (sz ws lbb movImm compress)

/-- `mr d, n` (as `addi d, n, 0`; `n` is not `r0`). -/
def mov (d n : Reg) : Instr := .addi d n 0

section
variable (w : Nat)

/-- The size of the hash value, where the buffer starts. -/
def N : Nat := 8 * ws w
/-- The block size. -/
def B : Nat := 16 * ws w

end

/-- The nonvolatile registers we use, and where they are saved in `scratch`. -/
def saved : List (Reg × Nat) :=
  [(.r26, 512), (.r27, 520), (.r28, 528), (.r29, 536), (.r30, 544), (.r31, 552)]

/-- Save them, with `scratch` in `b`. -/
def save (b : Reg) : List Instr := saved.map fun (r, d) => .store .d r b d

/-- Restore them from `scratch` in `r27` (`r27`, the base, last). -/
def restore : List Instr :=
  [.load .d .r26 .r27 512, .load .d .r28 .r27 528, .load .d .r29 .r27 536,
    .load .d .r30 .r27 544, .load .d .r31 .r27 552, .load .d .r27 .r27 520]

section
variable {w : Nat} (P : Spec.Blake2.Params w)

/-- `r30` := the number of bytes in the buffer for the byte count in `r31`:
`((count - 1) mod B) + 1`, or 0 if `count = 0`. -/
def bufLen : Prog isa :=
  .seq (.block [.subi .r30 .r31 1, .li .r9 (B w - 1), .logic .and .r30 .r30 .r9, .addi .r30 .r30 1])
    (.ite (.zero .d .r31) (.block [.li .r30 0]) (.block []))

/-- Compress into the hash value at `r26`, with scratch space `r27`, after
`args` set the blocks (`r4`), their number (`r5`), the counter (`r6`) and the
final block flag (`r7`). -/
def compressWith (args : List Instr) : Prog isa :=
  .seq (.block ([mov .r3 .r26] ++ args ++ [mov .r8 .r27]))
    (.call (if w = 64 then "vg_blake2b_compress" else "vg_blake2s_compress") (compress P))

/-- The loop copying `r11 ≥ 1` bytes of `data` (at `r28`) to the buffer, from
byte `r30` on. -/
def copyLoop : Prog isa :=
  .loop (.block [.lbz .r9 .r28 0, .add .r12 .r26 .r30, .stb .r9 .r12 (N w),
    .addi .r28 .r28 1, .addi .r30 .r30 1, .subi .r11 .r11 1]) (.nonzero .d .r11)

/-! ## `update` -/

/-- Copy `min(B - r30, r29)` bytes of `data` to the buffer: `r11 := B - r30`,
and if `r29 < B` and `r29 + r30 < B` (i.e. `r29 < B - r30`), `r11 := r29`. -/
def fill : Prog isa :=
  .seq (.block [.li .r11 (B w), .sub .r11 .r11 .r30, .lsr .d .r9 .r29 (lbb w)])
  (.seq (.ite (.zero .d .r9)
      (.seq (.block [.add .r9 .r29 .r30, .lsr .d .r9 .r9 (lbb w)])
        (.ite (.zero .d .r9) (.block [mov .r11 .r29]) (.block [])))
      (.block []))
  (.seq (.block [.sub .r29 .r29 .r11, .add .r31 .r31 .r11])
    (.ite (.zero .d .r11) (.block []) (copyLoop (w := w)))))

/-- Compress the (full) buffer, which is not the last block: its counter is
the byte count. -/
def compressBuf : Prog isa :=
  .seq (compressWith P [.addi .r4 .r26 (N w), .li .r5 1, mov .r6 .r31, .li .r7 0])
    (.block [.li .r30 0])

/-- If the buffer is not empty: fill it, and if more data follows, compress
it. -/
def head : Prog isa :=
  .ite (.zero .d .r30) (.block [])
    (.seq (fill (w := w)) (.ite (.zero .d .r29) (.block []) (compressBuf P)))

/-- With the buffer empty and `r29 ≥ 1` bytes left: compress all the blocks of
`data` but the last, `(r29 - 1) / B` of them, straight from `data`, leaving
`((r29 - 1) mod B) + 1` bytes. -/
def direct : Prog isa :=
  .seq (.block [.subi .r9 .r29 1, .lsr .d .r10 .r9 (lbb w)])
    (.ite (.zero .d .r10) (.block [])
      (.seq (compressWith P [mov .r4 .r28, mov .r5 .r10, .addi .r6 .r31 (B w), .li .r7 0])
        (.block [.subi .r9 .r29 1, .li .r10 (B w - 1),
          .logic .and .r9 .r9 .r10, .addi .r9 .r9 1, .sub .r10 .r29 .r9,
          .add .r28 .r28 .r10, .add .r31 .r31 .r10, mov .r29 .r9])))

/-- Copy the last `r29` (1 to `B`) bytes of `data` to the (empty) buffer. -/
def tail : Prog isa :=
  .seq (.block [mov .r11 .r29, .add .r31 .r31 .r29, .li .r29 0]) (copyLoop (w := w))

/-- The rest of `data`, if any, after `head`. -/
def rest : Prog isa :=
  .ite (.zero .d .r29) (.block []) (.seq (direct P) (tail (w := w)))

/-- Save registers and set up ours. -/
def updateStart : List Instr :=
  save .r7 ++ [mov .r26 .r3, mov .r27 .r7, mov .r28 .r5, mov .r29 .r6, mov .r31 .r4]

/-- `update`, but for saving the link register. -/
def updateMain : Prog isa :=
  .seq (.block updateStart) (.seq (bufLen (w := w))
    (.seq (.ite (.zero .d .r29) (.block []) (.seq (head P) (rest P))) (.block restore)))

def update : Prog isa :=
  .seq (.block [.mflr .r0])
    (.seq (.frame (.push .r0) (updateMain P) (.pop .r0)) (.block [.mtlr .r0]))

/-! ## `finalize` -/

/-- The loop zeroing the buffer from byte `r30` on, `r11 ≥ 1` bytes (`r9 = 0`). -/
def zeroLoop : Prog isa :=
  .loop (.block [.add .r12 .r26 .r30, .stb .r9 .r12 (N w), .addi .r30 .r30 1,
    .subi .r11 .r11 1]) (.nonzero .d .r11)

/-- Zero the rest of the buffer. -/
def pad : Prog isa :=
  .seq (.block [.li .r9 0, .li .r11 (B w), .sub .r11 .r11 .r30])
    (.ite (.zero .d .r11) (.block []) (zeroLoop (w := w)))

/-- Compress the buffer as the last block: its counter is the byte count. -/
def compressLast : Prog isa :=
  compressWith P [.addi .r4 .r26 (N w), .li .r5 1, mov .r6 .r31, .li .r7 1]

/-- Copy the hash value (at `r26`) to `out` (at `r28`). -/
def output : List Instr :=
  (List.range (N w / 8)).flatMap fun k => [.load .d .r9 .r26 (8 * k), .store .d .r9 .r28 (8 * k)]

/-- `finalize`, but for saving the link register. -/
def finalizeMain : Prog isa :=
  .seq (.block (save .r6 ++ [mov .r26 .r3, mov .r27 .r6, mov .r28 .r5, mov .r31 .r4]))
    (.seq (bufLen (w := w)) (.seq (pad (w := w)) (.seq (compressLast P)
      (.block (output (w := w) ++ restore)))))

def finalize : Prog isa :=
  .seq (.block [.mflr .r0])
    (.seq (.frame (.push .r0) (finalizeMain P) (.pop .r0)) (.block [.mtlr .r0]))

/-! ## `init`

Uses only `r3`–`r6` and `r9`–`r12`. -/

/-- `h := IV`, with the parameter block `0x0101kknn` XORed into `h[0]`
(`kk` = `keylen` in `r6`, `nn` = `outlen` in `r4`). -/
def initState : List Instr :=
  (List.finRange 7).flatMap (fun i =>
    movImm w .r9 ((P.IV[i.1 + 1]'(by omega)).setWidth 64) ++
      ([.store (sz w) .r9 .r3 (ws w * (i.1 + 1))] : List Instr)) ++
  movImm w .r9 ((P.IV[0] ^^^ 0x01010000).setWidth 64) ++
  ([.lsl .r10 .r6 8, .logic .xor .r9 .r9 .r10, .logic .xor .r9 .r9 .r4,
    .store (sz w) .r9 .r3 0] : List Instr)

/-- Zero the buffer and copy the `r6 ≥ 1` bytes of the key (at `r5`) to it. -/
def keyBlock : Prog isa :=
  .seq (.block (.li .r9 0 :: ((List.range (B w / 8)).map fun j => .store .d .r9 .r3 (N w + 8 * j)) ++
      ([.addi .r12 .r3 (N w)] : List Instr)))
    (.loop (.block [.lbz .r9 .r5 0, .stb .r9 .r12 0, .addi .r5 .r5 1, .addi .r12 .r12 1,
      .subi .r6 .r6 1]) (.nonzero .d .r6))

def init : Prog isa :=
  .seq (.block (initState P)) (.ite (.zero .d .r6) (.block []) (keyBlock (w := w)))

end

end VG.Impl.Blake2.PPC64LE.Stream
