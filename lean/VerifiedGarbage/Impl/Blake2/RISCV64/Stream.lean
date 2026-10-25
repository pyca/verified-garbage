module

public import VerifiedGarbage.Impl.Blake2.RISCV64

/-!
# Streaming BLAKE2: RISC-V implementation

`init`, `update` and `finalize` for words of `w` bits (`Spec.Blake2.b` or
`Spec.Blake2.s`), on the streaming state of `Spec.Blake2.Repr`, as on PPC64LE
(`Impl/Blake2/PPC64LE/Stream.lean`): the hash value (`N = 8 · w/8` bytes)
followed by a `B`-byte buffer (`B = 16 · w/8`) holding the last block of the
data so far, 1 to `B` bytes of it (none for empty data). The caller keeps the
byte count, `count`, from which the number of buffered bytes follows.

* `init(state = a0, outlen = a1, key = a2, keylen = a3)` stores the initial
  hash value and, for a key, the key block in the buffer.
* `update_scratch(state = a0, count = a1, data = a2, len = a3, scratch = a4)`
  fills the buffer; if more data follows, compresses it, compresses every
  block of `data` but the last straight from `data`, and copies that last one
  (1 to `B` bytes) to the buffer.
* `finalize_scratch(state = a0, count = a1, out = a2, scratch = a3)` pads the
  buffered block with zeros, compresses it as the last block, and writes the
  hash value to `out`.
* `update` and `finalize` are those with their scratch space in a frame on
  the stack (`alloc`).

The streaming state, the data, the key and `out` are argument buffers, whose
alignment the contracts do not state, so they are accessed a byte at a time
(the words of the initial hash value a byte at a time, `stLE`). The scratch
space is rounded up to a multiple of 8 (it has room to spare): its first 512
bytes are the compression function's (`compress`, `Impl/Blake2/RISCV64.lean`,
which rounds its own scratch pointer up again, to the same address), and the
next 48 hold the return address, which each call replaces, and our caller's
values of the callee-saved registers we use, `s7`–`s11`, which the compression
function never writes (it saves and restores `s0`–`s6`, so it would leave
values loaded from memory in those): our variables live there (`s7` =
`state`, `s8` = the rounded scratch pointer, `s9` = `data` or `out`, `s10` =
bytes of `data` left, `s11` = the byte count). The number of bytes in the
buffer, in `a7`, is set again after each call, which may change it.

Byte `r` of the buffer is addressed as `N(t2)` with `t2 = state + r` computed
just before the access, and `data` is consumed through a pointer that
advances. Every comparison is a shift or a subtraction tested against zero.
Every address and branch depends only on the pointers, `count`, `len`,
`outlen` and `keylen`.
-/

@[expose] public section

namespace VG.Impl.Blake2.RISCV64.Stream

open VG.RISCV64
open VG.Impl.Blake2.RISCV64 (ws lbb movImm stLE compress)

/-- `mv d, n` (`addi d, n, 0`). -/
def mov (d n : Reg) : Instr := .addi d n 0

section
variable (w : Nat)

/-- The size of the hash value, where the buffer starts. -/
def N : Nat := 8 * ws w
/-- The block size. -/
def B : Nat := 16 * ws w

end

/-- The bytes of `update`'s and `finalize`'s frames: the scratch space of
the `_scratch` functions (`[u64; 72]`). -/
def frameBytes : Nat := 576

/-- The registers we save, and where in the (rounded) scratch space; `s8`,
the base of the restores, last. -/
def saved : List (Reg × Nat) :=
  [(.ra, 512), (.s7, 520), (.s9, 528), (.s10, 536), (.s11, 544), (.s8, 552)]

/-- Round the scratch pointer in `sc` up into `t0`, and save the registers
there. -/
def save (sc : Reg) : List Instr :=
  [.addi .t0 sc 7, .logicImm .and .t0 .t0 (-8)] ++ saved.map fun (r, d) => .store .d r .t0 d

/-- Restore them, from the scratch space in `s8` (`s8` last). -/
def restore : List Instr := saved.map fun (r, d) => .load .d r .s8 d

section
variable {w : Nat} (P : Spec.Blake2.Params w)

/-- `a7` := the number of bytes in the buffer for the byte count in `s11`:
`((count - 1) mod B) + 1`, or 0 if `count = 0`. -/
def bufLen : Prog isa :=
  .seq (.block [.addi .a7 .s11 (-1), .logicImm .and .a7 .a7 (B w - 1 : Nat), .addi .a7 .a7 1])
    (.ite (.zero .s11) (.block [.li .a7 0]) (.block []))

/-- Compress into the hash value at `s7`, with scratch space `s8`, after
`args` set the blocks (`a1`), their number (`a2`), the counter (`a3`) and the
final block flag (`a4`). -/
def compressWith (args : List Instr) : Prog isa :=
  .seq (.block ([mov .a0 .s7] ++ args ++ [mov .a5 .s8]))
    (.call (if w = 64 then "vg_blake2b_compress" else "vg_blake2s_compress") (compress P))

/-- The loop copying `t3 ≥ 1` bytes of `data` (at `s9`) to the buffer, from
byte `a7` on. -/
def copyLoop : Prog isa :=
  .loop (.block [.load .b .t1 .s9 0, .add .t2 .s7 .a7, .store .b .t1 .t2 (N w),
    .addi .s9 .s9 1, .addi .a7 .a7 1, .addi .t3 .t3 (-1)]) (.nonzero .t3)

/-! ## `update` -/

/-- Copy `min(B - a7, s10)` bytes of `data` to the buffer: `t3 := B - a7`,
and if `s10 < B` and `s10 + a7 < B` (i.e. `s10 < B - a7`), `t3 := s10`. -/
def fill : Prog isa :=
  .seq (.block [.li .t3 (B w : Nat), .sub .t3 .t3 .a7, .shift .srl .d .t1 .s10 (lbb w)])
  (.seq (.ite (.zero .t1)
      (.seq (.block [.add .t1 .s10 .a7, .shift .srl .d .t1 .t1 (lbb w)])
        (.ite (.zero .t1) (.block [mov .t3 .s10]) (.block [])))
      (.block []))
  (.seq (.block [.sub .s10 .s10 .t3, .add .s11 .s11 .t3])
    (.ite (.zero .t3) (.block []) (copyLoop (w := w)))))

/-- Compress the (full) buffer, which is not the last block: its counter is
the byte count. -/
def compressBuf : Prog isa :=
  .seq (compressWith P [.addi .a1 .s7 (N w : Nat), .li .a2 1, mov .a3 .s11, .li .a4 0])
    (.block [.li .a7 0])

/-- If the buffer is not empty: fill it, and if more data follows, compress
it. -/
def head : Prog isa :=
  .ite (.zero .a7) (.block [])
    (.seq (fill (w := w)) (.ite (.zero .s10) (.block []) (compressBuf P)))

/-- With the buffer empty and `s10 ≥ 1` bytes left: compress all the blocks of
`data` but the last, `(s10 - 1) / B` of them, straight from `data`, leaving
`((s10 - 1) mod B) + 1` bytes (and the buffer empty again). -/
def direct : Prog isa :=
  .seq (.block [.addi .t1 .s10 (-1), .shift .srl .d .t2 .t1 (lbb w)])
    (.ite (.zero .t2) (.block [])
      (.seq (compressWith P [mov .a1 .s9, mov .a2 .t2, .addi .a3 .s11 (B w : Nat), .li .a4 0])
        (.block [.addi .t1 .s10 (-1), .logicImm .and .t1 .t1 (B w - 1 : Nat), .addi .t1 .t1 1,
          .sub .t2 .s10 .t1, .add .s9 .s9 .t2, .add .s11 .s11 .t2, mov .s10 .t1, .li .a7 0])))

/-- Copy the last `s10` (1 to `B`) bytes of `data` to the (empty) buffer. -/
def tail : Prog isa :=
  .seq (.block [mov .t3 .s10, .add .s11 .s11 .s10, .li .s10 0]) (copyLoop (w := w))

/-- The rest of `data`, if any, after `head`. -/
def rest : Prog isa :=
  .ite (.zero .s10) (.block []) (.seq (direct P) (tail (w := w)))

/-- `update_scratch`, with the scratch space in `sc`. -/
def updateMain (sc : Reg) : Prog isa :=
  .seq (.block (save sc ++ [mov .s7 .a0, mov .s8 .t0, mov .s9 .a2, mov .s10 .a3, mov .s11 .a1]))
    (.seq (bufLen (w := w))
      (.seq (.ite (.zero .s10) (.block []) (.seq (head P) (rest P))) (.block restore)))

def updateScratch : Prog isa := updateMain P .a4

def update : Prog isa :=
  .frame (.alloc frameBytes) (.seq (.block [.addSp .a4 0]) (updateMain P .a4)) (.free frameBytes)

/-! ## `finalize` -/

/-- The loop zeroing the buffer from byte `a7` on, `t3 ≥ 1` bytes (`t1 = 0`). -/
def zeroLoop : Prog isa :=
  .loop (.block [.add .t2 .s7 .a7, .store .b .t1 .t2 (N w), .addi .a7 .a7 1,
    .addi .t3 .t3 (-1)]) (.nonzero .t3)

/-- Zero the rest of the buffer. -/
def pad : Prog isa :=
  .seq (.block [.li .t1 0, .li .t3 (B w : Nat), .sub .t3 .t3 .a7])
    (.ite (.zero .t3) (.block []) (zeroLoop (w := w)))

/-- Compress the buffer as the last block: its counter is the byte count. -/
def compressLast : Prog isa :=
  compressWith P [.addi .a1 .s7 (N w : Nat), .li .a2 1, mov .a3 .s11, .li .a4 1]

/-- Copy the hash value (at `s7`) to `out` (at `s9`), a byte at a time. -/
def output : List Instr :=
  (List.range (N w)).flatMap fun k => [.load .b .t1 .s7 k, .store .b .t1 .s9 k]

/-- `finalize_scratch`, with the scratch space in `sc`. -/
def finalizeMain (sc : Reg) : Prog isa :=
  .seq (.block (save sc ++ [mov .s7 .a0, mov .s8 .t0, mov .s9 .a2, mov .s11 .a1]))
    (.seq (bufLen (w := w)) (.seq (pad (w := w)) (.seq (compressLast P)
      (.block (output (w := w) ++ restore)))))

def finalizeScratch : Prog isa := finalizeMain P .a3

def finalize : Prog isa :=
  .frame (.alloc frameBytes) (.seq (.block [.addSp .a3 0]) (finalizeMain P .a3)) (.free frameBytes)

/-! ## `init`

A leaf: uses only `a0`–`a3`, `t1`–`t3` and `t6`. -/

/-- `h := IV`, with the parameter block `0x0101kknn` XORed into `h[0]`
(`kk` = `keylen` in `a3`, `nn` = `outlen` in `a1`). -/
def initState : List Instr :=
  (List.finRange 7).flatMap (fun i =>
    movImm w .t1 ((P.IV[i.1 + 1]'(by omega)).setWidth 64) ++
      stLE w .t1 .t2 .t3 .a0 (ws w * (i.1 + 1))) ++
  movImm w .t1 ((P.IV[0] ^^^ 0x01010000).setWidth 64) ++
  ([.shift .sll .d .t2 .a3 8, .logic .xor .t1 .t1 .t2, .logic .xor .t1 .t1 .a1] : List Instr) ++
  stLE w .t1 .t2 .t3 .a0 0

/-- Zero the buffer and copy the `a3 ≥ 1` bytes of the key (at `a2`) to it. -/
def keyBlock : Prog isa :=
  .seq (.block (.li .t1 0 :: ((List.range (B w)).map fun j => .store .b .t1 .a0 (N w + j)) ++
      ([.addi .t2 .a0 (N w : Nat)] : List Instr)))
    (.loop (.block [.load .b .t1 .a2 0, .store .b .t1 .t2 0, .addi .a2 .a2 1, .addi .t2 .t2 1,
      .addi .a3 .a3 (-1)]) (.nonzero .a3))

def init : Prog isa :=
  .seq (.block (initState P)) (.ite (.zero .a3) (.block []) (keyBlock (w := w)))

end

end VG.Impl.Blake2.RISCV64.Stream
