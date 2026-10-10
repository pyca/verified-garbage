import VerifiedGarbage.Impl.Blake2.X86_64
import VerifiedGarbage.Impl.Argon2.X86_64.CompressAvx2

/-!
# BLAKE2b compression function on x86-64 with AVX2

`vg_blake2b_compress_avx2(state = rdi, blocks = rsi, n = rdx, t = rcx, last = r8, scratch = r9)`,
with the contract of `vg_blake2b_compress`, for CPUs with AVX and AVX2. It
does not use `scratch`.

* The work vector `v[0..15]` is four rows of four words in `ymm0`–`ymm3`:
  quadword `q` of `ymm k` is `v[4k + q]`. One `G` on the four quadwords of
  the registers at once is the four column `G`s of a round. After the
  quadwords of `ymm0`, `ymm2` and `ymm3` are rotated by three, one and two
  places (`vpermq`), quadword `q` holds the words of the diagonal `G`
  number `(q + 3) mod 4`, and one `G` on the registers is the four diagonal
  ones; the rows are then rotated back. `ymm1` (the second row, which each
  `G` computes last) stays in place, so that no permutation waits for it.
  The rotations are those of Argon2's `GB`, whose masks this code shares
  (`Impl/Argon2/X86_64/CompressAvx2.lean`): by 32 with `vpshufd`, by 24
  and 16 with `vpshufb` and the masks in `ymm14` and `ymm15`, and by 63
  with a shift, an addition and `vpxor`, with `ymm4`. Each `G` adds its
  message words to `a` before `b`, which is computed last.
* The message words a `G` adds, one per quadword, are gathered into `ymm5`
  from the block in memory: word `j` of the block is quadword `q` of a
  `vbroadcasti128` of the 16 bytes at word `j - q mod 2` (both 128-bit
  lanes hold the same two words), and `vpblendd` merges the four loads
  (through `ymm6`–`ymm8`). Word 0 in an odd quadword and word 15 in an
  even one would need bytes outside the block: they come from the load of
  words 0–1 or 14–15 with its two quadwords swapped (`vpshufd`).
* `ymm11` and `ymm12` hold the IV. The offset counter is in `rcx` (its low
  word) and `rax` (its high word) and the final block flag in `r8` (all one
  bits or zero); the fourth row starts as `IV[4..7]` XOR (`t₀`, `t₁`, `f`,
  0), built in `ymm13`.

Every address is `rdi` or `rsi` plus a constant, and the only branches are
on `last` and on the count of blocks, so only the pointers, `n`, `t` and
`last` can affect timing. Of the general-purpose registers, only `rax`,
`rcx`, `rdx`, `rsi` and `r8` are written; `vzeroupper` ends the function.
-/

namespace VG.Impl.Blake2.X86_64.Avx2

open VG.X86_64
open VG.Impl.Blake2.X86_64 (at_)

/-- `op dst, a, b` on 256 bits. -/
def v (op : VBinOp) (d a b : XReg) : Instr := .vop (.vbin op .l256 d a b)

/-! ## The message words -/

/-- The `G` of its kind (column or diagonal) that quadword `q` computes:
column `q`, or diagonal `(q + 3) mod 4`. -/
def lane (k q : Nat) : Nat := if k < 2 then q else (q + 3) % 4

/-- The word of the block that quadword `q` of message vector `k` of round
`r` holds: vectors 0 and 1 are the `x` and `y` of the column `G`s, 2 and 3
those of the diagonal ones, `SIGMA[r mod 10][8 (k / 2) + 2 i + k mod 2]` for
`G` number `i` of the kind. -/
def msgWord (r k q : Nat) : Nat :=
  (Spec.Blake2.sigmaAt r (8 * (k / 2) + 2 * lane k q + k % 2)).val

/-- The word at which `vbroadcasti128` loads 16 bytes to put word `j` in
quadword `q`, and whether the two quadwords are then swapped. -/
def src (j q : Nat) : Nat × Bool :=
  if q % 2 = 1 ∧ j = 0 then (0, true)
  else if q % 2 = 0 ∧ j = 15 then (14, true)
  else (j - q % 2, false)

/-- Load into `d` the words that put word `j` in quadword `q`. -/
def bcast (d : XReg) (j q : Nat) : List Instr :=
  .vbroadcasti128 d (at_ .rsi (8 * (src j q).1)) ::
    if (src j q).2 then [.vop (.vpshufd .l256 d d 0x4e)] else []

/-- Message vector `k` of round `r`, into `ymm5`. -/
def msg (r k : Nat) : List Instr :=
  bcast .xmm5 (msgWord r k 0) 0 ++ bcast .xmm6 (msgWord r k 1) 1 ++
    ([.vop (.vpblendd .l256 .xmm5 .xmm5 .xmm6 0x0c)] : List Instr) ++
    bcast .xmm7 (msgWord r k 2) 2 ++ bcast .xmm8 (msgWord r k 3) 3 ++
    ([.vop (.vpblendd .l256 .xmm7 .xmm7 .xmm8 0xc0),
      .vop (.vpblendd .l256 .xmm5 .xmm5 .xmm7 0xf0)] : List Instr)

/-! ## The rounds -/

/-- The first half of `G` on each quadword, with the message words in `ymm5`:
`a += b + x; d = (d ^ a) >>> 32; c += d; b = (b ^ c) >>> 24`. -/
def half1 : List Instr :=
  [v .vpaddq .xmm0 .xmm0 .xmm5, v .vpaddq .xmm0 .xmm0 .xmm1] ++
    Argon2.X86_64.Avx2.xorRot32 .xmm3 .xmm0 ++ [v .vpaddq .xmm2 .xmm2 .xmm3] ++
    Argon2.X86_64.Avx2.xorRot24 .xmm1 .xmm2

/-- The second half: `a += b + y; d = (d ^ a) >>> 16; c += d; b = (b ^ c) >>> 63`. -/
def half2 : List Instr :=
  [v .vpaddq .xmm0 .xmm0 .xmm5, v .vpaddq .xmm0 .xmm0 .xmm1] ++
    Argon2.X86_64.Avx2.xorRot16 .xmm3 .xmm0 ++ [v .vpaddq .xmm2 .xmm2 .xmm3] ++
    Argon2.X86_64.Avx2.xorRot63 .xmm1 .xmm2

/-- Rotate the quadwords of `ymm0`, `ymm2` and `ymm3` by three, one and two
places, so that the diagonals are columns. -/
def diagonalize : List Instr :=
  [.vop (.vpermq .xmm0 .xmm0 0x93), .vop (.vpermq .xmm2 .xmm2 0x39),
    .vop (.vpermq .xmm3 .xmm3 0x4e)]

/-- Rotate them back. -/
def undiagonalize : List Instr :=
  [.vop (.vpermq .xmm0 .xmm0 0x39), .vop (.vpermq .xmm2 .xmm2 0x93),
    .vop (.vpermq .xmm3 .xmm3 0x4e)]

/-- Round `r` (RFC 7693 §3.2). -/
def round (r : Nat) : Prog isa :=
  .seq (.block (msg r 0)) <| .seq (.block half1) <| .seq (.block (msg r 1)) <|
  .seq (.block (half2 ++ diagonalize)) <|
  .seq (.block (msg r 2)) <| .seq (.block half1) <| .seq (.block (msg r 3)) <|
  .block (half2 ++ undiagonalize)

/-- Rounds `0 … n-1`. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (round n)

/-! ## One block -/

/-- The work vector (RFC 7693 §3.2): the state, the IV, and the counter and
the flag XORed into the fourth row. -/
def init : List Instr :=
  [.vmovdquLoad .l256 .xmm0 (at_ .rdi 0), .vmovdquLoad .l256 .xmm1 (at_ .rdi 32),
    .vop (.vmovdqa .l256 .xmm2 .xmm11),
    .vop (.vmovq .xmm13 .rcx), .vop (.vmovq .xmm4 .rax),
    .vop (.vbin .vpunpcklqdq .l128 .xmm13 .xmm13 .xmm4), .vop (.vmovq .xmm4 .r8),
    .vop (.vinserti128 .xmm13 .xmm13 .xmm4 1), v .vpxor .xmm3 .xmm12 .xmm13]

/-- `h[i] := h[i] ^ v[i] ^ v[i + 8]`. -/
def finish : List Instr :=
  [v .vpxor .xmm0 .xmm0 .xmm2, v .vpxor .xmm1 .xmm1 .xmm3,
    .vmovdquLoad .l256 .xmm4 (at_ .rdi 0), v .vpxor .xmm0 .xmm0 .xmm4,
    .vmovdquStore .l256 (at_ .rdi 0) .xmm0,
    .vmovdquLoad .l256 .xmm4 (at_ .rdi 32), v .vpxor .xmm1 .xmm1 .xmm4,
    .vmovdquStore .l256 (at_ .rdi 32) .xmm1]

/-- The next block, its offset counter (128 bits, in `rcx` and `rax`), and
the count of blocks left (setting ZF when it hits 0). -/
def advance : List Instr :=
  [.alu .add .rsi (.imm 128), .alu .add .rcx (.imm 128), .alu .adc .rax (.imm 0),
    .alu .sub .rdx (.imm 1)]

def body : Prog isa :=
  .seq (.block init) (.seq (rounds 12) (.block (finish ++ advance)))

/-! ## The whole function -/

/-- `d := (lo, hi)` in its low 128 bits, through `rax` and `t`. -/
def pair (d t : XReg) (lo hi : BitVec 64) : List Instr :=
  [.movImm64 .rax lo, .vop (.vmovq d .rax), .movImm64 .rax hi, .vop (.vmovq t .rax),
    .vop (.vbin .vpunpcklqdq .l128 d d t)]

/-- `d := (a, b, c, e)`, through `ymm10` and `ymm13`. -/
def quad (d : XReg) (a b c e : BitVec 64) : List Instr :=
  pair d .xmm13 a b ++ pair .xmm10 .xmm13 c e ++ ([.vop (.vinserti128 d d .xmm10 1)] : List Instr)

/-- `last` as a 32-bit value (whose upper half is unspecified; first, so
that the constant-time analysis knows it is public), the masks and the IV,
the high word of the counter (0), and `last` tested. -/
def setup : List Instr :=
  ([.mov32 .r8 (.reg .r8)] : List Instr) ++ Argon2.X86_64.Avx2.masks ++
    quad .xmm11 Spec.Blake2.b.IV[0] Spec.Blake2.b.IV[1] Spec.Blake2.b.IV[2] Spec.Blake2.b.IV[3] ++
    quad .xmm12 Spec.Blake2.b.IV[4] Spec.Blake2.b.IV[5] Spec.Blake2.b.IV[6] Spec.Blake2.b.IV[7] ++
    ([.mov32 .rax (.imm 0), .alu .test .r8 (.reg .r8)] : List Instr)

/-- The final block flag in `r8`: all one bits if `last ≠ 0`; then test `n`. -/
def flag : Prog isa :=
  .seq (.ite .e (.block []) (.block [.mov .r8 (.imm 0xffffffff)]))
    (.block [.alu .test .rdx (.reg .rdx)])

def compress : Prog isa :=
  .seq (.block setup) (.seq flag
    (.seq (.ite .e (.block []) (.loop body .ne)) (.block [.vop .vzeroupper])))

end VG.Impl.Blake2.X86_64.Avx2
