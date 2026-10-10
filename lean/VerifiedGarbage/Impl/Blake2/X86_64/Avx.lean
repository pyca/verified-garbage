import VerifiedGarbage.Impl.Blake2.X86_64

/-!
# BLAKE2s compression function on x86-64 with AVX

`vg_blake2s_compress_avx(state = rdi, blocks = rsi, n = rdx, t = rcx, last = r8, scratch = r9)`,
with the contract of `vg_blake2s_compress`, for CPUs with AVX. It does not
use `scratch`. Every vector instruction is `VEX.128`-encoded, and needs AVX
alone.

* The work vector `v[0..15]` is four rows of four words in `xmm0`–`xmm3`:
  doubleword `q` of `xmm k` is `v[4k + q]`. One `G` on the four doublewords
  of the registers at once is the four column `G`s of a round. After the
  doublewords of `xmm0`, `xmm2` and `xmm3` are rotated by three, one and two
  places (`vpshufd`), doubleword `q` holds the words of the diagonal `G`
  number `(q + 3) mod 4`, and one `G` on the registers is the four diagonal
  ones; the rows are then rotated back. `xmm1` (the second row, which each
  `G` computes last) stays in place, so that no shuffle waits for it.
* The rotations right by 16 and 8 are `vpshufb`s of the bytes of each
  doubleword, with the masks in `xmm14` and `xmm15`; those by 12 and 7 are
  two shifts and a `vpor`, through `xmm4`. Each `G` adds its message words
  to `a` before `b`, which is computed last.
* The message words a `G` adds, one per doubleword, are gathered into
  `xmm5` from the block in memory, a pair of them at a time: the two words
  are loaded (16 bytes each) so that each is doubleword 0 of its load
  (`vpunpckldq` interleaves them), or doubleword 2 (`vpunpckhdq`), whichever
  keeps both loads inside the block; a word at neither place (a pair of a
  word below 2 and one above 12) is broadcast with `vpshufd` from the load
  of its row instead. `vpunpcklqdq` joins the two pairs.
* `xmm11` and `xmm12` hold the IV. The offset counter is in `rcx` and the
  final block flag in `r8` (`0xffffffff` or zero); the fourth row starts as
  `IV[4..7]` XOR (`t₀`, `t₁`, `f`, 0), built in `xmm13`.

Every address is `rdi` or `rsi` plus a constant, and the only branches are
on `last` and on the count of blocks, so only the pointers, `n`, `t` and
`last` can affect timing. Of the general-purpose registers, only `rax`,
`rcx`, `rdx`, `rsi` and `r8` are written.
-/

namespace VG.Impl.Blake2.X86_64.Avx

open VG.X86_64
open VG.Impl.Blake2.X86_64 (at_)

/-- `op dst, a, b` on 128 bits. -/
def v (op : VBinOp) (d a b : XReg) : Instr := .vop (.vbin op .l128 d a b)

/-! ## The message words -/

/-- The `G` of its kind (column or diagonal) that doubleword `q` computes:
column `q`, or diagonal `(q + 3) mod 4`. -/
def lane (k q : Nat) : Nat := if k < 2 then q else (q + 3) % 4

/-- The word of the block that doubleword `q` of message vector `k` of round
`r` holds: vectors 0 and 1 are the `x` and `y` of the column `G`s, 2 and 3
those of the diagonal ones, `SIGMA[r mod 10][8 (k / 2) + 2 i + k mod 2]` for
`G` number `i` of the kind. -/
def msgWord (r k q : Nat) : Nat :=
  (Spec.Blake2.sigmaAt r (8 * (k / 2) + 2 * lane k q + k % 2)).val

/-- Whether the pair of words `j, j'` is gathered from doubleword 2 of their
loads (`vpunpckhdq`), rather than doubleword 0 (`vpunpckldq`): if a load
with one of them at doubleword 0 would end past the block, and both can be
at doubleword 2. -/
def hiPair (j j' : Nat) : Bool := !(decide (j ≤ 12) && decide (j' ≤ 12)) && decide (2 ≤ j) && decide (2 ≤ j')

/-- The doubleword a pair is gathered from. -/
def pairPos (j j' : Nat) : Nat := if hiPair j j' then 2 else 0

/-- The word at which to load 16 bytes so that word `j` is doubleword `p`,
or else (`true`) the first word of `j`'s row, to broadcast it from. -/
def src (j p : Nat) : Nat × Bool :=
  if p ≤ j ∧ j ≤ 12 + p then (j - p, false) else (4 * (j / 4), true)

/-- Load into `d` the 16 bytes that put word `j` in doubleword `p`. -/
def ldw (d : XReg) (j p : Nat) : List Instr :=
  .vmovdquLoad .l128 d (at_ .rsi (4 * (src j p).1)) ::
    if (src j p).2 then [.vop (.vpshufd .l128 d d (BitVec.ofNat 8 (0x55 * (j % 4))))] else []

/-- Words `j, j'` into doublewords 0 and 1 of `d`, through `a` and `b`. -/
def pair (d a b : XReg) (j j' : Nat) : List Instr :=
  ldw a j (pairPos j j') ++ ldw b j' (pairPos j j') ++
    [v (if hiPair j j' then .vpunpckhdq else .vpunpckldq) d a b]

/-- Message vector `k` of round `r`, into `xmm5`. -/
def msg (r k : Nat) : List Instr :=
  pair .xmm5 .xmm6 .xmm7 (msgWord r k 0) (msgWord r k 1) ++
    pair .xmm8 .xmm8 .xmm9 (msgWord r k 2) (msgWord r k 3) ++
    [v .vpunpcklqdq .xmm5 .xmm5 .xmm8]

/-! ## The rounds -/

/-- Half of `G` on each doubleword, with the message words in `xmm5` and the
`vpshufb` mask in `mask`: `a += b + x; d = (d ^ a) >>> R; c += d;
b = (b ^ c) >>> n`. -/
def half (mask : XReg) (n : Nat) : List Instr :=
  [v .vpaddd .xmm0 .xmm0 .xmm5, v .vpaddd .xmm0 .xmm0 .xmm1, v .vpxor .xmm3 .xmm3 .xmm0,
    v .vpshufb .xmm3 .xmm3 mask, v .vpaddd .xmm2 .xmm2 .xmm3, v .vpxor .xmm1 .xmm1 .xmm2,
    .vop (.vshift .psrld .l128 .xmm4 .xmm1 (BitVec.ofNat 8 n)),
    .vop (.vshift .pslld .l128 .xmm1 .xmm1 (BitVec.ofNat 8 (32 - n))), v .vpor .xmm1 .xmm1 .xmm4]

/-- The first half of `G`: `d >>> 16` (`xmm14`) and `b >>> 12`. -/
def half1 : List Instr := half .xmm14 12

/-- The second half: `d >>> 8` (`xmm15`) and `b >>> 7`. -/
def half2 : List Instr := half .xmm15 7

/-- Rotate the doublewords of `xmm0`, `xmm2` and `xmm3` by three, one and
two places, so that the diagonals are columns. -/
def diagonalize : List Instr :=
  [.vop (.vpshufd .l128 .xmm0 .xmm0 0x93), .vop (.vpshufd .l128 .xmm2 .xmm2 0x39),
    .vop (.vpshufd .l128 .xmm3 .xmm3 0x4e)]

/-- Rotate them back. -/
def undiagonalize : List Instr :=
  [.vop (.vpshufd .l128 .xmm0 .xmm0 0x39), .vop (.vpshufd .l128 .xmm2 .xmm2 0x93),
    .vop (.vpshufd .l128 .xmm3 .xmm3 0x4e)]

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
  [.vmovdquLoad .l128 .xmm0 (at_ .rdi 0), .vmovdquLoad .l128 .xmm1 (at_ .rdi 16),
    .vop (.vmovdqa .l128 .xmm2 .xmm11), .vop (.vmovq .xmm13 .rcx), .vop (.vmovq .xmm4 .r8),
    v .vpunpcklqdq .xmm13 .xmm13 .xmm4, v .vpxor .xmm3 .xmm12 .xmm13]

/-- `h[i] := h[i] ^ v[i] ^ v[i + 8]`. -/
def finish : List Instr :=
  [v .vpxor .xmm0 .xmm0 .xmm2, v .vpxor .xmm1 .xmm1 .xmm3,
    .vmovdquLoad .l128 .xmm4 (at_ .rdi 0), v .vpxor .xmm0 .xmm0 .xmm4,
    .vmovdquStore .l128 (at_ .rdi 0) .xmm0,
    .vmovdquLoad .l128 .xmm4 (at_ .rdi 16), v .vpxor .xmm1 .xmm1 .xmm4,
    .vmovdquStore .l128 (at_ .rdi 16) .xmm1]

/-- The next block, its offset counter (64 bits, in `rcx`), and the count of
blocks left (setting ZF when it hits 0). -/
def advance : List Instr :=
  [.alu .add .rsi (.imm 64), .alu .add .rcx (.imm 64), .alu .sub .rdx (.imm 1)]

def body : Prog isa :=
  .seq (.block init) (.seq (rounds 10) (.block (finish ++ advance)))

/-! ## The whole function -/

/-- `d := (lo, hi)`, through `rax` and `xmm4`. -/
def pair64 (d : XReg) (lo hi : BitVec 64) : List Instr :=
  [.movImm64 .rax lo, .vop (.vmovq d .rax), .movImm64 .rax hi, .vop (.vmovq .xmm4 .rax),
    v .vpunpcklqdq d d .xmm4]

/-- The `vpshufb` masks rotating each doubleword right by 16 and by 8, as
their low and high quadwords. -/
def rot16Lo : BitVec 64 := 0x0504070601000302
def rot16Hi : BitVec 64 := 0x0d0c0f0e09080b0a
def rotr8Lo : BitVec 64 := 0x0407060500030201
def rotr8Hi : BitVec 64 := 0x0c0f0e0d080b0a09

/-- Words `i` and `i + 1` of the IV as a quadword. -/
def ivPair (i : Nat) : BitVec 64 :=
  Spec.Blake2.s.IV.toList.getD (i + 1) 0 ++ Spec.Blake2.s.IV.toList.getD i 0

/-- `last` as a 32-bit value (whose upper half is unspecified; first, so
that the constant-time analysis knows it is public), the masks and the IV,
and `last` tested. -/
def setup : List Instr :=
  ([.mov32 .r8 (.reg .r8)] : List Instr) ++ pair64 .xmm14 rot16Lo rot16Hi ++ pair64 .xmm15 rotr8Lo rotr8Hi ++
    pair64 .xmm11 (ivPair 0) (ivPair 2) ++ pair64 .xmm12 (ivPair 4) (ivPair 6) ++
    ([.alu .test .r8 (.reg .r8)] : List Instr)

/-- The final block flag in `r8`: `0xffffffff` if `last ≠ 0`; then test `n`. -/
def flag : Prog isa :=
  .seq (.ite .e (.block []) (.block [.mov32 .r8 (.imm 0xffffffff)]))
    (.block [.alu .test .rdx (.reg .rdx)])

def compress : Prog isa :=
  .seq (.block setup) (.seq flag (.ite .e (.block []) (.loop body .ne)))

end VG.Impl.Blake2.X86_64.Avx
