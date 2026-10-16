module

public import VerifiedGarbage.Impl.MlKem.X86_64.NttAvx2
public import VerifiedGarbage.Impl.MlKem.X86_64.MulAvx2
public import VerifiedGarbage.Impl.MlKem.X86_64.Arith

/-!
# ML-KEM on x86-64: sums of products in words, with AVX2

The pieces of `Bodies.avx2` (`KpkeMul.lean`) that keep a sum of products
`ŝ[j] ×_T ŷ[j]` as 256 words (an *accumulator*) rather than as 256 `u32`s:
the products of `vg_mlkem_multiply_ntts_avx2` (`MulAvx2.lean`) are added to
it where `vbase` leaves them, and `NTT⁻¹` starts from it rather than from
the `u32`s it would pack.

`vbase` leaves the products of the 32 coefficients of an iteration `i` in
two registers, in an order of their own: word `e` of lane `l` of `ymm1`
holds coefficient `2 p` and that of `ymm2` coefficient `2 p + 1`, for the
pair `p = 16i + 4⌊e/2⌋ + (e mod 2) + 2l`. The accumulator keeps them in
that order: `ymm1` at byte `64 i` and `ymm2` at `64 i + 32`
(`accIdx`).

* `zeroAccY(acc = rdi)`: the accumulator of the zero polynomial.
* `tabAccY(scratch = rcx)`: the `γ`s of `vg_mlkem_multiply_ntts_avx2`
  (`gTabY`) at `scratch + 3328`, once for all the products.
* `mulAccY(acc = rdi, f = rsi, g = rdx, scratch = rcx)`: `acc += f ×_T g`,
  8 times on 32 coefficients: `vg_mlkem_multiply_ntts_avx2`'s loads and
  `vbase`, with the table at `scratch + 3328`, then each of `ymm1` and
  `ymm2` added to its 32 bytes of the accumulator, reduced (`vcsub`).
* `mulSetY(acc = rdi, f = rsi, g = rdx, scratch = rcx)`: `acc = f ×_T g`:
  `mulAccY`, but storing `ymm1` and `ymm2` as they are.
* `finAccY(f = rdi, acc = rsi)`: `f += acc`, to the `u32`s at `f`, 32
  coefficients at a time: `vpunpcklwd` and `vpunpckhwd` of the
  accumulator's two registers put coefficients `4l + {0, …, 3}` and
  `8 + 4l + {0, …, 3}` (and those sixteen higher) in lane `l` (as in
  `yfromAcc`), and `vpunpcklwd` and `vpunpckhwd` of each with zero extend
  them to eight `u32`s in order, which `vg_mlkem_add_avx2`'s arithmetic adds
  to those of `f`.
* `nttInvAccY(acc = rdi, scratch = rsi)`: `vg_mlkem_inv_ntt_avx2` on the
  accumulator, to the `u32`s at `rdi`, with the prologue putting the
  accumulator's words in order into `S` (`yfromAcc`) rather than packing
  them: `vpunpcklwd` and `vpunpckhwd` of the two registers of an iteration
  put coefficients `4l + {0, …, 3}` and `8 + 4l + {0, …, 3}` (and those
  sixteen higher) in lane `l`, and `vpermq` with `0xD8` puts the quadwords
  in order.

Every address and branch depends only on the pointers.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

/-- The offset of the table of `mulAccY` in `scratch`. -/
def oTabY : Nat := 3328

/-- The coefficient at word `w` of the accumulator. -/
def accIdx (w : Nat) : Nat :=
  2 * (16 * (w / 32) + 4 * (w % 8 / 2) + w % 2 + 2 * (w % 16 / 8)) + w % 32 / 16

def zeroAccY : Prog isa :=
  .block (yb .vpxor .xmm0 .xmm0 .xmm0 ::
    (List.range 16).map fun i => .vmovdquStore .l256 (at_ .rdi (32 * i)) .xmm0)

def tabAccY : List Instr := leaR .r10 .rcx oTabY ++ wordTab gTabY 128 .r10 0

/-- The 32 bytes at `[rdi + off]` plus the words of `h`, reduced, and stored back. -/
def accStore (h : XReg) (off : Nat) : List Instr :=
  [.vmovdquLoad .l256 .xmm5 (at_ .rdi off)] ++ toY (xb .paddw h .xmm5 :: vcsub h .xmm3) ++
    [.vmovdquStore .l256 (at_ .rdi off) h]

/-- The products of 32 coefficients of `rsi` and `rdx`, to `ymm1` and `ymm2`
(`vbase`'s order). -/
def mulProdY : List Instr :=
  yload4 .rsi .xmm0 .xmm1 .xmm2 .xmm3 ++ toY (deintS .xmm0 .xmm1 .xmm2 .xmm3 .xmm4 .xmm5) ++
    yload4 .rdx .xmm6 .xmm7 .xmm8 .xmm9 ++ toY (deintS .xmm6 .xmm7 .xmm8 .xmm9 .xmm10 .xmm11) ++
    [.vmovdquLoad .l256 .xmm13 (at_ .r8 0)] ++ toY vbase

/-- The pointers to the next 32 coefficients. -/
def mulNextY : List Instr :=
  [.alu .add .rsi (.imm 128), .alu .add .rdx (.imm 128), .alu .add .rdi (.imm 64), .alu .add .r8 (.imm 32)]

def mulAccBodyY : List Instr := mulProdY ++ accStore .xmm1 0 ++ accStore .xmm2 32 ++ mulNextY

def mulSetBodyY : List Instr :=
  mulProdY ++ [.vmovdquStore .l256 (at_ .rdi 0) .xmm1, .vmovdquStore .l256 (at_ .rdi 32) .xmm2] ++ mulNextY

/-- The constants, and `r8` at the table. -/
def mulAccProY : List Instr := yconsts ++ yconst .xmm12 0x05490549 ++ leaR .r8 .rcx oTabY

def mulAccY : Prog isa := .seq (.block mulAccProY) (rcxLoop 8 mulAccBodyY)

def mulSetY : Prog isa := .seq (.block mulAccProY) (rcxLoop 8 mulSetBodyY)

/-- The accumulator at `[r9]` in order to the words at `[rdx]`, 32 at a time. -/
def yfromAcc : Prog isa :=
  rcxLoop 8 [.vmovdquLoad .l256 .xmm0 (at_ .r9 0), .vmovdquLoad .l256 .xmm1 (at_ .r9 32),
    yb .vpunpckhwd .xmm2 .xmm0 .xmm1, yb .vpunpcklwd .xmm0 .xmm0 .xmm1, .vop (.vpermq .xmm0 .xmm0 0xD8),
    .vop (.vpermq .xmm2 .xmm2 0xD8), .vmovdquStore .l256 (at_ .rdx 0) .xmm0,
    .vmovdquStore .l256 (at_ .rdx 32) .xmm2, .alu .add .r9 (.imm 64), .alu .add .rdx (.imm 64)]

/-- `ypro`, but for the accumulator at `rdi`. -/
def yproAcc (tab : Nat → Nat) : Prog isa :=
  .seq (.block (wordTab tab 128 .rsi 0 ++ yconsts ++ [.mov .r9 (.reg .rdi)] ++ leaR .rdx .rsi oS)) yfromAcc

def nttInvAccY : Prog isa := .seq (yproAcc zmTabInv) (.seq nttInvLazy yepi)

/-- Eight coefficients of the sum, from the words of `w` (`op` with `ymm14`,
zero) and the `u32`s at `[rdi + off]`, to `[rdi + off]`: the arithmetic of
`vg_mlkem_add_avx2` (`addArith`). -/
def finQ (w : XReg) (op : VBinOp) (off : Nat) : List Instr :=
  [.vmovdquLoad .l256 .xmm0 (at_ .rdi off), yb op .xmm1 w .xmm14] ++ toY addArith ++
    [.vmovdquStore .l256 (at_ .rdi off) .xmm0]

def finAccBodyY : List Instr :=
  [.vmovdquLoad .l256 .xmm8 (at_ .rsi 0), .vmovdquLoad .l256 .xmm9 (at_ .rsi 32),
    yb .vpunpcklwd .xmm10 .xmm8 .xmm9, yb .vpunpckhwd .xmm11 .xmm8 .xmm9] ++
    finQ .xmm10 .vpunpcklwd 0 ++ finQ .xmm10 .vpunpckhwd 32 ++ finQ .xmm11 .vpunpcklwd 64 ++
    finQ .xmm11 .vpunpckhwd 96 ++ [.alu .add .rsi (.imm 64), .alu .add .rdi (.imm 128)]

def finAccY : Prog isa :=
  .seq (.block (yconst .xmm15 3329 ++ [yb .vpxor .xmm14 .xmm14 .xmm14]))
    (.seq (rcxLoop 8 finAccBodyY) (.block [.vop .vzeroupper]))

end VG.Impl.MlKem.X86_64
