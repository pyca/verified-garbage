module

public import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Avx2

/-! Forward AVX2 NTT with a single canonical reduction after all eight layers. -/

@[expose] public section

namespace VG.Impl.MlDsa.X86_64.Arith
open VG.X86_64
open VG.Impl.MlKem.X86_64 (xb xmov withMxcsr rcxLoop toY yconst)

-- Forward NTT keeps coefficients nonnegative and below 17q. vmont accepts
-- arbitrary uint32 coefficients when its twiddle is below q.
def lazyBfly : List Instr :=
  vmont .xmm1 .xmm13 .xmm12 .xmm2 .xmm4 ++
  [xmov .xmm3 .xmm0, xb .paddd .xmm0 .xmm1,
   xb .paddd .xmm3 .xmm11, xb .psubd .xmm3 .xmm1]

-- q = 2^23 - 2^13 + 1. For x < 17q, removing (x >> 23)*q leaves < 2q.
def reduceLazy : List Instr := [xmov .xmm1 .xmm0, .xop (.shift .psrld .xmm1 23),
  xmov .xmm2 .xmm1, .xop (.shift .pslld .xmm2 23), xb .psubd .xmm0 .xmm2,
  xmov .xmm2 .xmm1, .xop (.shift .pslld .xmm2 13), xb .paddd .xmm0 .xmm2,
  xb .psubd .xmm0 .xmm1] ++ vcsub .xmm0 .xmm2

/-- `[rdi + 8 rax + d]`: with `rax = 8m`, the coefficients `16m + d / 4` on. -/
def fcoef (d : Nat) : MemOp := { base := .rdi, index := some .rax, scale := 8, disp := d }

/-- `[rsi + sc rax + d]`: with `rax = 8m`, the zetas of the table from
`(d + 8 sc m) / 4`. -/
def fzeta (sc d : Nat) : MemOp := { base := .rsi, index := some .rax, scale := sc, disp := d }

/-- `yzetaS o₀ o₁`, with the four zetas at `m`. -/
def yzetaSm (m : MemOp) (o₀ o₁ : BitVec 8) : List Instr :=
  .vbroadcasti128 .xmm13 m ::
    toY ([.xop (.pshufd .xmm2 .xmm13 o₁), .xop (.pshufd .xmm13 .xmm13 o₀)] : List Instr) ++
    ([.vop (.vpblendd .l256 .xmm13 .xmm13 .xmm2 0xF0)] : List Instr) ++ toY [.xop (.pshufd .xmm12 .xmm13 0xF5)]

/-- `yzeta8`, with the eight zetas at `m`. -/
def yzeta8m (m : MemOp) : List Instr :=
  ([.vmovdquLoad .l256 .xmm13 m, .vop (.vpermq .xmm13 .xmm13 0xD8)] : List Instr) ++
    toY [.xop (.pshufd .xmm12 .xmm13 0xF5)]

/-- The layers with `len = 4, 2, 1` and the reduction, on the sixteen
coefficients `16m, …, 16m + 15` (with `rax = 8m`) in registers: loaded once,
the layer with `len = 4` as `ylay4` does it (its two blocks gathered by
`vperm2i128`, and back into `ymm0` and `ymm1` in order), then those with
`len = 2` and `len = 1` as `ylay2` and `ylay1` do (their zetas at the same
places of the table, through `rax`), then `reduceLazy` of each eight, and
stored once. -/
def fusedBody : List Instr :=
  ([.vmovdquLoad .l256 .xmm4 (fcoef 0), .vmovdquLoad .l256 .xmm5 (fcoef 32)] : List Instr) ++
    yzetaSm (fzeta 1 128) 0x00 0x55 ++
    ([.vop (.vperm2i128 .xmm0 .xmm4 .xmm5 0x20), .vop (.vperm2i128 .xmm1 .xmm4 .xmm5 0x31)] : List Instr) ++
    toY lazyBfly ++
    ([.vop (.vperm2i128 .xmm1 .xmm0 .xmm3 0x31), .vop (.vperm2i128 .xmm0 .xmm0 .xmm3 0x20)] : List Instr) ++
    yzetaSm (fzeta 2 256) 0xA0 0xF5 ++ toY (gath2 ++ lazyBfly ++ scat2) ++
    ([.vop (.vmovdqa .l256 .xmm2 .xmm1)] : List Instr) ++ yzeta8m (fzeta 4 512) ++ toY (gath1 ++ lazyBfly ++ scat1) ++
    ([.vop (.vmovdqa .l256 .xmm5 .xmm1)] : List Instr) ++ toY reduceLazy ++
    ([.vmovdquStore .l256 (fcoef 0) .xmm0, .vop (.vmovdqa .l256 .xmm0 .xmm5)] : List Instr) ++ toY reduceLazy ++
    ([.vmovdquStore .l256 (fcoef 32) .xmm0, .alu .add .rax (.imm 8)] : List Instr)

/-- The last three layers and the reduction, sixteen coefficients at a time. -/
def fusedLast : Prog isa := .seq (.block [.mov32 .rax (.imm 0)]) (rcxLoop 16 fusedBody)

def lazyNtt : Prog isa := withMxcsr .rsi 768 <|
  .seq (.block ypro) (.seq (.block (yconst .xmm11 16760834))
    (.seq (ylay lazyBfly 128 1 4) (.seq (ylay lazyBfly 64 2 4) (.seq (ylay lazyBfly 32 4 4)
      (.seq (ylay lazyBfly 16 8 4) (.seq (ylay lazyBfly 8 16 4) (.seq fusedLast (.block yepi))))))))

end VG.Impl.MlDsa.X86_64.Arith
