import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Avx2

/-! Forward AVX2 NTT with a single canonical reduction after all eight layers. -/
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

def normalizeLazy : Prog isa :=
  .seq (.block [.mov .rdx (.reg .rdi)])
    (rcxLoop 32 ([.vmovdquLoad .l256 .xmm0 (at_ .rdx 0)] ++ toY reduceLazy ++
      [.vmovdquStore .l256 (at_ .rdx 0) .xmm0, .alu .add .rdx (.imm 32)]))

def lazyNtt : Prog isa := withMxcsr .rsi 768 <|
  .seq (.block ypro) (.seq (.block (yconst .xmm11 16760834))
    (.seq (ylay lazyBfly 128 1 4) (.seq (ylay lazyBfly 64 2 4) (.seq (ylay lazyBfly 32 4 4)
      (.seq (ylay lazyBfly 16 8 4) (.seq (ylay lazyBfly 8 16 4) (.seq (ylay4 lazyBfly 32 0x00 0x55 8)
        (.seq (ylay2 lazyBfly 64 0xA0 0xF5 16) (.seq (ylay1 lazyBfly 128 yzeta8 32)
          (.seq normalizeLazy (.block yepi)))))))))))

end VG.Impl.MlDsa.X86_64.Arith
