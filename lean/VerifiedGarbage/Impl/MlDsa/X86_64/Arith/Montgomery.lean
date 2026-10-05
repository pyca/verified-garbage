import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Avx2

/-! # Montgomery-scaled AVX2 products for ML-DSA -/

namespace VG.Impl.MlDsa.X86_64.Arith

open VG.X86_64
open VG.Impl.MlKem.X86_64 (xb yconst rcxLoop toY)

/-- Four products scaled by `2⁻³²`, reduced into `[0,q)`. -/
def montMulCore : List Instr :=
  [.xop (.pshufd .xmm12 .xmm13 0xF5)] ++ vmont .xmm3 .xmm13 .xmm12 .xmm2 .xmm4 ++ vcsub .xmm3 .xmm2

/-- Add four Montgomery-scaled products to ordinary reduced coefficients. -/
def montMulAddCore : List Instr := montMulCore ++ [xb .paddd .xmm3 .xmm5] ++ vcsub .xmm3 .xmm2

def montMulAvx2 : Prog isa := ymulFn montMulCore
def montMulAddAvx2 : Prog isa := ymulFn montMulAddCore

def montScale : Prog isa :=
  .seq (.block ([.mov .rdx (.reg .rdi)] ++ yconst .xmm13 41978 ++ [.vop (.vmovdqa .l256 .xmm12 .xmm13)]))
    (rcxLoop 32 ([.vmovdquLoad .l256 .xmm3 (at_ .rdx 0)] ++ toY (vmont .xmm3 .xmm13 .xmm12 .xmm2 .xmm4 ++
      vcsub .xmm3 .xmm2) ++ [.vmovdquStore .l256 (at_ .rdx 0) .xmm3, .alu .add .rdx (.imm 32)]))

def montNttInvAvx2 : Prog isa := VG.Impl.MlKem.X86_64.withMxcsr .rsi 768 <|
  .seq (.block ypro) (.seq (ylay1 vibfly 248 yzeta8R (-32)) (.seq (ylay2 vibfly 124 0x5F 0x0A (-16))
    (.seq (ylay4 vibfly 62 0x55 0x00 (-8)) (.seq (ylay vibfly 8 31 (-4)) (.seq (ylay vibfly 16 15 (-4))
      (.seq (ylay vibfly 32 7 (-4)) (.seq (ylay vibfly 64 3 (-4)) (.seq (ylay vibfly 128 1 (-4))
        (.seq montScale (.block yepi))))))))))


end VG.Impl.MlDsa.X86_64.Arith
