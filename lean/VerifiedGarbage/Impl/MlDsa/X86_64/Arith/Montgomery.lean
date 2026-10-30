module

public import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Lazy

/-! # Montgomery-scaled AVX2 products for ML-DSA -/

@[expose] public section

namespace VG.Impl.MlDsa.X86_64.Arith

open VG.X86_64
open VG.Impl.MlKem.X86_64 (xb xmov yconst rcxLoop toY)

/-- Four products scaled by `2⁻³²`, reduced into `[0,q)`. -/
def montMulCore : List Instr :=
  ([.xop (.pshufd .xmm12 .xmm13 0xF5)] : List Instr) ++ vmont .xmm3 .xmm13 .xmm12 .xmm2 .xmm4 ++ vcsub .xmm3 .xmm2

/-- Add four Montgomery-scaled products to ordinary reduced coefficients. -/
def montMulAddCore : List Instr := montMulCore ++ [xb .paddd .xmm3 .xmm5] ++ vcsub .xmm3 .xmm2

def montMulAvx2 : Prog isa := ymulFn montMulCore
def montMulAddAvx2 : Prog isa := ymulFn montMulAddCore

/-- The butterflies of Algorithm 42 without reductions: `xmm0 ← xmm0 + xmm1`
and `xmm3 ← ζ · (xmm1 - xmm0 + 128q)`, with `128q` in the doublewords of
`xmm11`. A coefficient below `b q` (`b ≤ 128`) stays nonnegative and below
`2^32` in both, the sum below `2 b q` and the product below `2q`. -/
def vibflyLazy : List Instr :=
  [xmov .xmm3 .xmm1, xb .psubd .xmm3 .xmm0, xb .paddd .xmm3 .xmm11, xb .paddd .xmm0 .xmm1] ++
    vmont .xmm3 .xmm13 .xmm12 .xmm2 .xmm4

/-- `vibflyLazy` on `a` and `b`, with the difference to `o` and a zeta
`ζ · 2³² mod q` in every doubleword of `z` (which is then its own odd
doublewords): `a ← a + b` and `o ← ζ · (b - a + 128q)`. -/
def ibfR (a b o z : XReg) : List Instr :=
  [xmov o b, xb .psubd o a, xb .paddd o .xmm11, xb .paddd a b] ++ vmont o z z .xmm2 .xmm4

/-- The layers with `len = 64` and `len = 128` and the multiplication by
`R/256` on the coefficients `j`, `j + 64`, `j + 128` and `j + 192` in `xmm0`,
`xmm1`, `xmm5` and `xmm6`, with the zetas `3` and `2` in `xmm7` and `xmm8`,
zeta `1` times `R/256` in `xmm9` and `R/256` in `xmm10`: the results, reduced,
in `xmm0`, `xmm3`, `xmm6` and `xmm5`. -/
def lastCore : List Instr :=
  ibfR .xmm0 .xmm1 .xmm3 .xmm7 ++ ibfR .xmm5 .xmm6 .xmm1 .xmm8 ++ ibfR .xmm0 .xmm5 .xmm6 .xmm9 ++
    ibfR .xmm3 .xmm1 .xmm5 .xmm9 ++ vmont .xmm0 .xmm10 .xmm10 .xmm2 .xmm4 ++ vcsub .xmm0 .xmm2 ++
    vmont .xmm3 .xmm10 .xmm10 .xmm2 .xmm4 ++ vcsub .xmm3 .xmm2 ++ vcsub .xmm6 .xmm2 ++ vcsub .xmm5 .xmm2

/-- The loads of `ylast`'s eight coefficients `j`, `j + 64`, `j + 128` and `j + 192`. -/
def lastLoads : List Instr :=
  [.vmovdquLoad .l256 .xmm0 (at_ .rdx 0), .vmovdquLoad .l256 .xmm1 (at_ .rdx 256),
    .vmovdquLoad .l256 .xmm5 (at_ .rdx 512), .vmovdquLoad .l256 .xmm6 (at_ .rdx 768)]

/-- The stores of `ylast`'s results, and the next eight coefficients. -/
def lastStores : List Instr :=
  [.vmovdquStore .l256 (at_ .rdx 0) .xmm0, .vmovdquStore .l256 (at_ .rdx 256) .xmm3,
    .vmovdquStore .l256 (at_ .rdx 512) .xmm6, .vmovdquStore .l256 (at_ .rdx 768) .xmm5, .alu .add .rdx (.imm 32)]

/-- The last two layers of `NTT⁻¹` and the multiplication by `R/256`, in one
pass: `lastCore` in each lane, eight times, with the zetas as immediates. -/
def ylast : Prog isa :=
  .seq (.block (([.mov .rdx (.reg .rdi)] : List Instr) ++ yconst .xmm7 7861508 ++ yconst .xmm8 5771523 ++
      yconst .xmm9 4404704 ++ yconst .xmm10 41978))
    (rcxLoop 8 (lastLoads ++ toY lastCore ++ lastStores))

/-- `NTT⁻¹` with Montgomery scaling: the eight layers with `vibflyLazy`, whose
coefficients stay below `256 q < 2^32`, the last two of them with the
reducing multiplication by `R/256`, which accepts any doubleword (`ylast`). -/
def montNttInvAvx2 : Prog isa := VG.Impl.MlKem.X86_64.withMxcsr .rsi 768 <|
  .seq (.block ypro) (.seq (.block (yconst .xmm11 1072693376)) (.seq (ylay1 vibflyLazy 248 yzeta8R (-32))
    (.seq (ylay2 vibflyLazy 124 0x5F 0x0A (-16)) (.seq (ylay4 vibflyLazy 62 0x55 0x00 (-8))
      (.seq (ylay vibflyLazy 8 31 (-4)) (.seq (ylay vibflyLazy 16 15 (-4)) (.seq (ylay vibflyLazy 32 7 (-4))
        (.seq ylast (.block yepi)))))))))

/-- AVX2 arithmetic with lazy forward NTT, scaled products and a compensating inverse NTT. -/
def Backend.avx2Combined : Backend :=
  { Backend.avx2 with
    ntt := lazyNtt
    invNtt := montNttInvAvx2
    mul := montMulAvx2
    mulAdd := montMulAddAvx2
    montgomery := true }

end VG.Impl.MlDsa.X86_64.Arith
