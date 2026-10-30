module

public import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Mul
public import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Ntt

/-!
# ML-DSA on x86-64: a row's sum of products, four coefficients at a time

`vg_mldsa_dot_inverse{c}` sums the products of the coefficients of `c` pairs
of polynomials `a[j]`, `b[j]` (each below `3 q`) in quadwords: `pmuludq`
multiplies the even doublewords of its operands, and those shifted down by
32 bits are the odd ones, so `xmm5` accumulates the products of the even
coefficients and `xmm6` those of the odd ones (`dotMac`). A sum of at most
seven products is below `63 q² < 2³² q`, so one Montgomery reduction of each
quadword (`vredc`), merged as in `vmont`, leaves the sum times `2⁻³²` below
`2 q`, which `vcsub` reduces (`dotRed`).

The SSE2 code (`dotInvSse2`), whose inverse NTT is not scaled, multiplies
each sum by `2⁶⁴ mod q` (in `xmm11`, `mulPro`) with `vmont` (`dotPlain`), which
cancels the `2⁻³²`.
-/

@[expose] public section

namespace VG.Impl.MlDsa.X86_64.Arith

open VG.X86_64
open VG.Impl.MlKem.X86_64 (xb xmov withMxcsr rcxLoop)

/-- The sums, zero. -/
def dotZero : List Instr := [xb .pxor .xmm5 .xmm5, xb .pxor .xmm6 .xmm6]

/-- The products of the doublewords of `xmm0` and `xmm1` added to the
quadwords of `xmm5` (even doublewords) and `xmm6` (odd ones). -/
def dotMac : List Instr :=
  [xmov .xmm2 .xmm0, .xop (.shift .psrlq .xmm2 32), xmov .xmm3 .xmm1, .xop (.shift .psrlq .xmm3 32),
    xb .pmuludq .xmm2 .xmm3, xb .pmuludq .xmm0 .xmm1, xb .paddq .xmm5 .xmm0, xb .paddq .xmm6 .xmm2]

/-- The sums, reduced: `(P + m q) / 2³²` of each quadword, merged into the
doublewords of `xmm5`, then reduced to `[0, q)`. -/
def dotRed : List Instr :=
  vredc .xmm5 .xmm2 ++ [.xop (.shift .psrlq .xmm5 32)] ++ vredc .xmm6 .xmm2 ++ [xb .por .xmm5 .xmm6] ++
    vcsub .xmm5 .xmm2

/-- The sum times `2⁻³²`, times `2⁶⁴ mod q` (in `xmm11`) times `2⁻³²`: the sum
modulo `q`. -/
def dotPlain : List Instr := vmont .xmm5 .xmm11 .xmm11 .xmm2 .xmm4 ++ vcsub .xmm5 .xmm2

/-- The coefficients of `a[j]` and `b[j]`. -/
def dotLoadsS (j : Nat) : List Instr := [.movdquLoad .xmm0 (at_ .r10 (1024 * j)), .movdquLoad .xmm1 (at_ .rdx (1024 * j))]

/-- Four coefficients of the sum of the `c` products. -/
def dotBodyS (c : Nat) : List Instr :=
  dotZero ++ (List.range c).flatMap (fun j => dotLoadsS j ++ dotMac) ++ dotRed ++ dotPlain ++
    [.movdquStore (at_ .r8 0) .xmm5, .alu .add .r8 (.imm 16), .alu .add .r10 (.imm 16), .alu .add .rdx (.imm 16)]

/-- `vg_mldsa_dot_inverse{c}`: the sum of the `c` products, then `NTT⁻¹`, in
one MXCSR region. -/
def dotInvSse2 (c : Nat) : Prog isa :=
  .seq (.block [.mov .r10 (.reg .rsi), .mov .rsi (.reg .rcx)]) <| withMxcsr .rsi 768 <|
    .seq (.block (mulPro ++ [.mov .r8 (.reg .rdi)])) (.seq (rcxLoop 64 (dotBodyS c)) nttInvBody)

end VG.Impl.MlDsa.X86_64.Arith
