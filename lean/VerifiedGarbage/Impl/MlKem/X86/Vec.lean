module

public import VerifiedGarbage.Impl.MlKem.X86.Basic

/-!
# ML-KEM on x86 (32-bit): arithmetic modulo `q` in the words of XMM registers

The pieces of `vg_mlkem_ntt`, `vg_mlkem_inv_ntt` and
`vg_mlkem_multiply_ntts` (`Impl/MlKem/X86/Ntt.lean`), as x86-64's
`Impl/MlKem/X86_64/Vec.lean` has them: eight coefficients at a time, in the
16-bit words of an XMM register, with `q` in the words of `xmm7` and
`q⁻¹ mod 2¹⁶` in those of `xmm6`.

* `wmont d z t`: the signed Montgomery product `d · z · 2⁻¹⁶ mod q` of each
  word of `d` and `z`, in `(-q, q)`: the high word of `d · z`, less the high
  word of `q` times the low word of `d · z · q⁻¹` (`pmullw`, `pmulhw`).
* `wcadd d t` adds `q` to the negative words of `d`, and `wcsub d t`
  subtracts `q` from the words that are at least `q`.

`pmullw` and `pmulhw` are on Intel's MCDT list, so the functions run them
inside an MCDT frame (`wframe`); an allocation of four bytes inside it makes
their stack use the 16 bytes of the scalar functions they replace.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86

open VG.X86

/-- `++`, grouping to the right. -/
local infixr:65 " +++ " => HAppend.hAppend

/-- `op d, r` -/
def wb (op : XBinOp) (d r : XReg) : Instr := .xop (.bin op d r)

/-- `d ← r` -/
def wmov (d r : XReg) : Instr := wb .movdqa d r

/-- `v` in every doubleword of `d`, through `eax`. -/
def wconst (d : XReg) (v : BitVec 32) : List Instr :=
  [.mov .eax (.imm v), .xop (.movd d .eax), .xop (.pshufd d d 0)]

/-- `d ← d · z · 2⁻¹⁶ mod q` in each word, in `(-q, q)`, with a temporary `t`. -/
def wmont (d z t : XReg) : List Instr :=
  [wmov t d, .pmullw t z, .pmullw t .xmm6, .pmulhw d z, .pmulhw t .xmm7, wb .psubw d t]

/-- `d ← d + q` for the negative words of `d`, with a temporary `t`. -/
def wcadd (d t : XReg) : List Instr :=
  [wmov t d, .xop (.shift .psraw t 15), wb .pand t .xmm7, wb .paddw d t]

/-- `d ← d mod q` for words in `[0, 2q)`, with a temporary `t`. -/
def wcsub (d t : XReg) : List Instr := wb .psubw d .xmm7 :: wcadd d t

/-- A function that is `body` in an MCDT frame, with 16 bytes of stack:
its arguments are at `[esp + 20]`, `[esp + 24]`, … in `body`. -/
def wframe (body : Prog isa) : Prog isa :=
  .frame (.mcdtEnter .eax) (.frame (.alloc 4) body (.free 4)) .mcdtLeave

end VG.Impl.MlKem.X86
