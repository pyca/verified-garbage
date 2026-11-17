module

public import VerifiedGarbage.Impl.MlDsa.Arm.Arith.Common

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_multiply_ntt` and `vg_mldsa_multiply_add_ntt`

`multiplyNTT(h = r0, f = r1, g = r2)` and `multiplyAddNTT(h = r0, f = r1,
g = r2)` save `r4`–`r9` (`saving`: 24 bytes of stack), put `-q` in `r4` and
`q` in `r5`, and run over the 256 coefficients with `r0`, `r1` and `r2`
pointing at coefficient `i` of `h`, `f` and `g`, and `r3 = 256 - i` counting
down: `g[i]` goes to `r6` and its `zp` to `r7` (`quot`), and `mulq`
multiplies `f[i]` (in `r8`) by it, into `r9`, less than `2³² - q`; `red`
and `csub` reduce it (for `multiplyAddNTT`, `h[i]` is added first). Every
address and branch depends only on the pointers.
-/

@[expose] public section

namespace VG.Impl.MlDsa.Arm.Arith

open VG.Arm

/-- The registers the multiplications save. -/
def mulSaved : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9]

/-- Advance the three pointers and count down. -/
def step3 : List Instr :=
  [.dp .add .r0 .r0 (.imm 4), .dp .add .r1 .r1 (.imm 4), .dp .add .r2 .r2 (.imm 4), .subs .r3 .r3 (.imm 1)]

/-- `f[i] · g[i]` less a multiple of `q`, less than `2³² - q`, in `r9`. -/
def mulHead : List Instr :=
  ([.ldr .r8 .r1 0, .ldr .r6 .r2 0] : List Instr) ++ quot .r7 .r6 ++ mulq .r9 .r8 .r6 .r7 .r12 .r4

/-- `r9` reduced, stored, and on to the next coefficient. -/
def mulTail : List Instr := red .r9 .r12 .r4 ++ csub .r9 .r12 .r5 ++ ([.str .r9 .r0 0] : List Instr) ++ step3

def mulBody : List Instr := mulHead ++ mulTail

def mulAddBody : List Instr := mulHead ++ ([.ldr .r8 .r0 0, .dp .add .r9 .r9 (.reg .r8)] : List Instr) ++ mulTail

/-- `-q` in `r4`, `q` in `r5`, and the count in `r3`. -/
def mulPre : List Instr := loadNQ .r4 ++ loadQ .r5 ++ ([.mov .r3 (.imm 256)] : List Instr)

def mul : Prog isa := saving mulSaved (.seq (.block mulPre) (.loop (.block mulBody) .ne))

def mulAdd : Prog isa := saving mulSaved (.seq (.block mulPre) (.loop (.block mulAddBody) .ne))

end VG.Impl.MlDsa.Arm.Arith
