module

public import VerifiedGarbage.Impl.MlDsa.X86.Arith.Basic

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_multiply_ntt` and `vg_mldsa_multiply_add_ntt`

`multiplyNTT(h, f, g)` and `multiplyAddNTT(h, f, g)` compute on four
coefficients at a time, as the doublewords of XMM registers, with `eax`,
`ecx` and `edx` pointing at coefficient `4i` of `h`, `f` and `g`, and
`h + 1024` in the argument slot of `h`, which the loop compares `eax` with.
They use no other general register, so they save none, and their only
stack is the MCDT frame's 12 bytes: `pmuludq` runs inside it
(`TCB/X86/Isa.lean`), and the arguments are at `[esp + 16]`, `[esp + 20]`
and `[esp + 24]` there.

The arithmetic, with `q` in the doublewords of `xmm7`, `-q⁻¹ mod 2³²` in
those of `xmm6`, `0xFFFFFFFF` in those of `xmm4` and `2³² - q` in those of
`xmm3` (`vconst`, through `eax`), and only instructions of the model (it
has neither `psubd` nor `psrad`):

* `vredc d t`: the Montgomery reductions of the quadword products in `d`,
  each to `P + m · q`, a multiple of `2³²` (`pmuludq` by `xmm6`, then by
  `xmm7`, which use the low doubleword of the product);
* `vmont d z u t`: `d ← d · z · 2⁻³² mod q`, in `[0, 2q)`, each doubleword
  of `d` by the even doubleword of `z` in its quadword: `pmuludq`
  multiplies the even doublewords, and the odd ones of `d` are moved down
  into `u` (`psrlq`); the quotients of the even products are moved down,
  and those of the odd ones are in place, over low doublewords that are 0,
  so `por` merges them. `vmont2 d b u` multiplies doubleword by doubleword,
  with the odd ones of `b` moved down too (`b` is then the temporary);
* `vcsub d t`: `d ← d mod q` for doublewords less than `2q`:
  `y = d + (2³² - q)` has its sign bit set exactly when `d < q`, so
  `(y >> 31) + 0xFFFFFFFF` is 0 then and `0xFFFFFFFF` otherwise, and `pandn`
  of it with `q` is the `q` to add back.

The product `f[i] · g[i]` is reduced twice by Montgomery, as the code this
replaces did: `vmont2` leaves `f[i] · g[i] · 2⁻³²`, less than `2q`, and
`vmont` of that by `2⁶⁴ mod q` (in `xmm5`) leaves `f[i] · g[i]`, less than
`2q`, which `vcsub` reduces. For `multiplyAddNTT`, `h[i]` is added and the
sum reduced. Every address and branch depends only on the pointers.
-/

@[expose] public section

namespace VG.Impl.MlDsa.X86.Arith

open VG.X86
open VG.Impl.MlKem.X86 (at_)

/-- `++`, grouping to the right. -/
local infixr:65 " +++ " => HAppend.hAppend

/-- `2⁶⁴ mod q`. -/
def r2Imm : BitVec 32 := 2365951

/-- `op d, r` -/
def xb (op : XBinOp) (d r : XReg) : Instr := .xop (.bin op d r)

/-- `d ← r` -/
def xmov (d r : XReg) : Instr := xb .movdqa d r

/-- `v` in every doubleword of `d`, through `eax`. -/
def vconst (d : XReg) (v : BitVec 32) : List Instr :=
  [.mov .eax (.imm v), .xop (.movd d .eax), .xop (.pshufd d d 0)]

/-- The Montgomery reductions of the quadword products in `d`, with a
temporary `t`: each quadword becomes `P + m · q`. -/
def vredc (d t : XReg) : List Instr :=
  [xmov t d, .pmuludq t .xmm6, .pmuludq t .xmm7, xb .paddq d t]

/-- The quotients of the reduced products `d` (of the even doublewords) and
`u` (of the odd ones), merged in `d`, with a temporary `t`. -/
def vjoin (d u t : XReg) : List Instr :=
  vredc d t +++ ([.xop (.shift .psrlq d 32)] : List Instr) +++ vredc u t +++ ([xb .por d u] : List Instr)

/-- `d ← d · z · 2⁻³² mod q`, in `[0, 2q)`, each doubleword of `d` by the
even doubleword of `z` in its quadword, with temporaries `u` and `t`. -/
def vmont (d z u t : XReg) : List Instr :=
  ([xmov u d, .xop (.shift .psrlq u 32), .pmuludq d z, .pmuludq u z] : List Instr) +++ vjoin d u t

/-- `d ← d · b · 2⁻³² mod q`, in `[0, 2q)`, doubleword by doubleword, with a
temporary `u`; `b` is clobbered. -/
def vmont2 (d b u : XReg) : List Instr :=
  ([xmov u d, .xop (.shift .psrlq u 32), .pmuludq d b, .xop (.shift .psrlq b 32), .pmuludq u b] : List Instr) +++
    vjoin d u b

/-- `d ← d mod q` for doublewords less than `2q`, with a temporary `t`. -/
def vcsub (d t : XReg) : List Instr :=
  [xb .paddd d .xmm3, xmov t d, .xop (.shift .psrld t 31), xb .paddd t .xmm4, xb .pandn t .xmm7,
    xb .paddd d t]

/-- `f · g` for the four coefficients in `xmm0` and `xmm1`, in `[0, q)`, in `xmm0`. -/
def mulCore : List Instr :=
  vmont2 .xmm0 .xmm1 .xmm2 +++ vmont .xmm0 .xmm5 .xmm2 .xmm1 +++ vcsub .xmm0 .xmm1

/-- `h + f · g` for four coefficients, in `[0, q)`, in `xmm0`. -/
def mulAddCore : List Instr :=
  mulCore +++ ([.movdquLoad .xmm1 (at_ .eax 0), xb .paddd .xmm0 .xmm1] : List Instr) +++ vcsub .xmm0 .xmm1

/-- The constants; `eax = h`, `ecx = f`, `edx = g`, and `h + 1024` in the
slot of `h`. -/
def mulInit : List Instr :=
  vconst .xmm7 qImm +++ vconst .xmm6 qInvImm +++ vconst .xmm5 r2Imm +++ vconst .xmm4 0xFFFFFFFF +++
  vconst .xmm3 4286586879 +++
  ([.mov .eax (.mem (at_ .esp 16)), .mov .ecx (.reg .eax), .alu .add .ecx (.imm 1024),
    .store (at_ .esp 16) .ecx, .mov .ecx (.mem (at_ .esp 20)), .mov .edx (.mem (at_ .esp 24))] : List Instr)

/-- Four coefficients: `core` of those of `f` and `g`, stored to `h`, and on
to the next four. -/
def mulStep (core : List Instr) : List Instr :=
  ([.movdquLoad .xmm0 (at_ .ecx 0), .movdquLoad .xmm1 (at_ .edx 0)] : List Instr) +++ core +++
  ([.movdquStore (at_ .eax 0) .xmm0, .alu .add .eax (.imm 16), .alu .add .ecx (.imm 16),
    .alu .add .edx (.imm 16), .alu .cmp .eax (.mem (at_ .esp 16))] : List Instr)

/-- A function of `h`, `f` and `g`, four coefficients at a time by `core`. -/
def mulFn (core : List Instr) : Prog isa :=
  .frame (.mcdtEnter .eax) (.seq (.block mulInit) (.loop (.block (mulStep core)) .ne)) .mcdtLeave

def mul : Prog isa := mulFn mulCore

def mulAdd : Prog isa := mulFn mulAddCore

end VG.Impl.MlDsa.X86.Arith
