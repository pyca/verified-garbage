module

public import VerifiedGarbage.Impl.MlKem.X86.Basic

/-!
# ML-DSA on x86 (32-bit): arithmetic modulo `q`, `vg_mldsa_add` and `vg_mldsa_sub`

Coefficients are `u32`s less than `q = 8380417 < 2²³`. `csubQ r t` is
`r ← r mod q` for `r < 2q`, without a branch: `sub r, q` borrows exactly
when `r < q`, `sbb t, t` turns the borrow into a mask, and `q` masked with
it is added back.

The functions are leaves (`Impl.MlKem.X86.leaf`), which save the caller's
`ebx`, `esi`, `edi` and `ebp` in a frame of 16 bytes; their arguments are
then at `[esp + 20]`, `[esp + 24]`, ….

* `add(f, g)`: `f[i] ← (f[i] + g[i]) mod q`;
* `sub(f, g)`: `f[i] ← (f[i] + q - g[i]) mod q`.

Both are the loop `Impl.MlKem.X86.mapLoop` with `esi = f`, `edi = g` and
`ecx` the coefficients left, around the arithmetic `addOp` or `subOp` on
`eax = f[i]`, with `edx` as a temporary. Every address and branch depends
only on the pointers.
-/

@[expose] public section

namespace VG.Impl.MlDsa.X86.Arith

open VG.X86
open VG.Impl.MlKem.X86 (at_ leaf mapLoop)

/-- `++`, grouping to the right. The kernel evaluates the code (for the
constant-time analysis), and `(a ++ b) ++ c` has it copy `a` twice. -/
local infixr:65 " +++ " => HAppend.hAppend

/-- `q = 8380417`, as an immediate. -/
def qImm : BitVec 32 := 8380417

/-- `-q⁻¹ mod 2³²`. -/
def qInvImm : BitVec 32 := 4236238847

/-- `r ← r mod q` for `r < 2q`, with the temporary `t`. -/
def csubQ (r t : Reg) : List Instr :=
  [.alu .sub r (.imm qImm), .alu .sbb t (.reg t), .alu .and t (.imm qImm), .alu .add r (.reg t)]

/-! ## `add` and `sub` -/

/-- `eax ← (eax + g[i]) mod q`. -/
def addOp : List Instr := .alu .add .eax (.mem (at_ .edi 0)) :: csubQ .eax .edx

/-- `eax ← (eax + q - g[i]) mod q`. -/
def subOp : List Instr :=
  .alu .add .eax (.imm qImm) :: .alu .sub .eax (.mem (at_ .edi 0)) :: csubQ .eax .edx

def add : Prog isa := leaf (mapLoop addOp)

def sub : Prog isa := leaf (mapLoop subOp)

end VG.Impl.MlDsa.X86.Arith
