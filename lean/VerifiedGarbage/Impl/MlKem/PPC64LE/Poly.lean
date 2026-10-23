module

public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# ML-KEM: the coefficient-wise primitives on PPC64LE

The coefficients are `u32`s in memory, loaded with `lwz` (zero-extended) and
stored with `stw` (the low word); the arithmetic is on all 64 bits, where a
coefficient and the sum or product of two never wraps around.

A value `u` in `(-q, q)` (as a 64-bit two's complement number) is reduced
into `[0, q)` without a branch by `fixup`: `c = u >> 63` (1 if `u` is
negative), then `u + c·q`, with `q` kept in a register. A sum `a + b` of
reduced values is reduced as `fixup (a + b - q)`, a difference as
`fixup (a - b)`.

* `vg_mlkem_add(f = r3, g = r4)`, `vg_mlkem_sub(f = r3, g = r4)`: a loop
  over the 256 coefficients, `r5` counting, with `q` in `r8`.

Every address is a pointer plus a constant, and every branch depends on a
counter: only the pointers can affect timing.
-/

@[expose] public section

namespace VG.Impl.MlKem.PPC64LE

open VG.PPC64LE

/-- `r := r + q` if `r` is negative, with `q` in `rq` and `t` a temporary. -/
def fixup (r t rq : Reg) : List Instr := [.lsr .d t r 63, .mul t t rq, .add r r t]

/-! ## Addition and subtraction -/

/-- The end of an iteration over coefficients: store, `f` and `g` advance,
`r5` counts down. -/
def accTail : List Instr :=
  [.store .w .r6 .r3 0, .addi .r3 .r3 4, .addi .r4 .r4 4, .subi .r5 .r5 1]

def addBody : List Instr :=
  [.load .w .r6 .r3 0, .load .w .r7 .r4 0, .add .r6 .r6 .r7, .sub .r6 .r6 .r8] ++
    fixup .r6 .r7 .r8 ++ accTail

def subBody : List Instr :=
  [.load .w .r6 .r3 0, .load .w .r7 .r4 0, .sub .r6 .r6 .r7] ++ fixup .r6 .r7 .r8 ++ accTail

def add : Prog isa := .seq (.block [.li .r5 256, .li .r8 3329]) (.loop (.block addBody) (.nonzero .d .r5))

def sub : Prog isa := .seq (.block [.li .r5 256, .li .r8 3329]) (.loop (.block subBody) (.nonzero .d .r5))

end VG.Impl.MlKem.PPC64LE
