module

public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# ML-KEM: the coefficient-wise primitives on RISC-V

As on PPC64LE (`Impl/MlKem/PPC64LE/Poly.lean`): the coefficients are `u32`s
in memory, loaded with `lwu` (zero-extended) and stored with `sw` (the low
word); the arithmetic is on all 64 bits, where a coefficient and the sum or
product of two never wraps around.

A value `u` in `(-q, q)` (as a 64-bit two's complement number) is reduced
into `[0, q)` without a branch by `fixup`: `c = u >> 63` arithmetically
(all ones if `u` is negative), then `u + (c & q)`, with `q` kept in a
register. A sum `a + b` of reduced values is reduced as `fixup (a + b - q)`,
a difference as `fixup (a - b)`. `q` does not fit an immediate: it is
`lui 1` and `addi -767` (`liq`).

* `vg_mlkem_add(f = a0, g = a1)`, `vg_mlkem_sub(f = a0, g = a1)`: a loop
  over the 256 coefficients, `a2` counting, with `q` in `a5`.

Every address is a pointer plus a constant, and every branch depends on a
counter: only the pointers can affect timing.
-/

@[expose] public section

namespace VG.Impl.MlKem.RISCV64

open VG.RISCV64

/-- `r := v` for `v < 4096`: one `li` below 2048, else `lui 1` and an
`addi` of `v - 4096`. -/
def liq (r : Reg) (v : Nat) : List Instr :=
  if v < 2048 then [.li r v] else [.lui r 1, .addi r r ((v : Int) - 4096)]

/-- `r := r + q` if `r` is negative, with `q` in `rq` and `t` a temporary. -/
def fixup (r t rq : Reg) : List Instr := [.shift .sra .d t r 63, .logic .and t t rq, .add r r t]

/-! ## Addition and subtraction -/

/-- The end of an iteration over coefficients: store, `f` and `g` advance,
`a2` counts down. -/
def accTail : List Instr :=
  [.store .w .a3 .a0 0, .addi .a0 .a0 4, .addi .a1 .a1 4, .addi .a2 .a2 (-1)]

def addBody : List Instr :=
  [.load .w .a3 .a0 0, .load .w .a4 .a1 0, .add .a3 .a3 .a4, .sub .a3 .a3 .a5] ++
    fixup .a3 .a4 .a5 ++ accTail

def subBody : List Instr :=
  [.load .w .a3 .a0 0, .load .w .a4 .a1 0, .sub .a3 .a3 .a4] ++ fixup .a3 .a4 .a5 ++ accTail

/-- The counter, and `q` in `a5`. -/
def polyInit : List Instr := [.li .a2 256] ++ liq .a5 3329

def add : Prog isa := .seq (.block polyInit) (.loop (.block addBody) (.nonzero .a2))

def sub : Prog isa := .seq (.block polyInit) (.loop (.block subBody) (.nonzero .a2))

end VG.Impl.MlKem.RISCV64
