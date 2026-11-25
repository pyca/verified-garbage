module

public import VerifiedGarbage.Impl.Mont.AArch64.P521
public import VerifiedGarbage.Impl.Weierstrass.AArch64.Mont

/-!
# P-521's field products as functions on AArch64

`vg_p521_prod_mod_p(ws, o, a, b)` and `vg_p521_sqr_mod_p(ws, o, a)`:
`[o] = [a] [b] R⁻¹` and `[a]^2 R⁻¹` modulo `p`, for operands below `p`, with
the entry and the exit of `vg_p521_mul_mod_p` (`Mont.lean`), which takes any
`[a]`: the offsets zero-extended, the callee-saved registers the function
writes saved in vector lanes, the pointers in `x28` (`[a]`), `x27` (`[b]`,
from `x3`, which the product uses) and `x30` (`[o]`).
-/

@[expose] public section

namespace VG.Impl.Weierstrass.AArch64.P521

open VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass.AArch64

/-- The product's body, from its pointers. -/
def prodBody : List Instr := .addImm .x .x27 .x3 0 :: Impl.Mont.AArch64.P521.mulR .x28 .x27 .x30 0 0 0

/-- The square's body, from its pointers. -/
def sqrBody : List Instr := Impl.Mont.AArch64.P521.sqrR .x28 .x30 0 0

/-- A function around a body. -/
def fn (body : List Instr) : Prog isa :=
  .seq (.block Mont.zextCode)
    (.block (Mont.saveCode 9 ++ ([.add .x .x30 .x0 .x1, .add .x .x28 .x0 .x2, .add .x .x3 .x0 .x3] : List Instr) ++ body ++
      Mont.restoreCode 9))

/-- `vg_p521_prod_mod_p`. -/
def prodFn : Prog isa := fn prodBody

/-- `vg_p521_sqr_mod_p`. -/
def sqrFn : Prog isa := fn sqrBody

/-- The modulus `m` of `n` words is P-521's `p`. -/
def isField (n m : Nat) : Bool := n == 9 && m == Impl.Mont.AArch64.P521.prime

/-- The modulus is P-521's `p`. -/
def supported (M : Mod) : Bool := M.n == 9 && decide (M.red = Red.ofModulus 9 Impl.Mont.AArch64.P521.prime)

end VG.Impl.Weierstrass.AArch64.P521
