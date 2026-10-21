module

public import VerifiedGarbage.Impl.P384.Ops
public import VerifiedGarbage.Impl.Weierstrass.AArch64.TCombJ

/-!
# P-384's comb arithmetic on AArch64

`program`: a field program as one straight line of `Ops.op` (the cores of
`vg_p384_mul_mod_p` and `vg_p384_sqr_mod_p` inline, and the sums and
differences), in place of the calls `fprogB` makes, for the comb's mixed
addition: one block, which the pipelined comb weaves with the next entry's
selection (`TCombCfg.combJP2`, `comb`).
-/

@[expose] public section

namespace VG.Impl.P384.CombArithmetic
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass

/-- A field program in a straight line of `Ops.op`, for P-384's modulus. -/
def program (_ : Mod) (ops : List FOp) : Prog isa := .block (ops.flatMap Ops.op)

/-- The comb's mixed addition, in a straight line. -/
def mixed : List Instr :=
  let K := Impl.Ecdsa.AArch64.p384.combCfg
  (maddJ K.S K.A K.E K.D).flatMap Ops.op

/-- The comb of P-384's signatures and public keys: by Jacobian mixed
additions, each woven with the next window's selection in two passes. -/
def comb : Prog isa := Impl.Ecdsa.AArch64.p384.combCfg.combJP2 program mixed

end VG.Impl.P384.CombArithmetic
