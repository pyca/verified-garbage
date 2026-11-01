module

public import VerifiedGarbage.Impl.Bignum.AArch64.ProductDispatch

/-! Share repeated Montgomery products by fixed-index helpers
(`vg_rsa_mul_{o}_{a}_{b}`, `Proof.Rsa.MontMulFixed`), as `SquareCall` shares
the in-place squares. Each helper is the eight-limb product
(`ProductDispatch.mm`), whose fallback for other widths is inline, so it
cannot overwrite the saved link. -/

@[expose] public section
namespace VG.Impl.Bignum.AArch64.MulFixedCall
open VG VG.AArch64

/-- The products with a shared helper: those DSA repeats. -/
def shared : List (Nat × Nat × Nat) :=
  [(5, 1, 4), (6, 5, 6), (6, 4, 7), (5, 5, 4), (6, 6, 5), (6, 6, 7), (1, 1, 4), (6, 5, 1),
    (5, 1, 7), (1, 1, 6), (4, 4, 7), (6, 4, 6)]

def mm (o a b : Nat) : Prog isa :=
  if (o, a, b) ∈ shared then
    SquareCall.call s!"vg_rsa_mul_{o}_{a}_{b}" (ProductDispatch.mm o a b)
  else ProductDispatch.mm o a b

end VG.Impl.Bignum.AArch64.MulFixedCall
