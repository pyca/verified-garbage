module

public import VerifiedGarbage.Impl.Weierstrass.X86.PowChain

/-! # Fixed prefixes for P-256's and P-521's scalar-order inversions -/

@[expose] public section

namespace VG.Impl.Weierstrass.X86
open VG.X86 VG.Impl.Mont.X86 VG.Impl.Weierstrass

def p256Order : Nat := 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551

/-- The top 128 bits of `n-2`: 32 ones, 32 zeros, then 64 ones.
Build the first run by an addition chain and reuse it twice. -/
def p256ScalarPrefixOps : List PowerOp :=
  [.save, .squares 1, .mulSaved,
   .save, .squares 2, .mulSaved,
   .save, .squares 4, .mulSaved,
   .save, .squares 8, .mulSaved,
   .save, .squares 16, .mulSaved, .save,
   .squares 64, .mulSaved, .squares 32, .mulSaved]

/-- Use the prefix chain, then the existing loop for the lower 128 bits.
The prefix takes 127 squarings and 7 other products; the suffix takes
256 multiplications, for 390 total instead of 512. -/
def p256ScalarPower (P : PowCfg) (F : Impl.Weierstrass.Mont.Modulus) : Prog isa :=
  .seq (.block (copy (2 * P.M.n) P.acc P.base ++ copy (2 * P.M.n) P.tmp P.base)) <|
  .seq (powerChain P F p256ScalarPrefixOps) <|
  .seq (.block [.mov .esi (.imm 128)]) (.loop (powBody P F) .ne)

/-- The chain `ops` from the base for the exponent's bits from `low`, then
the existing loop for its `low` lower bits. -/
def prefixPower (P : PowCfg) (F : Impl.Weierstrass.Mont.Modulus) (ops : List PowerOp) (low : Nat) :
    Prog isa :=
  .seq (.block (copy (2 * P.M.n) P.acc P.base ++ copy (2 * P.M.n) P.tmp P.base)) <|
  .seq (powerChain P F ops) <|
  .seq (.block [.mov .esi (.imm (BitVec.ofNat 32 low))]) (.loop (powBody P F) .ne)

/-- The top 262 bits of P-521's `n - 2`, all ones: `x^(2^k - 1)` for `k` =
2, 4, …, 64, 65, 130, 131 and 262, each from the one before it (by `k`
squarings and the saved `x^(2^k - 1)`, or a squaring and the base). This
uses 261 squares and 10 other multiplications; the loop for the other 259
bits takes 518 products, for 789 in all instead of 1152. -/
def p521ScalarPrefixOps : List PowerOp :=
  [.squares 1, .mulSaved, .save, .squares 2, .mulSaved, .save, .squares 4, .mulSaved,
   .save, .squares 8, .mulSaved, .save, .squares 16, .mulSaved, .save, .squares 32, .mulSaved,
   .squares 1, .mulBase, .save, .squares 65, .mulSaved, .squares 1, .mulBase,
   .save, .squares 131, .mulSaved]

def powScalar (P : PowCfg) (F : Impl.Weierstrass.Mont.Modulus) (m : Nat) : Prog isa :=
  if m = p256Order ∧ 128 ≤ P.nbits then p256ScalarPower P F
  else if m = Spec.P521.n ∧ 259 ≤ P.nbits then prefixPower P F p521ScalarPrefixOps 259
  else pow P F

end VG.Impl.Weierstrass.X86
