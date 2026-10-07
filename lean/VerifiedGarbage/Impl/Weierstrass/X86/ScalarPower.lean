import VerifiedGarbage.Impl.Weierstrass.X86.PowChain

/-! # A fixed prefix for P-256 scalar-order inversion -/
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
def p256ScalarPower (P : PowCfg) (wk : Nat) : Prog isa :=
  .seq (.block (copy (2 * P.M.n) P.acc P.base ++ copy (2 * P.M.n) P.tmp P.base)) <|
  .seq (powerChain P wk p256ScalarPrefixOps) <|
  .seq (.block [.mov .esi (.imm 128)]) (.loop (powBody P wk) .ne)

def powScalar (P : PowCfg) (wk m : Nat) : Prog isa :=
  if m = p256Order ∧ 128 ≤ P.nbits then p256ScalarPower P wk else pow P wk

end VG.Impl.Weierstrass.X86
