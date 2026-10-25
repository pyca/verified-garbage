module

public import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Reflect
import VerifiedGarbage.Proof.Framework.Bitslice.Anf

@[expose] public section
namespace VG.Proof.Sha3.AArch64.Scalar
open VG VG.AArch64 VG.Impl.Sha3.AArch64.Scalar

/-- Push rotations to leaves. Deferred rotations can then be checked without
expanding an entire 24-round permutation into one expression tree. -/
def Expr.rotateNormal : Expr → Nat → Expr
  | .reg r, n => .ror (.reg r) (n % 64)
  | .slot k, n => .ror (.slot k) (n % 64)
  | .xor a b, n => .xor (a.rotateNormal n) (b.rotateNormal n)
  | .bic a b, n => .bic (a.rotateNormal n) (b.rotateNormal n)
  | .ror a k, n => a.rotateNormal ((k + n) % 64)

theorem rotateRight_not (x : Lane) (n : Nat) :
    (~~~x).rotateRight n = ~~~(x.rotateRight n) := by
  ext i hi
  simp only [BitVec.getElem_rotateRight, BitVec.getElem_not]
  split <;> rfl

theorem Expr.rotateNormal_eval (e : Expr) (f : File) (n : Nat) :
    (e.rotateNormal n).eval f = (e.eval f).rotateRight n := by
  induction e generalizing n with
  | reg r => exact BitVec.rotateRight_mod_eq_rotateRight
  | slot k => exact BitVec.rotateRight_mod_eq_rotateRight
  | xor a b ha hb =>
    simp only [rotateNormal, Expr.eval, ha, hb, VG.Bitslice.Anf.rotateRight_xor]
  | bic a b ha hb =>
    simp only [rotateNormal, Expr.eval, ha, hb, VG.Bitslice.Anf.rotateRight_and,
      rotateRight_not]
  | ror a k ha =>
    simp only [rotateNormal, Expr.eval, ha, VG.Bitslice.Anf.rotateRight_rotateRight]

end VG.Proof.Sha3.AArch64.Scalar
